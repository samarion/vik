package io.bovel.vik

import scala.collection.immutable.ArraySeq
import scala.collection.mutable.{ArrayBuffer, HashMap}

import io.bovel.egraph.{App, EClassId, EGraph, Rules}

/** Algebraic datatypes as rules of the e-graph (Barrett, Shikanian and Tinelli
 *  2007). The encoder registers the classes of the constructor, selector and
 *  tester symbols and of `true`; the rules then keep, per class, the
 *  constructor node it holds, and:
 *    - injectivity: two constructor nodes of one constructor in one class
 *      equate their arguments; distinctness: nodes of different constructors in
 *      one class are a contradiction;
 *    - selectors: `s_i(t)` is the `i`-th argument of the constructor node of
 *      `t`'s class, once there is one;
 *    - testers: `(_ is C)(t)` holds when `t`'s class has a `C` node and cannot
 *      hold when it has another; a tester that holds expands `t` into
 *      `C(s_1(t), ..., s_n(t))`, so that every term with a known constructor
 *      has a constructor node (the encoder asserts that some tester of every
 *      datatype term holds);
 *    - acyclicity, at the final check: no class reaches itself through the
 *      arguments of constructor nodes.
 *  Every derived equality carries its premises; the state has levels.
 */
final class AdtRules extends Rules:
  /** A constructor node: the constructor's class, the argument classes (as
   *  added) and the node's own class.
   */
  final case class Node(fun: EClassId, args: ArraySeq[EClassId], cls: EClassId)

  /** A constructor symbol: its selectors' classes, in order. */
  private val constructors = HashMap.empty[EClassId, ArraySeq[EClassId]]

  /** A selector symbol: its constructor's class and its index. */
  private val selectors = HashMap.empty[EClassId, (EClassId, Int)]

  /** A tester symbol: its constructor's class. */
  private val testers = HashMap.empty[EClassId, EClassId]

  private var trueClass: EClassId = -1

  /** The constructor node of a class, by the representative at the time it was
   *  set (see `nodeOf`); `trail` records replaced entries for `pop`.
   */
  private val nodes = HashMap.empty[EClassId, Node]
  private val trail = ArrayBuffer.empty[(EClassId, Node | Null)]
  private val marks = ArrayBuffer.empty[Int]

  def register(constructor: EClassId, selectorClasses: List[EClassId], tester: EClassId): Unit =
    constructors(constructor) = ArraySeq.from(selectorClasses)
    for (selector, i) <- selectorClasses.zipWithIndex do selectors(selector) = (constructor, i)
    testers(tester) = constructor

  /** A nullary constructor is a class of its own, not an application. */
  def constant(constructor: EClassId): Unit = set(constructor, Node(constructor, ArraySeq.empty, constructor))

  def truth(cls: EClassId): Unit = trueClass = cls

  private def nodeOf(eg: EGraph, cls: EClassId): Node | Null = nodes.getOrElse(eg.find(cls), null)

  /** The constructor node of a class, for the models. */
  def node(eg: EGraph, cls: EClassId): Node | Null = nodeOf(eg, cls)

  private def set(rep: EClassId, node: Node): Unit =
    if marks.nonEmpty then trail += ((rep, nodes.getOrElse(rep, null)))
    nodes(rep) = node

  override def added(eg: EGraph, app: App, cls: EClassId): Unit =
    val fun = eg.find(app.fun)
    if constructors.contains(fun) then
      val node = Node(fun, app.args, cls)
      val rep = eg.find(cls)
      val existing = nodeOf(eg, rep)
      if existing == null then set(rep, node) else meet(eg, node, existing)
    else
      selectors.get(fun).foreach { (constructor, i) =>
        val t = app.args(0)
        val node = nodeOf(eg, t)
        if node != null && node.fun == constructor then eg.derive(cls, node.args(i), List((t, node.cls)))
      }
      testers.get(fun).foreach { constructor =>
        val t = app.args(0)
        val node = nodeOf(eg, t)
        if node != null && node.fun == constructor then eg.derive(cls, trueClass, List((t, node.cls)))
      }

  /** Two constructor nodes in one class: injectivity or a contradiction. */
  private def meet(eg: EGraph, a: Node, b: Node): Unit =
    if a.fun == b.fun then for i <- a.args.indices do eg.derive(a.args(i), b.args(i), List((a.cls, b.cls)))
    else eg.contradiction(List((a.cls, b.cls)))

  override def merged(
      eg: EGraph,
      from: EClassId,
      into: EClassId,
      members: Iterable[EClassId],
      parents: Iterable[(App, EClassId)]
  ): Unit =
    val cf = nodes.getOrElse(from, null)
    val ci = nodes.getOrElse(into, null)
    if cf != null && ci != null then meet(eg, cf, ci)
    else if cf != null then
      set(into, cf)
      selectorsAndTesters(eg, into, cf, eg.parents(into).toList) // materialized: derived merges append to the list
    else if ci != null then selectorsAndTesters(eg, into, ci, parents)
    // Testers that just became true: the true class absorbed them, or was absorbed with them.
    if trueClass >= 0 && eg.find(trueClass) == into then
      // The absorbed side's members became true, or, if the true class was the absorbed one, the whole class did.
      val scope = if members.exists(_ == trueClass) then eg.nodes(into).map(_._2).toList else members // materialized
      for m <- scope do
        val app = eg.app(m)
        if app != null then testers.get(eg.find(app.fun)).foreach(constructor => holds(eg, app, m, constructor))

  /** The selectors and testers among `parents` applied to the class of `rep`,
   *  now that it holds the constructor node `node`.
   */
  private def selectorsAndTesters(eg: EGraph, rep: EClassId, node: Node, parents: IterableOnce[(App, EClassId)]): Unit =
    for (app, cls) <- parents.iterator.toList do // materialized: derived merges append to parent lists
      val fun = eg.find(app.fun)
      if eg.find(app.args(0)) == eg.find(rep) then
        selectors.get(fun).foreach { (constructor, i) =>
          if constructor == node.fun then eg.derive(cls, node.args(i), List((app.args(0), node.cls)))
        }
        testers.get(fun).foreach { constructor =>
          if constructor == node.fun then eg.derive(cls, trueClass, List((app.args(0), node.cls)))
          else if eg.find(cls) == eg.find(trueClass) then
            eg.contradiction(List((cls, trueClass), (app.args(0), node.cls)))
        }

  /** The tester `app` (in class `cls`) of `constructor` holds: `t` has that
   *  constructor node, or gets one by expansion, or has another one, a
   *  contradiction.
   */
  private def holds(eg: EGraph, app: App, cls: EClassId, constructor: EClassId): Unit =
    val t = app.args(0)
    val node = nodeOf(eg, t)
    if node == null then
      val premises = List((cls, trueClass))
      val selectorClasses = constructors(constructor)
      if selectorClasses.isEmpty then eg.derive(t, constructor, premises)
      else
        val fields = selectorClasses.map(s => eg.add(App(s, ArraySeq(t))))
        eg.derive(t, eg.add(App(constructor, fields)), premises)
    else if node.fun != constructor then eg.contradiction(List((cls, trueClass), (t, node.cls)))

  /** Acyclicity: a depth-first search over the classes with a constructor node,
   *  following the arguments; a class on the current path reached again is a
   *  cycle, explained by the equalities along it: each node's argument is the
   *  next node.
   */
  override def finalCheck(eg: EGraph): Option[Seq[(EClassId, EClassId)]] =
    val state = HashMap.empty[EClassId, Int] // 1 on the path, 2 done
    val path = ArrayBuffer.empty[(EClassId, Node)]
    def visit(rep: EClassId): Option[Seq[(EClassId, EClassId)]] =
      val node = nodes.getOrElse(rep, null)
      if node == null then None
      else
        state(rep) = 1
        path += ((rep, node))
        var found: Option[Seq[(EClassId, EClassId)]] = None
        val args = node.args.iterator
        while found.isEmpty && args.hasNext do
          val arg = args.next()
          val r = eg.find(arg)
          state.getOrElse(r, 0) match
            case 1 =>
              val cycle = path.drop(path.indexWhere(_._1 == r))
              val holding = ArrayBuffer.empty[(EClassId, EClassId)]
              for ((c, n), i) <- cycle.zipWithIndex do
                val next = cycle((i + 1) % cycle.length)._2
                val argOfN = n.args.find(a => eg.find(a) == cycle((i + 1) % cycle.length)._1).get
                holding += ((argOfN, next.cls)) // its argument is the next node
              found = Some(holding.toList)
            case 0 => found = visit(r)
            case _ => ()
        path.remove(path.length - 1)
        state(rep) = 2
        found
    val reps = nodes.keys.filter(k => eg.find(k) == k).toList
    reps.iterator.map(visit).collectFirst { case Some(reasons) => reasons }

  override def push(): Unit = marks += trail.length

  override def pop(): Unit =
    val mark = marks.remove(marks.length - 1)
    while trail.length > mark do
      val (rep, old) = trail.remove(trail.length - 1)
      if old == null then nodes.remove(rep) else nodes(rep) = old
