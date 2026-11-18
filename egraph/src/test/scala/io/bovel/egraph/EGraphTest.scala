package io.bovel.egraph

import scala.collection.immutable.ArraySeq
import scala.collection.mutable.{ArrayBuffer, HashMap}

class EGraphTest extends munit.FunSuite:

  /** [[EGraphBuilder]] plus test conveniences: reasonless `merge`/`disequate`
   *  (reason 0) and sorted explanations.
   */
  class TestGraph extends EGraphBuilder:
    def merge(a: EClassId, b: EClassId): Unit = eg.merge(a, b, 0)
    def disequate(a: EClassId, b: EClassId): Unit = eg.disequate(a, b, 0)
    def explain(a: EClassId, b: EClassId): Seq[Int] = eg.explain(a, b).toSeq.sorted

  test("adding the same application twice gives one class"):
    val t = TestGraph()
    val a = t.sym("a")
    val fa = t.node("f", a)
    val fa2 = t.node("f", a)
    assertEquals(t.find(fa), t.find(fa2))
    assertEquals(t.eg.classes(t.find(fa)).length, 1) // listed once

  test("add returns different ids for different nodes"):
    val t = TestGraph()
    val a = t.sym("a")
    val b = t.sym("b")
    val fa = t.node("f", a)
    val fb = t.node("f", b)
    assertNotEquals(fa, fb)

  test("an application needs arguments"):
    val t = TestGraph()
    intercept[IllegalArgumentException]:
      App(t.sym("a"), ArraySeq.empty)

  test("find returns self for fresh class"):
    val t = TestGraph()
    val a = t.sym("a")
    assertEquals(t.find(a), a)

  test("merge makes find return same representative"):
    val t = TestGraph()
    val a = t.sym("a")
    val b = t.sym("b")
    t.merge(a, b)
    assertEquals(t.find(a), t.find(b))

  test("merge is idempotent"):
    val t = TestGraph()
    val a = t.sym("a")
    val b = t.sym("b")
    t.merge(a, b)
    t.merge(a, b)
    assertEquals(t.find(a), t.find(b))

  test("merge is transitive"):
    val t = TestGraph()
    val a = t.sym("a")
    val b = t.sym("b")
    val c = t.sym("c")
    t.merge(a, b)
    t.merge(b, c)
    assertEquals(t.find(a), t.find(c))

  test("congruence: merge args triggers merge of parents"):
    val t = TestGraph()
    val a = t.sym("a")
    val b = t.sym("b")
    val fa = t.node("f", a)
    val fb = t.node("f", b)
    assertNotEquals(t.find(fa), t.find(fb))

    t.merge(a, b)
    t.rebuild()
    assertEquals(t.find(fa), t.find(fb))

  test("congruence propagates through multiple levels"):
    val t = TestGraph()
    val a = t.sym("a")
    val b = t.sym("b")
    val fa = t.node("f", a)
    val fb = t.node("f", b)
    val gfa = t.node("g", fa)
    val gfb = t.node("g", fb)

    t.merge(a, b)
    t.rebuild()
    assertEquals(t.find(fa), t.find(fb))
    assertEquals(t.find(gfa), t.find(gfb))

  test("congruence with fun merge: merging function symbols"):
    val t = TestGraph()
    val a = t.sym("a")
    val f = t.sym("f")
    val g = t.sym("g")
    val fa = t.node("f", a)
    val ga = t.node("g", a)
    assertNotEquals(t.find(fa), t.find(ga))

    t.merge(f, g)
    t.rebuild()
    assertEquals(t.find(fa), t.find(ga))

  test("add after merge uses canonical form"):
    val t = TestGraph()
    val a = t.sym("a")
    val b = t.sym("b")
    val fa = t.node("f", a)
    t.merge(a, b)
    t.rebuild()
    val fb = t.node("f", b)
    assertEquals(t.find(fa), t.find(fb))

  test("binary node congruence"):
    val t = TestGraph()
    val a = t.sym("a")
    val b = t.sym("b")
    val c = t.sym("c")
    val d = t.sym("d")
    val ab = t.node("+", a, b)
    val cd = t.node("+", c, d)
    assertNotEquals(t.find(ab), t.find(cd))

    t.merge(a, c)
    t.merge(b, d)
    t.rebuild()
    assertEquals(t.find(ab), t.find(cd))

  // Cyclic tests inspired by Nelson & Oppen's congruence closure

  test("cycle: f(a) = a (fixed point)"):
    val t = TestGraph()
    val a = t.sym("a")
    val fa = t.node("f", a)
    t.merge(a, fa)
    t.rebuild()
    assertEquals(t.find(a), t.find(fa))
    // f(f(a)) should also equal a by congruence
    val ffa = t.node("f", fa)
    assertEquals(t.find(a), t.find(ffa))

  test("cycle: f(f(a)) = a (2-cycle)"):
    val t = TestGraph()
    val a = t.sym("a")
    val fa = t.node("f", a)
    val ffa = t.node("f", fa)
    t.merge(a, ffa)
    t.rebuild()
    assertEquals(t.find(a), t.find(ffa))
    // f(a) and f(f(f(a))) should also be equivalent
    val fffa = t.node("f", ffa)
    assertEquals(t.find(fa), t.find(fffa))

  test("cycle: f(a) = a implies f(b) = b when a = b"):
    val t = TestGraph()
    val a = t.sym("a")
    val b = t.sym("b")
    val fa = t.node("f", a)
    val fb = t.node("f", b)
    t.merge(a, fa) // f(a) = a
    t.merge(a, b) // a = b
    t.rebuild()
    assertEquals(t.find(b), t.find(fb))

  test("cycle: f(a) = a and g(a) = a implies f(g(a)) = a"):
    val t = TestGraph()
    val a = t.sym("a")
    val fa = t.node("f", a)
    val ga = t.node("g", a)
    t.merge(a, fa) // f(a) = a
    t.merge(a, ga) // g(a) = a
    t.rebuild()
    // f(g(a)) = f(a) = a
    val fga = t.node("f", ga)
    assertEquals(t.find(a), t.find(fga))

  test("cycle: mutual fixed points f(a) = b, f(b) = a implies a = b"):
    val t = TestGraph()
    val a = t.sym("a")
    val b = t.sym("b")
    val fa = t.node("f", a)
    val fb = t.node("f", b)
    t.merge(fa, b) // f(a) = b
    t.merge(fb, a) // f(b) = a
    t.rebuild()
    assertEquals(t.find(fa), t.find(b))
    assertEquals(t.find(fb), t.find(a))

  test("random merges: every canonical form belongs to exactly one class"):
    val t = TestGraph()
    val rnd = scala.util.Random(7)
    val ids = ArrayBuffer.fill(50)(t.eg.newClass())
    for _ <- 0 until 200 do ids += t.node("h", ids(rnd.nextInt(ids.size)), ids(rnd.nextInt(ids.size)))
    for _ <- 0 until 40 do t.merge(ids(rnd.nextInt(ids.size)), ids(rnd.nextInt(ids.size)))
    t.rebuild()
    val classOfForm = HashMap.empty[(EClassId, Seq[EClassId]), EClassId]
    var nodes = 0
    for (cls, ns) <- t.eg.classes; App(fun, args) <- ns do
      nodes += 1
      val form = (t.find(fun), args.map(t.find))
      assertEquals(classOfForm.getOrElseUpdate(form, cls), cls) // congruent nodes share a class
      assertEquals(t.find(t.eg.add(App(fun, args))), cls) // and the congruence table knows the node
    assert(nodes > 100)

  test("pop undoes merges and their congruences"):
    val t = TestGraph()
    val a = t.sym("a")
    val b = t.sym("b")
    val fa = t.node("f", a)
    val fb = t.node("f", b)
    t.push()
    t.merge(a, b)
    t.rebuild()
    assertEquals(t.find(fa), t.find(fb))
    t.pop()
    assertNotEquals(t.find(a), t.find(b))
    assertNotEquals(t.find(fa), t.find(fb))
    assertEquals(t.find(t.node("f", b)), t.find(fb)) // the congruence table is restored too
    assertEquals(t.eg.level, 0)

  test("pop undoes nodes and classes added in the level"):
    val t = TestGraph()
    val a = t.sym("a")
    val fa = t.node("f", a)
    t.sym("g") // symbols created inside the level would be popped with it
    val n = t.eg.classCount
    t.push()
    val ga = t.node("g", a)
    t.merge(ga, fa)
    t.rebuild()
    t.pop()
    assertEquals(t.eg.classCount, n)
    assertEquals(t.node("g", a), ga) // fresh again, and gets the same id back
    assertNotEquals(t.find(ga), t.find(fa))
    assertEquals(t.find(t.node("f", a)), t.find(fa)) // still there

  test("levels nest"):
    val t = TestGraph()
    val a = t.sym("a")
    val b = t.sym("b")
    val c = t.sym("c")
    t.push()
    t.merge(a, b)
    t.push()
    t.merge(b, c)
    t.rebuild()
    assertEquals(t.find(a), t.find(c))
    t.pop()
    assertEquals(t.find(a), t.find(b))
    assertNotEquals(t.find(a), t.find(c))
    t.pop()
    assertNotEquals(t.find(a), t.find(b))

  test("pop without push fails"):
    val t = TestGraph()
    intercept[IllegalArgumentException]:
      t.eg.pop()

  test("random operations with push/pop match a replay of the kept operations"):
    enum Op:
      case Add(f: EClassId, x: EClassId, y: EClassId)
      case Merge(x: EClassId, y: EClassId)
      case Diseq(x: EClassId, y: EClassId)
      case Rebuild
    // The kept operations: one list per open level, the last one being the current level.
    val kept = ArrayBuffer(ArrayBuffer.empty[Op])
    def replay(): EGraph =
      val eg = EGraph()
      for _ <- 0 to 20 do eg.newClass() // h and the leaves
      for level <- kept; op <- level do
        op match
          case Op.Add(f, x, y) => eg.add(App(f, ArraySeq(x, y)))
          case Op.Merge(x, y) => eg.merge(x, y, 0)
          case Op.Diseq(x, y) => eg.disequate(x, y, 0)
          case Op.Rebuild => eg.rebuild()
      eg
    // Representation-independent view: classes as sets of ids, nodes keyed by the smallest id of their class.
    def state(eg: EGraph) =
      val classes = (0 until eg.classCount).groupBy(eg.find).values.map(_.toSet).toSet
      val canon = (0 until eg.classCount).map(id =>
        id -> (0 until eg.classCount).filter(eg.find(_) == eg.find(id)).min
      ).toMap
      val nodes =
        eg.classes.map((cls, ns) => canon(cls) -> ns.map(app => (canon(app.fun), app.args.map(canon))).toSet)
      val reps = (0 until eg.classCount).filter(id => eg.find(id) == id)
      val diseqs = (for r1 <- reps; r2 <- reps if r1 < r2 && eg.areDisequal(r1, r2) yield (canon(r1), canon(r2))).toSet
      (eg.classCount, classes, nodes, diseqs, eg.conflict.isDefined)

    val rnd = scala.util.Random(11)
    val eg = EGraph()
    val h = eg.newClass()
    val ids = ArrayBuffer.fill(20)(eg.newClass())
    val snapshots = ArrayBuffer.empty[Any] // state at each push
    var pops = 0
    for step <- 0 until 600 do
      rnd.nextInt(10) match
        case 0 | 1 | 2 =>
          val x = ids(rnd.nextInt(ids.size))
          val y = ids(rnd.nextInt(ids.size))
          ids += eg.add(App(h, ArraySeq(x, y)))
          kept.last += Op.Add(h, x, y)
        case 3 =>
          val x = ids(rnd.nextInt(ids.size))
          val y = ids(rnd.nextInt(ids.size))
          eg.disequate(x, y, step)
          kept.last += Op.Diseq(x, y)
        case 4 | 5 | 6 =>
          val x = ids(rnd.nextInt(ids.size))
          val y = ids(rnd.nextInt(ids.size))
          eg.merge(x, y, step)
          kept.last += Op.Merge(x, y)
          if rnd.nextBoolean() then
            eg.rebuild()
            kept.last += Op.Rebuild
        case 7 | 8 =>
          eg.push() // rebuilds first
          kept.last += Op.Rebuild
          snapshots += state(eg)
          kept += ArrayBuffer.empty
        case _ if eg.level > 0 =>
          eg.pop()
          kept.remove(kept.length - 1)
          pops += 1
          ids.filterInPlace(_ < eg.classCount) // drop ids of popped classes
          assertEquals(state(eg), snapshots.remove(snapshots.length - 1), s"pop at step $step vs. push snapshot")
          assertEquals(state(eg), state(replay()), s"pop at step $step vs. replay")
        case _ => ()
    assert(pops > 20)

  test("disequate then merge is a conflict, undone by pop"):
    val t = TestGraph()
    val a = t.sym("a")
    val b = t.sym("b")
    t.disequate(a, b)
    assert(t.eg.areDisequal(a, b))
    assert(t.eg.areDisequal(b, a))
    assert(!t.eg.areDisequal(a, a))
    assertEquals(t.eg.conflict, None)
    t.push()
    t.merge(a, b)
    assert(t.eg.conflict.exists(reasons => reasons.contains(0) && reasons.length == 2)) // the disequality and the merge
    t.pop()
    assertEquals(t.eg.conflict, None)
    assert(t.eg.areDisequal(a, b))

  test("disequality conflict through congruence"):
    val t = TestGraph()
    val a = t.sym("a")
    val b = t.sym("b")
    val fa = t.node("f", a)
    val fb = t.node("f", b)
    t.disequate(fa, fb)
    t.merge(a, b)
    assertEquals(t.eg.conflict, None) // not before the rebuild
    t.rebuild()
    assert(t.eg.conflict.exists(_.contains(0))) // a conflict whose reasons include the disequality's

  test("disequalities follow equalities"):
    val t = TestGraph()
    val a = t.sym("a")
    val b = t.sym("b")
    val c = t.sym("c")
    t.disequate(a, b)
    t.merge(b, c)
    t.rebuild()
    assert(t.eg.areDisequal(a, c))
    assert(!t.eg.areDisequal(b, c))
    assertEquals(t.eg.conflict, None)

  test("disequate within a class is an immediate conflict"):
    val t = TestGraph()
    val a = t.sym("a")
    val b = t.sym("b")
    t.merge(a, b)
    t.disequate(a, b)
    assert(t.eg.conflict.exists(reasons => reasons.contains(0) && reasons.length == 2)) // the disequality and the merge
  test("pop undoes disequalities"):
    val t = TestGraph()
    val a = t.sym("a")
    val b = t.sym("b")
    t.push()
    t.disequate(a, b)
    t.pop()
    assert(!t.eg.areDisequal(a, b))
    t.merge(a, b)
    assertEquals(t.eg.conflict, None)

  test("touched ids: the absorbed class, the smaller side of a disequality, null past the limit"):
    val t = TestGraph()
    val Seq(a, b, c, d, e) = Seq("a", "b", "c", "d", "e").map(t.sym)
    t.merge(a, b) // before anyone watches: not listed
    t.eg.touchedLimit = 10
    assertEquals(t.eg.takeTouched().nn.toSet, Set.empty[EClassId])
    t.merge(a, c) // absorbs c
    assertEquals(t.eg.takeTouched().nn.toSet, Set(c))
    t.eg.takeTouched().nn.clear()
    t.disequate(a, d) // d's class is the smaller
    assertEquals(t.eg.takeTouched().nn.toSet, Set(d))
    t.eg.takeTouched().nn.clear()
    t.merge(d, e) // {d, e} is now disequal to {a, b, c}, and still the smaller
    assertEquals(t.eg.takeTouched().nn.toSet, Set(d, e))
    t.eg.takeTouched().nn.clear()
    t.eg.touchedLimit = 1
    t.merge(a, d)
    assertEquals(t.eg.takeTouched(), null)
    assertEquals(t.eg.takeTouched().nn.toSet, Set.empty[EClassId])

  test("touched ids: random pairs that became equal or disequal have a touched side"):
    val rnd = scala.util.Random(13)
    var checked = 0
    var overflows = 0
    for _ <- 0 until 100 do
      val t = TestGraph()
      val leaves = Seq.tabulate(8)(i => t.sym(s"a$i"))
      val terms = leaves ++ leaves.map(t.node("f", _)) ++ leaves.take(4).map(x => t.node("g", x, leaves(7)))
      t.eg.touchedLimit = if rnd.nextInt(4) == 0 then 4 else 1000
      def term() = terms(rnd.nextInt(terms.length))
      // 1 for equal, 2 for disequal, 0 for neither, of every pair
      def statuses() =
        for x <- terms; y <- terms yield if t.find(x) == t.find(y) then 1 else if t.eg.areDisequal(x, y) then 2 else 0
      var before = statuses()
      for _ <- 0 until 40 do
        for _ <- 0 to rnd.nextInt(3) do
          rnd.nextInt(8) match
            case 0 | 1 => t.eg.push()
            case 2 => if t.eg.level > 0 then t.eg.pop()
            case 3 => t.disequate(term(), term())
            case _ => t.merge(term(), term())
        t.eg.rebuild()
        if t.eg.conflict.isEmpty then // as a theory does, which looks at nothing on a conflict
          val ids = t.eg.takeTouched()
          val after = statuses()
          if ids == null then overflows += 1
          else
            val listed = ids.toSet
            for i <- terms.indices; j <- terms.indices do
              val k = i * terms.length + j
              if after(k) != 0 && after(k) != before(k) then
                checked += 1
                assert(
                  listed(terms(i)) || listed(terms(j)),
                  s"${terms(i)} and ${terms(j)}: ${before(k)} to ${after(k)}"
                )
            ids.clear()
          before = after
    assert(checked > 1000 && overflows > 10, s"$checked pairs checked, $overflows overflows")

  test("explain: transitivity, with the relevant reasons only"):
    val t = TestGraph()
    val a = t.sym("a")
    val b = t.sym("b")
    val c = t.sym("c")
    val d = t.sym("d")
    t.merge(a, b, 1)
    t.merge(c, d, 2)
    t.merge(b, c, 3)
    assertEquals(t.explain(a, b), Seq(1))
    assertEquals(t.explain(a, c), Seq(1, 3))
    assertEquals(t.explain(a, d), Seq(1, 2, 3))
    assertEquals(t.explain(d, a), Seq(1, 2, 3))
    assertEquals(t.explain(a, a), Seq())

  test("explain: congruence, nested"):
    val t = TestGraph()
    val a = t.sym("a")
    val b = t.sym("b")
    val fa = t.node("f", a)
    val fb = t.node("f", b)
    val gfa = t.node("g", fa)
    val gfb = t.node("g", fb)
    t.merge(a, b, 1)
    t.rebuild()
    assertEquals(t.explain(fa, fb), Seq(1))
    assertEquals(t.explain(gfa, gfb), Seq(1))

  test("explain: shared arguments are justified once"):
    // t(k+1) = g(t(k), t(k)): justifying each edge again under each argument took 2^depth steps.
    val t = TestGraph()
    var x = t.sym("a")
    var y = t.sym("b")
    t.merge(x, y, 1)
    for _ <- 0 until 64 do
      x = t.node("g", x, x)
      y = t.node("g", y, y)
    t.rebuild()
    assertEquals(t.explain(x, y), Seq(1))

  test("explain: a term added after the equality it depends on"):
    val t = TestGraph()
    val a = t.sym("a")
    val c = t.sym("c")
    t.merge(a, c, 1)
    val fa = t.node("f", a)
    val fc = t.node("f", c)
    assertEquals(t.find(fa), t.find(fc))
    assertEquals(t.explain(fa, fc), Seq(1))

  test("explain: merged function symbols"):
    val t = TestGraph()
    val a = t.sym("a")
    val fa = t.node("f", a)
    val ga = t.node("g", a)
    t.merge(t.sym("f"), t.sym("g"), 4)
    t.rebuild()
    assertEquals(t.explain(fa, ga), Seq(4))

  test("explain: popped reasons are gone"):
    val t = TestGraph()
    val a = t.sym("a")
    val b = t.sym("b")
    val c = t.sym("c")
    t.merge(a, b, 1)
    t.push()
    t.merge(b, c, 2)
    assertEquals(t.explain(a, c), Seq(1, 2))
    t.pop()
    t.merge(a, c, 3)
    assertEquals(t.explain(a, c), Seq(3))
    assertEquals(t.explain(b, c), Seq(1, 3))

  test("explain: disequality conflict"):
    val t = TestGraph()
    val a = t.sym("a")
    val b = t.sym("b")
    val c = t.sym("c")
    t.eg.disequate(a, b, 5)
    t.merge(a, c, 1)
    t.merge(c, b, 2)
    assert(t.eg.conflict.exists(_.contains(5))) // a conflict whose reasons include the disequality's
    assertEquals(t.explain(a, b), Seq(1, 2))

  test("explain requires equal terms"):
    val t = TestGraph()
    intercept[IllegalArgumentException]:
      t.eg.explain(t.sym("a"), t.sym("b"))

  test("random explanations are sound: replaying only their reasons re-derives the equality"):
    enum Op:
      case Add(x: EClassId, y: EClassId)
      case Merge(x: EClassId, y: EClassId, reason: Int)
    val rnd = scala.util.Random(5)
    val eg = EGraph()
    val h = eg.newClass()
    val ids = ArrayBuffer.fill(15)(eg.newClass())
    val ops = ArrayBuffer.empty[Op]
    for step <- 0 until 300 do
      val x = ids(rnd.nextInt(ids.size))
      val y = ids(rnd.nextInt(ids.size))
      if rnd.nextInt(3) == 0 then
        ops += Op.Add(x, y)
        ids += eg.add(App(h, ArraySeq(x, y)))
      else
        ops += Op.Merge(x, y, step)
        eg.merge(x, y, step)
        if rnd.nextInt(4) == 0 then eg.rebuild()
    eg.rebuild()
    // Replay the adds (same ids) and only the merges with the given reasons.
    def derives(reasons: Set[Int], x: EClassId, y: EClassId): Boolean =
      val g = EGraph()
      for _ <- 0 to 15 do g.newClass()
      for op <- ops do
        op match
          case Op.Add(a, b) => g.add(App(h, ArraySeq(a, b)))
          case Op.Merge(a, b, r) => if reasons(r) then g.merge(a, b, r)
      g.rebuild()
      g.find(x) == g.find(y)
    var checked = 0
    for _ <- 0 until 300 do
      val x = ids(rnd.nextInt(ids.size))
      val y = ids(rnd.nextInt(ids.size))
      if eg.find(x) == eg.find(y) then
        checked += 1
        val reasons = eg.explain(x, y)
        assertEquals(reasons.distinct.length, reasons.length)
        assert(derives(reasons.toSet, x, y), s"$x = $y not derivable from $reasons")
    assert(checked > 100)

  test("disequality: sides oriented by class, for propagating negated atoms"):
    val t = TestGraph()
    val a = t.sym("a")
    val b = t.sym("b")
    val c = t.sym("c")
    val d = t.sym("d")
    t.eg.disequate(a, b, 5)
    t.merge(b, c, 1)
    t.merge(a, d, 2)
    assertEquals(t.eg.disequality(c, d), Some((b, a, 5)))
    assertEquals(t.eg.disequality(d, c), Some((a, b, 5)))
    assertEquals(t.eg.disequality(a, a), None)
    assertEquals(t.eg.disequality(a, t.sym("e")), None)
    assertEquals(t.explain(c, b) ++ t.explain(d, a), Seq(1, 2))

  /** A toy theory: `f` is idempotent (`f(f(x)) = f(x)`, on addition), `g` is
   *  injective (`g(x) = g(y)` implies `x = y`, on merge), and `a` and `b` may
   *  never be equal (a contradiction on merge); the final check forbids `g(a)`.
   */
  class ToyRules(f: EClassId, g: EClassId, a: EClassId, b: EClassId) extends Rules:
    var pushes = 0
    override def added(eg: EGraph, app: App, cls: EClassId): Unit =
      if app.fun == f && eg.nodes(app.args(0)).exists((inner, _) => eg.find(inner.fun) == f) then
        eg.derive(
          cls,
          app.args(0),
          List((app.args(0), eg.find(app.args(0))))
        ) // f(f(x)) = f(x): the argument is an f-node
    override def merged(
        eg: EGraph,
        from: EClassId,
        into: EClassId,
        members: Iterable[EClassId],
        parents: Iterable[(App, EClassId)]
    ): Unit =
      if eg.find(a) == eg.find(b) && eg.conflict.isEmpty then eg.contradiction(List((a, b)))
      val gs = eg.nodes(into).filter((n, _) => eg.find(n.fun) == g).toList
      for ((n1, c1), (n2, c2)) <- gs.zip(gs.drop(1)) do
        eg.derive(n1.args(0), n2.args(0), List((c1, c2))) // the g-nodes are equal
    override def finalCheck(eg: EGraph): Option[Seq[(EClassId, EClassId)]] =
      eg.parents(a).find((p, _) => eg.find(p.fun) == g && eg.find(p.args(0)) == eg.find(a)).map(_ => List((a, a)))
    override def push(): Unit = pushes += 1
    override def pop(): Unit = pushes -= 1

  test("rules: idempotence on addition, with the explanation of the premise"):
    val eg = EGraph(ToyRules(0, 1, 2, 3))
    for _ <- 0 until 5 do eg.newClass() // f = 0, g = 1, a = 2, b = 3, c = 4
    val fa = eg.add(App(0, ArraySeq(2)))
    val ffa = eg.add(App(0, ArraySeq(fa)))
    assertEquals(eg.find(ffa), eg.find(fa))
    assertEquals(eg.explain(ffa, fa).toList, Nil) // the premise holds trivially
    // through a merge: c = f(a) asserted, then f(c) is f(f(a))
    eg.merge(4, fa, 7)
    eg.rebuild()
    val fc = eg.add(App(0, ArraySeq(4)))
    assertEquals(eg.find(fc), eg.find(fa))
    assertEquals(eg.explain(fc, 4).toList, List(7))

  test("rules: injectivity on merge, contradiction, final check, levels"):
    val rules = ToyRules(0, 1, 2, 3)
    val eg = EGraph(rules)
    for _ <- 0 until 6 do eg.newClass() // f = 0, g = 1, a = 2, b = 3, x = 4, y = 5
    val gx = eg.add(App(1, ArraySeq(4)))
    val gy = eg.add(App(1, ArraySeq(5)))
    eg.push()
    assertEquals(rules.pushes, 1)
    eg.merge(gx, gy, 9)
    eg.rebuild()
    assertEquals(eg.find(4), eg.find(5)) // x = y by injectivity
    assertEquals(eg.explain(4, 5).toList, List(9))
    eg.pop()
    assertEquals(rules.pushes, 0)
    assert(eg.find(4) != eg.find(5))
    eg.push()
    eg.merge(2, 3, 11)
    eg.rebuild()
    assertEquals(eg.conflict.map(_.toList), Some(List(11)))
    eg.pop()
    assertEquals(eg.conflict, None)
    assertEquals(eg.finalCheck(), None)
    eg.add(App(1, ArraySeq(2)))
    assertEquals(eg.finalCheck().map(_.toList), Some(List((2, 2))))
