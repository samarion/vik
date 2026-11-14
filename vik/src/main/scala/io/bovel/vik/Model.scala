package io.bovel.vik

import io.bovel.lia

/** A model of a `Sat` answer, taken from the engines before the solver unwound:
 *  values for the declared constants, and a finite graph per declared function
 *  — the applications the problem mentions, and a default.
 *
 *  Values are closed terms: a numeral, `true`/`false` as a [[Term.Bool]], a
 *  constructor application for a datatype, an abstract element `@Sort!k` for an
 *  uninterpreted sort — distinct constants map to distinct elements exactly
 *  when the e-graph kept them apart — or, for an array, the SMT-LIB form
 *  `(store (store ((as const (Array I E)) d) i v) j w)`: a default `d` and the
 *  indices the problem read or wrote ([[Model.select]], [[Model.store]]).
 */
final case class Model(
    constants: Map[String, Term],
    functions: Map[String, Model.Function],
    datatypes: List[io.bovel.smtlib.Datatype] = Nil
):
  /** A selector's constructor and position, a tester's constructor. */
  private lazy val constructors: Set[String] = datatypes.flatMap(_.constructors).map(_.name).toSet
  private lazy val selectors: Map[String, (String, Int)] =
    (for d <- datatypes; c <- d.constructors; ((s, _), i) <- c.selectors.zipWithIndex yield s -> (c.name, i)).toMap
  private lazy val testers: Map[String, String] =
    (for d <- datatypes; c <- d.constructors yield c.tester -> c.name).toMap

  /** The value of a term under this model: arithmetic is computed, a function
   *  application is looked up in its graph (the default when absent), and an
   *  unknown constant of an uninterpreted sort is itself.
   */
  def value(term: Term): Term = term match
    case Term.Num(_) => term
    case Term.Linear(terms, c) =>
      val values = terms.map((a, t) => (a, rational(value(t))))
      if values.forall(_._2.isDefined) then
        Model.rationalTerm(values.foldLeft(lia.Rational(c)) { case (sum, (a, v)) => sum + lia.Rational(a) * v.get })
      else term // a term the model has no number for: the combination is not one either
    case Term.Const(name) =>
      functions.get(name) match
        case Some(f) if f.parameters.isEmpty => f.default
        case _ => constants.getOrElse(name, term)
    case Term.App(Term.Const(name), List(a, i, v)) if name.startsWith("store!") =>
      Model.store(value(a), value(i), value(v))
    case Term.App(Term.Const(name), List(d)) if name.startsWith("const!") => Model.constArray("?", value(d))
    case Term.App(Term.Const(name), arrays) if name.startsWith("map!") =>
      Model.mapArrays(name.split('!')(1), arrays.map(value))
    case Term.App(Term.Const(name), List(arg)) if selectors.contains(name) => // a selector on a constructor value
      val (constructor, i) = selectors(name)
      value(arg) match
        case Term.App(Term.Const(c), args) if c == constructor => args(i)
        case v => lookup(name, List(v)) // another constructor's value: unconstrained, the graph's choice
    case Term.App(Term.Const(name), List(arg)) if testers.contains(name) =>
      val holds = value(arg) match
        case Term.App(Term.Const(c), _) => c == testers(name)
        case Term.Const(c) => c == testers(name)
        case _ => false
      Term.boolean(if holds then Formula.True else Formula.False)
    case Term.App(fun, List(index)) if Model.isArray(value(fun)) => Model.select(value(fun), value(index))
    // A constructor application is a value once its arguments are: through the graph it would get the
    // default, an abstract element, for a term the solver never saw (a definition of the simplifier's).
    case Term.App(Term.Const(name), args) if constructors.contains(name) => Term.App(Term.Const(name), args.map(value))
    case Term.App(Term.Const(name), args) => lookup(name, args.map(value))
    case Term.Bool(formula) => Term.boolean(if holds(formula) then Formula.True else Formula.False)
    case _ => term

  /** This model with a constant valued by its definition — `k = t`, or
   *  `c ⇒ k = t` when `c` holds, or the two bounds of an integer equality — the
   *  way the lowering states one for a term-level `ite`; only a name `fresh`
   *  accepts is bound, never a declared one, which a definition of the
   *  lowering's mentions as a value, not as the defined (issue 28).
   */
  def defined(definition: Formula, fresh: String => Boolean): Model =
    def bind(k: String, t: Term): Model = if fresh(k) then copy(constants = constants + (k -> value(t))) else this
    definition match
      case Formula.Implies(c, body) => if holds(c) then defined(body, fresh) else this
      case Formula.Eq(Term.Const(k), t) if fresh(k) => bind(k, t)
      case Formula.Eq(t, Term.Const(k)) if fresh(k) => bind(k, t)
      case Formula.And(List(Formula.Le(Term.Const(k), t), Formula.Le(u, Term.Const(k2)))) if k == k2 && t == u =>
        bind(k, t) // `IntEq`, the fresh constant on the left
      case Formula.And(List(Formula.Le(t, Term.Const(k)), Formula.Le(Term.Const(k2), u))) if k == k2 && t == u =>
        bind(k, t) // `IntEq`, the fresh constant on the right
      case _ => this

  /** A function application by the function's graph: the row of the argument
   *  values, else the default; the application itself for an unknown symbol.
   */
  private def lookup(name: String, values: List[Term]): Term = functions.get(name) match
    // Array arguments are compared extensionally: a row keyed by a store read back is one (issue 49).
    case Some(f) =>
      f.rows.collectFirst { case (a, r) if a.length == values.length && a.zip(values).forall(Model.same) => r }
        .getOrElse(f.default)
    case None => Term.App(Term.Const(name), values)

  /** Whether a formula holds under this model. */
  def holds(formula: Formula): Boolean = formula match
    case Formula.True => true
    case Formula.False => false
    case Formula.Not(a) => !holds(a)
    case Formula.And(as) => as.forall(holds)
    case Formula.Or(as) => as.exists(holds)
    case Formula.Implies(a, b) => !holds(a) || holds(b)
    case Formula.Iff(a, b) => holds(a) == holds(b)
    case Formula.Ite(c, t, e) => if holds(c) then holds(t) else holds(e)
    case Formula.Eq(l, r) => Model.same(value(l), value(r))
    // Failing closed: a side the model has no number for makes no bound hold (issue 35).
    case Formula.Le(l, r) => rational(value(l)).zip(rational(value(r))).exists(_ <= _)
    case Formula.Less(l, r) => rational(value(l)).zip(rational(value(r))).exists(_ < _)
    case Formula.Pred(t) => value(t) == Term.Bool(Formula.True)

  private def rational(t: Term): Option[lia.Rational] = t match
    case Term.Num(v) => Some(lia.Rational(v))
    case Term.App(Term.Const("/"), List(p, q)) => rational(p).zip(rational(q)).map(_ / _)
    case _ => None // not a number the model knows

object Model:
  /** A rational as a term: a numeral, or `(/ num den)`. */
  def rationalTerm(r: lia.Rational): Term =
    if r.isInteger then Term.Num(r.num)
    else Term.App(Term.Const("/"), List(Term.Num(r.num), Term.Num(r.den)))

  /** A declared function in a model: its parameter sorts, result sort, the rows
   *  of its graph (argument values to result value) and the value everywhere
   *  else.
   */
  final case class Function(parameters: List[String], result: String, rows: List[(List[Term], Term)], default: Term)

  /** The array of sort `sort` (as SMT-LIB writes it) holding `default`
   *  everywhere: `((as const (Array I E)) d)`.
   */
  def constArray(sort: String, default: Term): Term = Term.App(Term.Const(s"(as const $sort)"), List(default))

  /** `array` with `value` at `index`: `(store array index value)`. */
  def store(array: Term, index: Term, value: Term): Term = Term.App(Term.Const("store"), List(array, index, value))

  /** The map of a Boolean connective (`and`, `or`, `not`, `=>`) over array
   *  values: the connective of the defaults, and of the elements at every index
   *  one of the arrays writes.
   */
  def mapArrays(op: String, arrays: List[Term]): Term =
    def connective(values: List[Term]): Term =
      val bs = values.map(_ == Term.Bool(Formula.True))
      val b = op match
        case "and" => bs.forall(identity)
        case "or" => bs.exists(identity)
        case "not" => !bs.head
        case _ => !bs.head || bs(1)
      Term.Bool(if b then Formula.True else Formula.False)
    def constant(array: Term): Option[String] = array match
      case Term.App(Term.Const("store"), List(a, _, _)) => constant(a)
      case Term.App(Term.Const(name), List(_)) if name.startsWith("(as const ") => Some(name)
      case _ => None
    val graphs = arrays.map(graph)
    val name = arrays.flatMap(constant).headOption.getOrElse("(as const ?)")
    val default = connective(graphs.map(_._1))
    val indices = graphs.flatMap(_._2.keys).distinct.sortBy(_.toString)
    indices.foldLeft(Term.App(Term.Const(name), List(default)): Term) { (acc, i) =>
      val v = connective(arrays.map(select(_, i)))
      if v == default then acc else store(acc, i, v)
    }

  /** Whether a value is an array, in the form above. */
  def isArray(value: Term): Boolean = value match
    case Term.App(Term.Const("store"), List(_, _, _)) => true
    case Term.App(Term.Const(name), List(_)) => name.startsWith("(as const ")
    case _ => false

  /** The element of an array value at an index: the innermost write to it, else
   *  the default.
   */
  def select(array: Term, index: Term): Term = array match
    case Term.App(Term.Const("store"), List(a, i, v)) => if same(i, index) then v else select(a, index)
    case Term.App(Term.Const(name), List(d)) if name.startsWith("(as const ") => d
    case _ => Term.App(array, List(index))

  /** An array value as its default and the map of the indices written to a
   *  value other than it.
   */
  def graph(array: Term): (Term, Map[Term, Term]) = array match
    case Term.App(Term.Const("store"), List(a, i, v)) =>
      val (d, m) = graph(a)
      (d, if same(v, d) then m - i else m.updated(i, v))
    case Term.App(Term.Const(_), List(d)) => (d, Map.empty)
    case _ => (array, Map.empty)

  /** Whether two values are the same: arrays extensionally (their elements
   *  likewise, for arrays of arrays), the rest as terms.
   */
  def same(a: Term, b: Term): Boolean =
    if isArray(a) && isArray(b) then
      val ((da, ma), (db, mb)) = (graph(a), graph(b))
      same(da, db) && ma.keySet == mb.keySet && ma.forall((i, v) => same(v, mb(i)))
    else a == b
