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
 *
 *  Two values are the same exactly when their normal forms are equal
 *  ([[Model.normal]]): an array is its default and its other writes, in one
 *  order, below a constructor and as an index too (#193).
 */
final case class Model(
    constants: Map[String, Term],
    functions: Map[String, Model.Function],
    datatypes: List[Datatype] = Nil
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
    case Term.App(Term.Const(name), List(a, i, v)) if Names.isStore(name) =>
      Model.store(value(a), value(i), value(v))
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
    // Without arrays the same values are equal values, and the row is found by its key: a scan of the rows
    // per application made the check of a model quadratic in the applications of a function.
    case Some(f) =>
      val row =
        if anyArray then
          f.rows.collectFirst { case (a, r) if a.length == values.length && a.zip(values).forall(same) => r }
        else f.byArguments.get(values)
      row.getOrElse(f.default)
    case None => Term.App(Term.Const(name), values)

  /** Whether `value` is a value of `sort`, a sort as the solver knows it: a
   *  number of a range of the integers lies in the range, and so do the fields
   *  of a constructor's value, the indices and the elements of an array's. No
   *  assertion says so (the sort does), hence no assertion found false shows a
   *  number out of its range: the check of a model asks here.
   */
  def ofSort(value: Term, sort: Sort): Boolean = (value, sort) match
    case (Term.Num(v), Sort.IntRange(lower, upper)) => lower <= v && v <= upper
    case (Term.App(Term.Const("store"), List(a, i, v)), Sort.Fun(index :: rest, result)) =>
      ofSort(a, sort) && ofSort(i, index) && ofSort(v, Sort.fun(rest, result))
    case (Term.App(Term.Const(name), List(d)), Sort.Fun(_ :: rest, result)) if name.startsWith("(as const ") =>
      ofSort(d, Sort.fun(rest, result))
    case (Term.App(Term.Const(c), args), Sort.Named(_)) =>
      fields.get(c).forall(sorts => sorts.length != args.length || args.zip(sorts).forall(ofSort))
    case _ => true

  /** Whether two values are the same ([[Model.same]]). In a model with no array
   *  anywhere, a value is its own normal form, and two values are compared as
   *  they are: looking for an array inside each at every comparison took the
   *  model check of a Stainless session from 2.4 s to 3.2 s.
   */
  def same(a: Term, b: Term): Boolean = a == b || (anyArray && Model.same(a, b))

  private lazy val anyArray: Boolean =
    datatypes.exists(_.constructors.exists(_.selectors.exists((_, s) => s.arrow.isDefined)))
      || functions.valuesIterator.exists(f => (f.result :: f.parameters).exists(_.arrow.isDefined))
      || constants.valuesIterator.exists(Model.isArray)

  private lazy val fields: Map[String, List[Sort]] =
    (for d <- datatypes; c <- d.constructors yield c.name -> c.selectors.map(_._2)).toMap

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
    case Formula.Eq(l, r) => same(value(l), value(r))
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
  final case class Function(parameters: List[Sort], result: Sort, rows: List[(List[Term], Term)], default: Term):
    /** The rows by their arguments, the first of a key as a scan finds it. */
    lazy val byArguments: Map[List[Term], Term] = rows.reverseIterator.toMap

  /** The array of sort `sort` (the function sort the solver knows it by)
   *  holding `default` everywhere: `((as const (Array I E)) d)`.
   */
  def constArray(sort: Sort, default: Term): Term =
    Term.App(Term.Const(s"(as const ${sort.arrayText})"), List(default))

  /** `array` with `value` at `index`: `(store array index value)`. */
  def store(array: Term, index: Term, value: Term): Term = Term.App(Term.Const("store"), List(array, index, value))

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
   *  value other than it, all in normal form ([[normal]]).
   */
  def graph(array: Term): (Term, Map[Term, Term]) = array match
    case Term.App(Term.Const("store"), List(a, i, v)) =>
      val (d, m) = graph(a)
      val (index, value) = (normal(i), normal(v))
      (d, if value == d then m - index else m.updated(index, value))
    case Term.App(Term.Const(_), List(d)) => (normal(d), Map.empty)
    case _ => (array, Map.empty)

  /** Whether two values are the same: equal normal forms. A value without an
   *  array is its own normal form, and is compared as it is: normalized at
   *  every comparison, the large datatype values of a Stainless session took
   *  its model check from 2.4 s to 6.5 s.
   */
  def same(a: Term, b: Term): Boolean = a == b || (holdsArray(a) && holdsArray(b) && normal(a) == normal(b))

  private def holdsArray(value: Term): Boolean = isArray(value) ||
    (value match
      case Term.App(Term.Const(name), args) if name != "/" => args.exists(holdsArray)
      case _ => false)

  /** A value in the one form it has among the terms that write it, so that two
   *  values are the same exactly when their normal forms are equal. An array is
   *  its default and its writes of other values, in the order of their indices;
   *  its indices, its elements and a constructor's arguments are normal too, so
   *  that `(C a)` and `(C (store a 0 1))` are one value when `a` holds 1 at 0
   *  (#141), and so are two arrays written at those two values (#180).
   *
   *  Over a finite index sort with few values, an array is the function it is
   *  at every index, and its default the element at the first: over `Bool`, "0
   *  with `true` at 1" and "1 with `false` at 0" are one array, and so are "0
   *  with `false` at 2 and `true` at 1" and "2 with `true` at 1".
   */
  def normal(value: Term): Term =
    if isArray(value) then
      val (d, m) = graph(value)
      val (default, writes) = indexValues(base(value)) match
        case Some(all) if all.nonEmpty =>
          // The function over every index, then the element of the first as the default.
          val first = m.getOrElse(all.head, d)
          (first, (m ++ all.filterNot(m.contains).map(_ -> d)).filter((_, v) => v != first))
        case _ => (d, m)
      writes.toList.sortBy(_._1.toString).foldLeft(Term.App(base(value), List(default)): Term) { case (a, (i, v)) =>
        store(a, i, v)
      }
    else
      value match
        case Term.App(f @ Term.Const(name), args) if name != "/" && args.exists(holdsArray) =>
          Term.App(f, args.map(normal))
        case _ => value

  /** The head of the constant array at the bottom of an array value, `(as const
   *  (Array I E))`.
   */
  private def base(array: Term): Term = array match
    case Term.App(Term.Const("store"), List(a, _, _)) => base(a)
    case Term.App(head, List(_)) => head
    case _ => array

  /** Every value of a finite index sort that a model writes as an index, when
   *  there are few: the Booleans, the bit-vectors of up to 8 bits. Read from
   *  the head of a constant array.
   */
  private def indexValues(head: Term): Option[List[Term]] = head match
    case Term.Const(name) if name.startsWith("(as const (Array ") =>
      val rest = name.stripPrefix("(as const (Array ")
      if rest.startsWith("Bool ") then Some(List(Term.Bool(Formula.False), Term.Bool(Formula.True)))
      else
        """\(_ IntRange (-?\d+) (-?\d+)\) """.r.findPrefixMatchOf(rest).flatMap { m =>
          val (lower, upper) = (BigInt(m.group(1).nn), BigInt(m.group(2).nn))
          Option.when(upper - lower < 256)(List.range(lower, upper + 1).map(Term.Num(_)))
        }
    case _ => None
