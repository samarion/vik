package io.bovel.vik

import scala.collection.mutable.HashMap

import Formula.*
import Term.*

/** Simplifications of a set of assertions before encoding.
 *
 *  Local constant elimination: in a conjunction `c = t ∧ φ` in a positive
 *  position (under `And`, `Or`, the branches of `Ite` and the right side of
 *  `Implies` only: under a negation the conjunction is not an existential
 *  context) where every occurrence of the constant `c` in the whole assertion
 *  set lies inside that conjunction and `t` does not mention `c`, `c` is
 *  existentially local, so the conjunction is equivalent to `φ[t/c]`. This
 *  turns the diamonds of the `eq_diamond` benchmarks,
 *  `(x = y ∧ y = x') ∨ (x = z ∧ z = x')` with `y` and `z` used nowhere else,
 *  into `x = x'`, which the solver then propagates at level 0 instead of
 *  enumerating the paths (z3 and cvc5 preprocess likewise).
 */
object Simplifier:
  /** `interpreted` names constants with a meaning of their own (nullary
   *  constructors of datatypes): they are never eliminated; neither is a
   *  constant of `kept`, formulas asserted alongside but left as they are (the
   *  named ones). Returns the simplified assertions and the constants
   *  eliminated by substitution — an elimination is sound only while no other
   *  assertion mentions the constant, so a caller that keeps the result and
   *  later learns of one must start over. `step` is called at every formula
   *  visited: a caller with a deadline stops the simplification by throwing
   *  from it.
   */
  def simplify(
      assertions: List[Formula],
      interpreted: Set[String] = Set.empty,
      kept: List[Formula] = Nil,
      step: () => Unit = () => ()
  ): (List[Formula], Map[String, Term]) =
    val (out, defined) = simplifyEach(assertions, interpreted, kept, step)
    (out.filter(_ != True), defined)

  /** [[simplify]] with every assertion left at its place: `True` where one
   *  simplified away, for a caller that goes by the places.
   */
  def simplifyEach(
      assertions: List[Formula],
      interpreted: Set[String] = Set.empty,
      kept: List[Formula] = Nil,
      step: () => Unit = () => ()
  ): (List[Formula], Map[String, Term]) =
    val (pairs, defined, _) = traced(assertions, interpreted, kept, step)
    (pairs.map(_._2), defined)

  /** The eliminations of a conjunction: the positions of the equalities it lost
   *  among its conjuncts, each with whether the constant was on the left.
   */
  type Eliminations = List[(Int, Boolean)]

  /** [[simplify]], each assertion with its simplification (`True` included),
   *  and the eliminations of each conjunction that lost equalities, for a proof
   *  that each simplification holds in every model of its assertion
   *  ([[implies]]). A conjunction met twice with different eliminations is left
   *  out of the map: [[implies]] then refuses the simplifications under it.
   */
  def traced(
      assertions: List[Formula],
      interpreted: Set[String] = Set.empty,
      kept: List[Formula] = Nil,
      step: () => Unit = () => ()
  ): (List[(Formula, Formula)], Map[String, Term], Map[Formula, Eliminations]) =
    // The occurrences of every constant over the whole set: one walk, taken the first time a
    // conjunction has an equality to eliminate — most sets have none, and pay nothing.
    lazy val total =
      val counts = HashMap.empty[String, Int]
      for f <- assertions do countConstants(f, counts)
      for f <- kept do countConstants(f, counts)
      for name <- interpreted do counts(name) = Int.MaxValue // never local to a conjunction
      counts
    val defined = HashMap.empty[String, Term]
    val hints = HashMap.empty[Formula, Eliminations | Null]
    val out = assertions.map(f => (f, simplify(f, total, true, defined, hints, step)))
    (out, defined.toMap, hints.collect { case (f, e: List[(Int, Boolean)] @unchecked) => (f, e) }.toMap)

  private def countConstants(f: Formula, counts: HashMap[String, Int]): Unit = f match
    case True | False => ()
    case Not(a) => countConstants(a, counts)
    case And(as) => as.foreach(countConstants(_, counts))
    case Or(as) => as.foreach(countConstants(_, counts))
    case Implies(a, b) =>
      countConstants(a, counts)
      countConstants(b, counts)
    case Iff(a, b) =>
      countConstants(a, counts)
      countConstants(b, counts)
    case Ite(c, t, e) =>
      countConstants(c, counts)
      countConstants(t, counts)
      countConstants(e, counts)
    case Eq(l, r) =>
      countConstants(l, counts)
      countConstants(r, counts)
    case Pred(t) => countConstants(t, counts)
    case Le(l, r) =>
      countConstants(l, counts)
      countConstants(r, counts)
    case Less(l, r) =>
      countConstants(l, counts)
      countConstants(r, counts)

  private def countConstants(t: Term, counts: HashMap[String, Int]): Unit = t match
    case Const(name) => counts(name) = counts.getOrElse(name, 0) + 1
    case App(fun, args) =>
      countConstants(fun, counts)
      args.foreach(countConstants(_, counts))
    case Num(_) => ()
    case Linear(terms, _) => terms.foreach((_, u) => countConstants(u, counts))
    case Bool(formula) => countConstants(formula, counts)

  /** `positive`: whether `f` is in a positive position of the assertion;
   *  `defined` collects each eliminated constant with the term that replaced it
   *  — the terms mention only surviving constants, since earlier substitutions
   *  already went through them — so a model can value the constants the solver
   *  never saw.
   */
  private def simplify(
      f: Formula,
      total: => HashMap[String, Int],
      positive: Boolean,
      defined: HashMap[String, Term],
      hints: HashMap[Formula, Eliminations | Null],
      step: () => Unit
  ): Formula =
    step()
    f match
      case True | False | Eq(_, _) | Pred(_) | Le(_, _) | Less(_, _) => f
      case Not(a) => Not(simplify(a, total, false, defined, hints, step))
      case Or(as) => Or(as.map(simplify(_, total, positive, defined, hints, step)))
      case Implies(a, b) =>
        Implies(simplify(a, total, false, defined, hints, step), simplify(b, total, positive, defined, hints, step))
      case Iff(a, b) =>
        Iff(simplify(a, total, false, defined, hints, step), simplify(b, total, false, defined, hints, step))
      case Ite(c, t, e) => Ite(
          simplify(c, total, false, defined, hints, step),
          simplify(t, total, positive, defined, hints, step),
          simplify(e, total, positive, defined, hints, step)
        )
      case And(as) if !positive => And(as.map(simplify(_, total, false, defined, hints, step)))
      case And(as) =>
        // each conjunct with its position in `as`
        var conjuncts = as.map(simplify(_, total, true, defined, hints, step)).zipWithIndex
        val gone = List.newBuilder[(Int, Boolean)]
        // Eliminate the constants local to this conjunction, one equality at a time. Only a
        // conjunction with an equality `c = t` among its conjuncts is counted: the counting walks
        // the conjunction, and every conjunction nested inside is walked once more per level above.
        var changed = conjuncts.exists(g => isDefinition(g._1))
        while changed do
          changed = false
          val local = HashMap.empty[String, Int]
          conjuncts.foreach(g => countConstants(g._1, local))
          conjuncts.zipWithIndex.collectFirst {
            case ((Eq(Const(c), t), at), i) if local.getOrElse(c, 0) == total(c) && !mentions(t, c) =>
              (c, t, i, at, true)
            case ((Eq(t, Const(c)), at), i) if local.getOrElse(c, 0) == total(c) && !mentions(t, c) =>
              (c, t, i, at, false)
          } match
            case Some((c, t, i, at, left)) =>
              defined(c) = t
              gone += ((at, left))
              for (name, d) <- defined.toList if name != c do defined(name) = substitute(d, c, t)
              conjuncts = conjuncts.zipWithIndex.collect { case ((g, a), j) if j != i => (substitute(g, c, t), a) }
              // The counts over the whole set follow the conjunction: `c` is gone from it and the
              // constants of `t` now stand where it stood. A count taken once would let a constant
              // that another assertion mentions pass as local, once enough of `t` had been put into
              // this conjunction to match its stale total (issue 12).
              val after = HashMap.empty[String, Int]
              conjuncts.foreach(g => countConstants(g._1, after))
              for name <- local.keySet ++ after.keySet if total.getOrElse(name, 0) != Int.MaxValue do
                total(name) = total.getOrElse(name, 0) - local.getOrElse(name, 0) + after.getOrElse(name, 0)
              changed = true
            case None => ()
        val eliminations = gone.result()
        if eliminations.nonEmpty || hints.contains(f) then
          hints.get(f) match
            case None => hints(f) = eliminations
            case Some(e) => if e != eliminations then hints(f) = null
        conjuncts.map(_._1) match
          case Nil => True
          case single :: Nil => single
          case cs => And(cs)

  private def isDefinition(f: Formula): Boolean = f match
    case Eq(Const(_), _) | Eq(_, Const(_)) => true
    case _ => false

  private def mentions(t: Term, c: String): Boolean = t match
    case Const(name) => name == c
    case App(fun, args) => mentions(fun, c) || args.exists(mentions(_, c))
    case Num(_) => false
    case Linear(terms, _) => terms.exists((_, u) => mentions(u, c))
    case Bool(formula) => formula.terms.exists(mentions(_, c))

  private def substitute(f: Formula, c: String, t: Term): Formula = f match
    case True | False => f
    case Not(a) => Not(substitute(a, c, t))
    case And(as) => And(as.map(substitute(_, c, t)))
    case Or(as) => Or(as.map(substitute(_, c, t)))
    case Implies(a, b) => Implies(substitute(a, c, t), substitute(b, c, t))
    case Iff(a, b) => Iff(substitute(a, c, t), substitute(b, c, t))
    case Ite(a, b, d) => Ite(substitute(a, c, t), substitute(b, c, t), substitute(d, c, t))
    case Eq(l, r) => Eq(substitute(l, c, t), substitute(r, c, t))
    case Pred(u) => Formula.pred(substitute(u, c, t))
    case Le(l, r) => Le(substitute(l, c, t), substitute(r, c, t))
    case Less(l, r) => Less(substitute(l, c, t), substitute(r, c, t))

  private def substitute(u: Term, c: String, t: Term): Term = u match
    case Const(name) => if name == c then t else u
    case App(fun, args) => App(substitute(fun, c, t), args.map(substitute(_, c, t)))
    case Num(_) => u
    case Linear(terms, k) => Term.linear(terms.map((a, v) => (a, substitute(v, c, t))), k)
    case Bool(formula) => Term.boolean(substitute(formula, c, t))

  /** Whether `s` holds in every model of `o`, `s` the simplification of `o`
   *  that drops at each conjunction the equalities `hints` gives it, each
   *  oriented from its constant: the check `proofs/lean` makes of a simplified
   *  input (`Low.simplifies`), over formulas rather than nodes.
   */
  def implies(o: Formula, s: Formula, hints: collection.Map[Formula, Eliminations]): Boolean =
    weaker(o, s, Equalities(Nil), hints)

  private type Expr = Term | Formula

  /** Equalities oriented from their constant, with the pairs `eqv` already
   *  compared under them: the formulas share subterms through `let`, which a
   *  walk without memory visits once per path.
   */
  private final class Equalities(val pairs: List[(Expr, Expr)]):
    val known = HashMap.empty[(Expr, Expr), Boolean]

  private def weaker(o: Formula, s: Formula, eqs: Equalities, hints: collection.Map[Formula, Eliminations])
      : Boolean =
    eqv(o, s, eqs) ||
      ((o, s) match
        case (Or(os), Or(ss)) => os.length == ss.length && os.lazyZip(ss).forall(weaker(_, _, eqs, hints))
        case (Implies(a, b), Implies(a2, b2)) => eqv(a, a2, eqs) && weaker(b, b2, eqs, hints)
        case (Ite(c, a, b), Ite(c2, a2, b2)) =>
          eqv(c, c2, eqs) && weaker(a, a2, eqs, hints) && weaker(b, b2, eqs, hints)
        case (And(os), _) =>
          val elim = hints.getOrElse(o, Nil)
          val more = elim.flatMap((i, left) =>
            os.lift(i) match
              case Some(Eq(x, y)) => List(if left then (x, y) else (y, x))
              case _ => Nil
          )
          val eqs2 = if more.isEmpty then eqs else Equalities(eqs.pairs ++ more)
          os.zipWithIndex.collect { case (g, i) if !elim.exists(_._1 == i) => g } match
            case Nil => s == True
            case x :: Nil => weaker(x, s, eqs2, hints)
            case xs =>
              s match
                case And(ss) => xs.length == ss.length && xs.lazyZip(ss).forall(weaker(_, _, eqs2, hints))
                case _ => false
        case _ => false)

  /** Whether `a` and `b` have the same value where the equalities `eqs` hold,
   *  `a` replaced by the right side of an equality of which it is the left.
   */
  private def eqv(a: Expr, b: Expr, eqs: Equalities): Boolean =
    a == b || eqs.pairs.nonEmpty && eqs.known.getOrElseUpdate(
      (a, b),
      eqs.pairs.exists((x, y) => x == a && eqv(y, b, eqs)) ||
        skeleton(a) == skeleton(b) && {
          val (as, bs) = (children(a), children(b))
          as.length == bs.length && as.lazyZip(bs).forall(eqv(_, _, eqs))
        }
    )

  /** What `Node.skel` keeps of a node: its kind and its data, without its
   *  children.
   */
  private def skeleton(e: Expr): Any = e match
    case Const(n) => ("const", n)
    case App(_, args) => ("app", args.length)
    case Num(v) => ("num", v)
    case Linear(ts, k) => ("linear", ts.map(_._1), k)
    case Bool(_) => "bterm"
    case True => "tt"
    case False => "ff"
    case Not(_) => "not"
    case And(as) => ("and", as.length)
    case Or(as) => ("or", as.length)
    case Implies(_, _) => "implies"
    case Iff(_, _) => "iff"
    case Ite(_, _, _) => "ite"
    case Eq(_, _) => "eq"
    case Pred(_) => "pred"
    case Le(_, _) => "le"
    case Less(_, _) => "lt"

  private def children(e: Expr): List[Expr] = e match
    case Const(_) | Num(_) | True | False => Nil
    case App(f, args) => f :: args
    case Linear(ts, _) => ts.map(_._2)
    case Bool(f) => List(f)
    case Not(a) => List(a)
    case And(as) => as
    case Or(as) => as
    case Implies(a, b) => List(a, b)
    case Iff(a, b) => List(a, b)
    case Ite(c, a, b) => List(c, a, b)
    case Eq(a, b) => List(a, b)
    case Pred(t) => List(t)
    case Le(a, b) => List(a, b)
    case Less(a, b) => List(a, b)
