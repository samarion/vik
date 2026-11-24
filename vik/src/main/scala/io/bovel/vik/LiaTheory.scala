package io.bovel.vik

import scala.collection.mutable.ArrayBuffer

import io.bovel.cdclt.{Lit, Theory, Var}
import io.bovel.lia

/** Linear integer arithmetic as a theory of the CDCL(T) solver: the atom of
 *  variable `v` is `atoms(v)`, on a variable `x` of the LIA solver standing for
 *  an `Int` term or a linear combination: `Bound(x, c)` is `x ≤ c`, its
 *  negation `x ≥ c + 1`; `Equal(x, c)` is `x = c`, its negation the clause of
 *  `Solver.shareIntegers` (an equality of shared terms is such an atom, of the
 *  UF theory as well); or none when `null`. A literal asserts its bounds with
 *  the literal (its index) as reason; `propagate` decides the rational
 *  relaxation (bound propagation and simplex) and `finalCheck` the integers and
 *  the disequalities (branch and bound), both reporting a conflict as the
 *  literals whose bounds are inconsistent. What the bounds already decide is
 *  implied rather than left to the search: an atom whose bounds force it, or
 *  forbid it, is propagated with those bounds as its explanation — which is
 *  what keeps the arrangement of the shared terms of a combination out of the
 *  decisions. `newBound(x, c)`, when given, appends the atom `x ≤ c` to `atoms`
 *  on a variable of its own and returns its literal.
 */
final class LiaTheory(
    solver: lia.Solver,
    atoms: ArrayBuffer[LiaTheory.Atom | Null],
    guided: scala.collection.Set[Var] = Set.empty,
    newBound: ((lia.Var, BigInt) => Lit) | Null = null
) extends Theory:
  // With a way to make atoms, a split the solver keeps meeting is left to the search (see `report`).
  // Note the side effect: the theory turns splitting on demand on in the solver it is given.
  solver.splitOnDemand = newBound != null

  /** A conflict found while asserting, reported by the next `propagate`, with
   *  its certificate when the solver gives them (`lia.Solver.proofs`).
   */
  private var conflict: ArrayBuffer[Lit] | Null = null
  private var conflictCertificate: lia.Certificate | Null = null

  /** The certificate of the last conflict or explanation (see [[certificate]]).
   */
  private var last: lia.Certificate | Null = null

  /** Atoms asserted so far, with the level marks for `pop`; an implied atom is
   *  asserted by the solver in turn, so this is also what `propagate` skips.
   *  `atoms` may grow between solves, so these grow with it.
   */
  private val assigned = ArrayBuffer.empty[Boolean]
  private val assignedTrail = ArrayBuffer.empty[Int]
  private val marks = ArrayBuffer.empty[Int]

  /** For each atom implied, the reasons of the bounds that implied it, and with
   *  proofs, the certificate of its explanation, taken when it was implied: the
   *  bound may have changed by the time the explanation is asked for.
   */
  private val reasonsOf = ArrayBuffer.empty[Set[Int] | Null]
  private val certificateOf = ArrayBuffer.empty[lia.Certificate | Null]

  private def grown(): Unit =
    while assigned.length < atoms.length do
      val v = assigned.length
      assigned += false
      reasonsOf += null
      certificateOf += null
      // A bound atom is indexed by its variable, and looked at when that variable's bounds move; a new
      // one is looked at once, whether they moved or not.
      atoms(v) match
        case LiaTheory.Atom.Bound(x, _, false) =>
          while watchers.length <= x do watchers += null
          if watchers(x) == null then watchers(x) = ArrayBuffer.empty
          watchers(x).nn += v
          fresh += v
        case _ => ()

  private def lits(reasons: Set[Int]): ArrayBuffer[Lit] = ArrayBuffer.from(reasons.map(Lit.fromIndex))

  /** Whether any bound moved since the last check: a decision that concerns no
   *  atom costs nothing.
   */
  private var touched = true

  def assertLit(lit: Lit): Unit =
    grown()
    val v = lit.variable
    val atom = if v < atoms.length then atoms(v) else null
    if atom != null then
      touched = true
      assigned(v) = true
      assignedTrail += v
    if atom != null && conflict == null then
      val result = atom match
        case LiaTheory.Atom.Bound(x, c, strict) =>
          if lit.positive then solver.assertUpper(x, c, strict, lit.index)
          else solver.assertLower(x, c, !strict, lit.index) // not (x ≤ c) is x > c; not (x < c) is x ≥ c
        case LiaTheory.Atom.Equal(x, c) =>
          // False, the atom asserts nothing: the clause of `Solver.shareIntegers` makes the search take
          // one of the two sides, each a bound atom.
          if !lit.positive then lia.Solver.Result.Sat
          else
            solver.assertUpper(x, c, lit.index) match
              case lia.Solver.Result.Sat => solver.assertLower(x, c, lit.index)
              case unsat => unsat
      result match
        case lia.Solver.Result.Unsat(reasons) =>
          conflict = lits(reasons)
          conflictCertificate = solver.conflictCertificate
        case lia.Solver.Result.Sat => ()
        // Asserting a bound never runs the search, so it can neither be told to stop nor ask for a split.
        case lia.Solver.Result.Unknown | lia.Solver.Result.Split(_, _) =>
          throw AssertionError("asserting a bound does not search")

  def propagate(): Theory.Result =
    if !touched && conflict == null then Theory.ok
    else
      touched = false
      report(solver.checkRelaxation())

  override def finalCheck(): Theory.Result = report(solver.check())

  // Model-based combination can need a split before there are any disequality clauses.
  private[vik] var guideBoundsFromModel = false

  /** A bound atom as the relaxation stands to it, for its first decision, on a
   *  problem that can need an arrangement of shared terms. The side of a clause
   *  the search takes is the one already true, and the other bounds start where
   *  the relaxation is. Nothing on a problem without shared terms, where the
   *  conflicts of an unsat search would then all wait for the final check
   *  (measured 200× slower on a bit-vector file); nothing past the first
   *  decision, where phase saving's locality matters more (measured on `Hash`).
   */
  override def phase(v: Var): Option[Boolean] =
    if (guided.nonEmpty || guideBoundsFromModel) && v < atoms.length then
      atoms(v) match
        case LiaTheory.Atom.Bound(x, c, strict) =>
          val value = solver.value(x)
          Some(if strict then value < c else value <= c)
        case _ => None
    else None

  /** The bound atoms of a variable, and the atoms not yet looked at. Only the
   *  bounds are implied: implying an equality of the arrangement was measured
   *  to be far worse (the results of 2026-08-31), because it merges classes the
   *  search then has to take apart again.
   */
  private val watchers = ArrayBuffer.empty[ArrayBuffer[Var] | Null]
  private val fresh = ArrayBuffer.empty[Var]

  /** The atoms the bounds decide, and not yet assigned: those of the variables
   *  whose bounds moved since the last call, and the ones that are new. Walking
   *  every atom at every call cost the same whether anything had changed or
   *  not, which a script that checks often over a problem that stays pays at
   *  every check (bench/results/lia).
   */
  private def implied(): ArrayBuffer[Lit] =
    grown()
    val out = ArrayBuffer.empty[Lit]
    def look(v: Var): Unit =
      if !assigned(v) then
        atoms(v) match
          case LiaTheory.Atom.Bound(x, c, false) =>
            solver.decidesUpper(x, c) match
              case Some((holds, reasons)) =>
                reasonsOf(v) = reasons
                if solver.proofs then certificateOf(v) = solver.decidedCertificate(x, c, holds, Lit(v, !holds).index)
                out += Lit(v, holds)
              case None => ()
          case _ => ()
    for v <- fresh do look(v)
    fresh.clear()
    for x <- solver.takeMoved() do
      if x < watchers.length then
        val watching = watchers(x)
        if watching != null then for v <- watching do look(v)
    out

  private def report(check: => lia.Solver.Result): Theory.Result =
    val pending = conflict
    if pending != null then
      conflict = null
      last = conflictCertificate
      Theory.Result.Conflict(pending)
    else
      check match
        case lia.Solver.Result.Sat => Theory.Result.Ok(implied())
        case lia.Solver.Result.Unknown => Theory.Result.Unknown
        case lia.Solver.Result.Unsat(reasons) =>
          last = solver.conflictCertificate
          Theory.Result.Conflict(lits(reasons))
        // The atom is new: one for the same split would be assigned at a final check, and its bound would
        // keep `x` off the open interval. The right side first, where a first decision would go (the
        // relaxation has `x` above `c`).
        case lia.Solver.Result.Split(x, c) => Theory.Result.Split(newBound.nn(x, c).neg)

  def explain(lit: Lit): ArrayBuffer[Lit] =
    if solver.proofs then last = certificateOf(lit.variable)
    lits(reasonsOf(lit.variable).nn)

  /** A `lia.Certificate` deriving a contradiction from the negations of the
   *  literals of the last conflict or explanation.
   */
  override def certificate(): AnyRef | Null = last

  def push(): Unit =
    marks += assignedTrail.length
    solver.push()

  def pop(): Unit =
    touched = true // undone bounds: atoms may need re-implying
    conflict = null
    conflictCertificate = null
    val mark = marks.remove(marks.length - 1)
    while assignedTrail.length > mark do assigned(assignedTrail.remove(assignedTrail.length - 1)) = false
    solver.pop()

object LiaTheory:
  enum Atom:
    case Bound(x: lia.Var, c: BigInt, strict: Boolean = false)
    case Equal(x: lia.Var, c: BigInt)
