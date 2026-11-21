package io.bovel.vik

import scala.collection.mutable.ArrayBuffer

import io.bovel.cdclt.{Lit, Theory, Var}
import io.bovel.egraph.{EClassId, EGraph}

/** Equality with uninterpreted functions over an [[io.bovel.egraph.EGraph]], as
 *  a theory of the CDCL(T) solver: the atom of variable `v` is `t = u` for
 *  `atoms(v) = (t, u)`, e-classes of `eg`, or none when `atoms(v)` is `null`.
 *  Terms are added to `eg` before solving.
 *
 *  A true atom merges its sides, a false one adds a disequality — or, for the
 *  atom `t = true` of a Boolean-sorted term in `twoValued`, merges `t` with
 *  `false`, so that such terms are two-valued — both with the literal (its
 *  index) as reason; `propagate` rebuilds the congruence closure, reports the
 *  violated disequality's explanation as a conflict, and implies every
 *  unassigned atom whose sides became equal (or disequal). Explanations come
 *  from `EGraph.explain`, whose reasons are the literals asserted.
 */
final class UfTheory(
    eg: EGraph,
    atoms: ArrayBuffer[(EClassId, EClassId) | Null],
    trueClass: EClassId,
    falseClass: EClassId,
    twoValued: EClassId => Boolean,
    mergeFirst: Var => Boolean = _ => false // the equality atoms a decision makes true first
) extends Theory:
  /** Atoms asserted so far, with the level marks for `pop`; `atoms` may grow
   *  between solves, so these grow with it.
   */
  private val assigned = ArrayBuffer.empty[Boolean]
  private val assignedTrail = ArrayBuffer.empty[Var]
  private val marks = ArrayBuffer.empty[Int]

  /** For each atom implied false, the disequality that implied it: its side in
   *  `t`'s class, its side in `u`'s class, and its reason.
   */
  private val impliedBy = ArrayBuffer.empty[(EClassId, EClassId, Int) | Null]

  /** The atoms of each id, as either of their sides. */
  private val atomsAt = ArrayBuffer.empty[ArrayBuffer[Var] | Null]

  /** The atoms to look at whatever the e-graph says: the new ones, and the ones
   *  a pop made unassigned, whose implication may have outlived their
   *  assignment.
   */
  private val again = ArrayBuffer.empty[Var]

  /** The atoms a propagation looks at, each once (see [[propagate]]): the stamp
   *  of the last propagation to take each, and the ones taken.
   */
  private var seenAt = new Array[Int](0)
  private var stamp = 0
  private var candidates = new Array[Int](0)

  /** What the last propagation implied: the search does not take all of it when
   *  it finds a conflict.
   */
  private var lastImplied = ArrayBuffer.empty[Lit]

  private def grown(): Unit =
    while assigned.length < atoms.length do
      val v = assigned.length
      assigned += false
      impliedBy += null
      val atom = atoms(v)
      if atom != null then
        val (t, u) = atom
        watch(t, v)
        watch(u, v)
        again += v

  private def watch(id: EClassId, v: Var): Unit =
    while atomsAt.length <= id do atomsAt += null
    if atomsAt(id) == null then atomsAt(id) = ArrayBuffer.empty
    atomsAt(id).nn += v

  private def lits(reasons: ArrayBuffer[Int]): ArrayBuffer[Lit] = reasons.map(Lit.fromIndex)

  /** Whether anything reached the e-graph since the last scan of the atoms: a
   *  decision that concerns no atom costs nothing.
   */
  private var touched = true

  def assertLit(lit: Lit): Unit =
    grown()
    val v = lit.variable
    val atom = if v < atoms.length then atoms(v) else null
    if atom != null then
      touched = true
      val (t, u) = atom
      if lit.positive then eg.merge(t, u, lit.index)
      else if u == trueClass && twoValued(t) then eg.merge(t, falseClass, lit.index)
      else eg.disequate(t, u, lit.index)
      assigned(v) = true
      assignedTrail += v

  /** Atoms scanned for implied equalities and disequalities, for a budget. */
  var atomScans = 0L

  def propagate(): Theory.Result =
    grown()
    if !touched then return Theory.ok
    eg.touchedLimit = atoms.length // listing more ids than there are atoms costs more than looking at them all
    eg.rebuild()
    eg.conflict match
      case Some(reasons) => Theory.Result.Conflict(lits(reasons))
      case None =>
        touched = false
        val implied = ArrayBuffer.empty[Lit]
        def look(v: Var): Unit =
          atomScans += 1
          val atom = atoms(v)
          if atom != null && !assigned(v) then
            val (t, u) = atom
            if eg.find(t) == eg.find(u) then implied += Lit(v)
            else
              eg.disequality(t, u) match
                case Some(diseq) =>
                  impliedBy(v) = diseq
                  implied += Lit(v, false)
                case None => ()
        // Only the atoms of what changed: looking at every atom at every propagation was most of the time of
        // the large unrollings of a verification condition, where most of them never change. In order of
        // variable, as such a walk gave them.
        val ids = eg.takeTouched()
        if ids == null then
          var v = 0
          while v < atoms.length do
            look(v)
            v += 1
        else
          // Each atom once, in order of variable: an id of a class many terms meet lists its atoms with every
          // other's, and sorting the list with its repeats was most of the search on arrays read at many
          // indices, whose reads the theory combination pairs (`Encoder.shareIntegers`).
          if seenAt.length < atoms.length then
            seenAt = java.util.Arrays.copyOf(seenAt, math.max(atoms.length, 2 * seenAt.length))
          if candidates.length < atoms.length then
            candidates = new Array[Int](math.max(atoms.length, 2 * candidates.length))
          stamp += 1
          var n = 0
          def take(v: Var): Unit =
            if seenAt(v) != stamp then
              seenAt(v) = stamp
              candidates(n) = v
              n += 1
          var i = 0
          while i < again.length do
            take(again(i))
            i += 1
          i = 0
          while i < ids.length do
            val id = ids(i)
            if id < atomsAt.length then
              val at = atomsAt(id)
              if at != null then
                var k = 0
                while k < at.length do
                  take(at(k))
                  k += 1
            i += 1
          java.util.Arrays.sort(candidates, 0, n)
          i = 0
          while i < n do
            look(candidates(i))
            i += 1
          ids.clear()
        again.clear()
        lastImplied = implied
        Theory.Result.Ok(implied)

  override def finalCheck(): Theory.Result = propagate() match
    case Theory.Result.Ok(implied) if implied.isEmpty =>
      eg.finalCheck() match
        case Some(reasons) => Theory.Result.Conflict(lits(reasons))
        case None => Theory.ok
    case other => other

  override def firmPhase(v: Var): Option[Boolean] = if mergeFirst(v) then Some(true) else None

  def explain(lit: Lit): ArrayBuffer[Lit] =
    val (t, u) = atoms(lit.variable).nn
    if lit.positive then lits(eg.explain(t, u))
    else
      val (s, s2, reason) = impliedBy(lit.variable).nn
      lits(eg.explain(t, s) ++= eg.explain(u, s2) += reason)

  def push(): Unit =
    eg.push()
    marks += assignedTrail.length

  def pop(): Unit =
    touched = true // undone merges: atoms may need re-implying
    eg.pop()
    val mark = marks.remove(marks.length - 1)
    while assignedTrail.length > mark do
      val v = assignedTrail.remove(assignedTrail.length - 1)
      assigned(v) = false
      again += v
    for l <- lastImplied do again += l.variable
    lastImplied = ArrayBuffer.empty
