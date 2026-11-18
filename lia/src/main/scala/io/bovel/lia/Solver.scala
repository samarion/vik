package io.bovel.lia

import scala.collection.mutable.{ArrayBuffer, HashMap, HashSet}
import scala.util.boundary
import scala.util.boundary.break

/** A variable of the [[Solver]]: an index in `0 until numVars`. */
type Var = Int

object Solver:
  enum Result:
    case Sat

    /** [[Solver.check]] was told to stop (see its `keepGoing`). */
    case Unknown

    /** No solution: the bounds asserted with these reasons are inconsistent by
     *  themselves.
     */
    case Unsat(reasons: Set[Int])

    /** [[Solver.check]] leaves a branch to the client (see
     *  [[Solver.splitOnDemand]]): no answer yet; assert `x ≤ c` or `x ≥ c + 1`
     *  and check again.
     */
    case Split(x: Var, c: BigInt)

  /** A bound on a variable: its value (an integer) and why it holds: the reason
   *  it was asserted with, or the bounds it was derived from (`premises`, see
   *  `propagateBounds`). The reasons of a derived bound, the union of those of
   *  its premises, are collected only when a conflict needs them: derivations
   *  are many, conflicts few. With [[Solver.proofs]], `certificate` derives the
   *  bound (see [[Certificate]]).
   */
  /** A count shared by the bounds of one solver: see [[Solver.reasonWork]]. */
  private final class Counter:
    var n = 0L

  private final class Bound(
      val value: Delta,
      val reason: Int,
      val premises: Array[Bound],
      work: Counter,
      val certificate: Certificate | Null = null
  ):
    lazy val reasons: Set[Int] = // once per bound: a conflict may ask again and again along a long derivation
      val literals = Set.newBuilder[Int]
      val seen = scala.collection.mutable.HashSet.empty[Bound] // premises are shared: a graph, not a tree
      val todo = ArrayBuffer(this)
      while todo.nonEmpty do
        val bound = todo.remove(todo.length - 1)
        work.n += 1 + bound.premises.length
        if seen.add(bound) then
          if bound.premises.isEmpty then literals += bound.reason
          else todo ++= bound.premises
      literals.result()

  /** A bound replaced inside a level: the variable, the side, the old bound. */
  private final case class Undo(x: Var, isUpper: Boolean, old: Bound | Null)

  /** An open branch of branch and bound on `x`: its two bounds, its reason, and
   *  the explanation of its failed left side once on the right side.
   */
  private final case class Branch(
      x: Var,
      floor: BigInt,
      ceil: BigInt,
      reason: Int,
      because: Set[Int], // the reasons of the disequality the branch decides, if any: part of its explanation
      var left: Set[Int] | Null = null,
      var leftCertificate: Certificate | Null = null,
      strict: Boolean = false, // a real disequality splits into strict sides
      up: Boolean = false // the upper side `x ≥ ceil` first, toward zero
  )

  /** How many 64-bit words of coefficients [[Solver.integerEquations]] may go
   *  over: the check is an aid, not an obligation.
   */
  val equationWork = 100000

  /** An integer equation `Σ coefs = constant` of [[Solver.integerEquations]],
   *  with the reasons of the bounds it was combined from, and with
   *  [[Solver.proofs]], the factors of the equations `x = c` of the variables
   *  the bounds fix that it is the combination of (the rows are identities over
   *  the unknowns, and the definitions of fresh variables a change of
   *  variables).
   */
  private final class Equation(
      val coefs: HashMap[Int, BigInt],
      var constant: BigInt,
      var reasons: Set[Int],
      val factors: HashMap[Var, Rational] | Null = null
  )

  /** A set of variables with its smallest at hand: a binary min-heap. */
  private final class VarHeap:
    private var heap = new Array[Int](16)
    private var count = 0
    private var present = new Array[Boolean](16)

    def nonEmpty: Boolean = count > 0
    def isEmpty: Boolean = count == 0
    def min: Var = heap(0)

    def +=(x: Var): Unit =
      if x >= present.length then present = java.util.Arrays.copyOf(present, math.max(x + 1, 2 * present.length))
      if !present(x) then
        present(x) = true
        if count == heap.length then heap = java.util.Arrays.copyOf(heap, 2 * count)
        var i = count
        count += 1
        while i > 0 && heap((i - 1) / 2) > x do
          heap(i) = heap((i - 1) / 2)
          i = (i - 1) / 2
        heap(i) = x

    def removeMin(): Unit =
      present(heap(0)) = false
      count -= 1
      val x = heap(count)
      var i = 0
      var moving = true
      while moving do
        var c = 2 * i + 1
        if c + 1 < count && heap(c + 1) < heap(c) then c += 1
        if c < count && heap(c) < x then
          heap(i) = heap(c)
          i = c
        else moving = false
      heap(i) = x

  /** A row of the tableau: the non-basic variables it mentions, in increasing
   *  order, with their coefficients — parallel arrays, so that a variable is
   *  found by a binary search and a row is walked by index, with no boxing of
   *  the variables and no hash nodes. Rows are short (a dozen entries on the
   *  evaluation's instances) over hundreds of variables, so a sparse row over a
   *  dense one, and a shift on insertion over a merge. `slots(i)` is where the
   *  row's owner sits in the column of `vars(i)`, so that leaving the column
   *  costs nothing (see [[Column]]).
   */
  private final class Row(capacity: Int = 4):
    var vars: Array[Var] = new Array[Var](capacity)
    var coefs: Array[Rational] = new Array[Rational](capacity)
    var slots: Array[Int] = new Array[Int](capacity)
    var size: Int = 0
    def varAt(i: Int): Var = vars(i)
    def coefAt(i: Int): Rational = coefs(i)

    /** The index of `x`, or the insertion point as `-(i + 1)`. */
    def indexOf(x: Var): Int = java.util.Arrays.binarySearch(vars, 0, size, x)
    def apply(x: Var): Rational = coefs(indexOf(x))
    def existsVar(p: Var => Boolean): Boolean =
      var i = 0
      while i < size do
        if p(vars(i)) then return true
        i += 1
      false
    def insertAt(i: Int, x: Var, c: Rational): Unit =
      if size == vars.length then
        vars = java.util.Arrays.copyOf(vars, 2 * size)
        coefs = java.util.Arrays.copyOf(coefs, 2 * size)
        slots = java.util.Arrays.copyOf(slots, 2 * size)
      System.arraycopy(vars, i, vars, i + 1, size - i)
      System.arraycopy(coefs, i, coefs, i + 1, size - i)
      System.arraycopy(slots, i, slots, i + 1, size - i)
      vars(i) = x
      coefs(i) = c
      size += 1
    def removeAt(i: Int): Rational =
      val c = coefs(i)
      System.arraycopy(vars, i + 1, vars, i, size - i - 1)
      System.arraycopy(coefs, i + 1, coefs, i, size - i - 1)
      System.arraycopy(slots, i + 1, slots, i, size - i - 1)
      size -= 1
      coefs(size) = null.asInstanceOf[Rational] // no reference kept
      c

  /** The basic variables whose rows mention a variable, in no order: an array
   *  grown by doubling. An owner leaves by the last one taking its slot
   *  ([[Solver.leave]]), which its row is told of: no search, no hash set, no
   *  boxing — on a wide bit-vector instance a column runs to hundreds of owners
   *  and a pivot empties dozens of them.
   */
  private final class Column:
    var owners: Array[Var] = new Array[Var](4)
    var size: Int = 0
    def apply(i: Int): Var = owners(i)

    /** Adds `b` and returns its slot. */
    def add(b: Var): Int =
      if size == owners.length then owners = java.util.Arrays.copyOf(owners, 2 * size)
      owners(size) = b
      size += 1
      size - 1
    def clear(): Unit = size = 0

    /** A copy, for a walk that changes the column. */
    def snapshot: Array[Var] = java.util.Arrays.copyOf(owners, size)

/** A solver for conjunctions of bounds on integer linear expressions
 *  (quantifier-free linear integer arithmetic), after Dutertre and de Moura, "A
 *  Fast Linear-Arithmetic Solver for DPLL(T)" (CAV 2006): a general simplex
 *  over the rationals whose tableau is set up once and never backtracked, with
 *  bounds as the only assertions (the only state that [[pop]] undoes), then
 *  branch and bound for integrality.
 *
 *  A variable is either an integer unknown ([[newVar]]) or stands for a linear
 *  expression over earlier variables ([[newSlack]]), integer-valued as well.
 *  Bounds are asserted with an `Int` reason (for a CDCL(T) solver, a literal)
 *  and are tightened to integers, which for an expression means dividing by the
 *  gcd of its coefficients (`2x + 2y ≤ 3` gives `x + y ≤ 1`); an
 *  [[Solver.Result.Unsat]] names the reasons of some bounds that are
 *  inconsistent by themselves.
 *
 *  Invariants between calls:
 *    - each row holds: the value of its basic variable is the row's combination
 *      of the values of the non-basic variables it mentions, and rows mention
 *      non-basic variables only;
 *    - every non-basic variable is within its bounds (asserting a bound on one
 *      moves its value, popping only loosens bounds), so only basic variables
 *      can violate their bounds, which [[check]] repairs by pivoting;
 *    - after a [[check]] returning `Sat`, every variable is within its bounds
 *      and every value is an integer: [[value]] is a solution.
 */
final class Solver:
  import Solver.*

  private val lower = ArrayBuffer.empty[Bound | Null]
  private val upper = ArrayBuffer.empty[Bound | Null]
  private val values = ArrayBuffer.empty[Rational]

  /** The infinitesimal parts of the assignment, touched only when a real
   *  variable exists ([[anyReal]]): a pure-integer problem pays for exactly one
   *  rational per variable.
   */
  private val valuesD = ArrayBuffer.empty[Rational]
  private var anyReal = false

  /** The row of each basic variable (`null` for a non-basic one): the
   *  coefficients of the non-basic variables whose combination it equals.
   */
  private val rows = ArrayBuffer.empty[Row | Null]

  /** For each variable, the basic variables whose rows mention it. */
  private val columns = ArrayBuffer.empty[Column]

  /** Every basic variable violating a bound, and possibly others that no longer
   *  do: whatever moves a value or tightens a bound offers the variable through
   *  [[suspect]], so [[simplex]] needs no scan of all the variables per pivot.
   */
  private val suspects = VarHeap()

  /** Whether the variable stands for an expression, and then the gcd of the
   *  expression's coefficients: the variable holds the expression divided by
   *  it, so that its bounds can be tightened to integers.
   */
  private val isSlack = ArrayBuffer.empty[Boolean]
  private val scale = ArrayBuffer.empty[BigInt]

  /** Whether the variable is integer-valued: branch and bound and the integer
   *  tightenings apply to it; a real variable is decided by the relaxation.
   */
  private val isInt = ArrayBuffer.empty[Boolean]
  private var anyInt = false

  def isInteger(x: Var): Boolean = isInt(x)

  private val trail = ArrayBuffer.empty[Undo]
  private val levels = ArrayBuffer.empty[(Int, Int)] // the lengths of `trail` and `distinct` at each push

  /** Variables whose bounds tightened since the last bound propagation. */
  private val tightened = ArrayBuffer.empty[Var]

  /** The values variables must not take, with the reasons (see
   *  [[assertDistinct]]).
   */
  private val distinct = ArrayBuffer.empty[(Var, BigInt, Int)] // in the caller's units (see `scale`)

  /** Reasons of the branches of the current branch and bound search: negative
   *  (never a caller's), and removed from the explanations they contribute to.
   */
  private var branches = 0

  def numVars: Int = values.length

  /** Whether the solver gives a [[Certificate]] of each `Unsat`
   *  ([[conflictCertificate]]); set before asserting anything.
   */
  var proofs: Boolean = false

  /** With [[proofs]], the certificate of the last `Unsat`. */
  var conflictCertificate: Certificate | Null = null

  /** The expression of each slack (see [[newSlack]]), `null` for an unknown. */
  private val definitions = ArrayBuffer.empty[Array[(BigInt, Var)] | Null]

  /** The expression `x` stands for, over the unknowns ([[newVar]]): `x` itself
   *  for an unknown.
   */
  def form(x: Var): Map[Var, Rational] =
    val d = definitions(x)
    if d == null then Map(x -> Rational.one)
    else
      val out = HashMap.empty[Var, Rational]
      for (a, y) <- d; (u, b) <- form(y) do
        val sum = out.getOrElse(u, Rational.zero) + b * Rational(a)
        if sum.isZero then out.remove(u) else out(u) = sum
      out.toMap

  /** An `Unsat` with its certificate, when proofs are on. */
  private def unsat(reasons: Set[Int], certificate: => Certificate): Result =
    if proofs then conflictCertificate = certificate
    Result.Unsat(reasons)

  /** The combination of the certificates of `bounds` with the given factors
   *  (those that are zero left out).
   */
  private def comb(factors: Array[Rational], bounds: Array[Certificate]): Certificate =
    val keep = factors.indices.filter(i => !factors(i).isZero)
    Certificate.Comb(keep.map(factors(_)).toArray, keep.map(bounds(_)).toArray)

  /** A new variable, unbounded, non-basic, valued 0; integer unless said
   *  otherwise.
   */
  def newVar(integer: Boolean = true): Var =
    lower += null
    upper += null
    values += Rational.zero
    valuesD += Rational.zero
    rows += null
    columns += Column()
    isSlack += false
    definitions += null
    scale += 1
    isInt += integer
    if integer then anyInt = true else anyReal = true
    values.length - 1

  /** A new variable standing for `Σ coefficient × variable` over `terms`
   *  (non-empty, integer coefficients, non-zero): basic, with the expression
   *  substituted by the rows of the basic variables it mentions.
   */
  def newSlack(terms: Iterable[(BigInt, Var)], integer: Boolean = true): Var =
    require(terms.nonEmpty, "empty expression")
    require(terms.forall((a, _) => a.signum != 0), "zero coefficient")
    val g = if integer then terms.map((a, _) => a.abs).reduce(_ gcd _) else BigInt(1)
    val s = newVar(integer)
    isSlack(s) = true
    definitions(s) = terms.toArray
    scale(s) = g
    val row = Row()
    for (a, x) <- terms do
      val c = Rational(a / g)
      val r = rows(x)
      if r == null then add(s, row, x, c)
      else
        var i = 0
        while i < r.size do
          add(s, row, r.varAt(i), c * r.coefAt(i))
          i += 1
    tableau += 1
    rows(s) = row
    var v = Rational.zero
    var vD = Rational.zero
    var i = 0
    while i < row.size do
      v = v + values(row.varAt(i)) * row.coefAt(i)
      if anyReal then vD = vD + valuesD(row.varAt(i)) * row.coefAt(i)
      i += 1
    values(s) = v
    if anyReal then valuesD(s) = vD
    s

  /** Adds `c × x` to the row of `owner`, keeping `columns` up to date. */
  private def add(owner: Var, row: Row, x: Var, c: Rational): Unit =
    entries += 1
    val i = row.indexOf(x)
    if i < 0 then
      if !c.isZero then
        row.insertAt(-i - 1, x, c)
        row.slots(-i - 1) = columns(x).add(owner)
    else
      val e = row.coefAt(i) + c
      if e.isZero then
        leave(x, row.slots(i))
        row.removeAt(i)
      else row.coefs(i) = e

  /** Empties slot `slot` of the column of `x`: the last owner moves in, and its
   *  row learns the new slot.
   */
  private def leave(x: Var, slot: Int): Unit =
    val column = columns(x)
    column.size -= 1
    if slot < column.size then
      val moved = column.owners(column.size)
      column.owners(slot) = moved
      val row = rows(moved).nn
      row.slots(row.indexOf(x)) = slot

  /** The value of `x` (of the expression it stands for): a solution after a
   *  `Sat` [[check]].
   */
  def value(x: Var): BigInt = (values(x) * Rational(scale(x))).floor

  /** The value of a real variable, the infinitesimal resolved: after a `Sat`
   *  [[check]], a concrete positive δ small enough for every bound exists, and
   *  this is the value at it.
   */
  def realValue(x: Var): Rational = values(x) + (if anyReal then valuesD(x) else Rational.zero) * delta0()

  /** A δ that satisfies every asserted bound strictly enough: for each bound
   *  whose infinitesimal part demands room, the rational gap divided by the
   *  infinitesimal gap bounds δ from above; 1 works when nothing does.
   */
  private def delta0(): Rational =
    var best = Rational.one
    var x = 0
    while x < numVars do
      val vr = values(x)
      val vd = if anyReal then valuesD(x) else Rational.zero
      val l = lower(x)
      val u = upper(x)
      if l != null && l.value.d > vd && l.value.r < vr then
        val candidate = (vr - l.value.r) / (l.value.d - vd)
        if candidate < best then best = candidate
      if u != null && u.value.d < vd && u.value.r > vr then
        val candidate = (u.value.r - vr) / (vd - u.value.d)
        if candidate < best then best = candidate
      x += 1
    best

  /** Asserts `x ≤ c` for `reason` (on the expression `x` stands for): `Unsat`
   *  if it contradicts the lower bound of `x`, `Sat` otherwise, which leaves
   *  the feasibility of the whole to [[check]].
   */
  def assertUpper(x: Var, c: BigInt, reason: Int): Result = assertUpper(x, c, false, reason)

  /** Asserts `x ≤ c`, or `x < c` when `strict` — which for an integer variable
   *  is `x ≤ c − 1`, and for a real one an inclusive bound at `c − δ`.
   */
  def assertUpper(x: Var, c: BigInt, strict: Boolean, reason: Int): Result =
    val value =
      if isInt(x) then Delta(Rational(floorDiv(if strict then c - 1 else c, scale(x))))
      else if strict then Delta.strictUpper(Rational(c))
      else Delta(Rational(c))
    assertBound(
      x,
      Bound(value, reason, Array.empty, reasons, if proofs then hyp(reason, x, c, strict, true) else null),
      true
    )

  /** Asserts `x ≥ c` for `reason`, as [[assertUpper]]. */
  def assertLower(x: Var, c: BigInt, reason: Int): Result = assertLower(x, c, false, reason)

  /** Asserts `x ≥ c`, or `x > c` when `strict`, as [[assertUpper]]. */
  def assertLower(x: Var, c: BigInt, strict: Boolean, reason: Int): Result =
    val value =
      if isInt(x) then Delta(Rational(-floorDiv(-(if strict then c + 1 else c), scale(x))))
      else if strict then Delta.strictLower(Rational(c))
      else Delta(Rational(c))
    assertBound(
      x,
      Bound(value, reason, Array.empty, reasons, if proofs then hyp(reason, x, c, strict, false) else null),
      false
    )

  /** The certificate of an asserted bound: the hypothesis, on the expression
   *  `x` stands for, divided by its gcd (the bound is on `x`), and rounded when
   *  `x` is an integer.
   */
  private def hyp(reason: Int, x: Var, c: BigInt, strict: Boolean, upper: Boolean): Certificate =
    val h = Certificate.Hyp(reason, x, c, strict, upper)
    val scaled = if scale(x) == 1 then h else Certificate.Comb(Array(Rational(1, scale(x))), Array(h))
    if isInt(x) then Certificate.Round(scaled) else scaled

  /** Asserts `x ≠ c` (for a slack, that its combination is not `c`): a
   *  disequality is decided by [[check]], which branches on `x ≤ c − 1` or
   *  `x ≥ c + 1` when the assignment violates it; it fails at once only against
   *  bounds fixing `x` to `c`.
   */
  def assertDistinct(x: Var, c: BigInt, reason: Int): Result =
    if isInt(x) && c.mod(scale(x)) != 0 then
      Result.Sat // a combination never takes a value its gcd does not divide
    else
      val v = Delta(Rational(c / (if isInt(x) then scale(x) else BigInt(1))))
      val l = lower(x)
      val u = upper(x)
      if l != null && u != null && l.value == v && u.value == v then
        unsat(
          l.reasons ++ u.reasons + reason, {
            // A split of the disequality, each side against one of the bounds.
            val s = if isInt(x) then scale(x) else BigInt(1)
            val strict = !isInt(x)
            val (floor, ceil) = if strict then (c, c) else (c - s, c + s)
            branches += 1
            val r = -branches
            def side(bound: Bound, upper: Boolean, at: BigInt) = Certificate.Comb(
              Array(Rational.one, Rational(scale(x))),
              Array(Certificate.Hyp(r, x, at, strict, upper), bound.certificate.nn)
            )
            Certificate.Split(r, x, floor, ceil, side(l, true, floor), side(u, false, ceil), reason, c, strict)
          }
        )
      else
        distinct += ((x, c, reason))
        Result.Sat

  private def floorDiv(a: BigInt, b: BigInt): BigInt = (a - a.mod(b)) / b

  /** Whether the bounds asserted so far already decide `x ≤ c`, with the
   *  reasons: `Some((true, ...))` when they force it, `Some((false, ...))` when
   *  they forbid it, `None` when both remain possible. For the theory
   *  propagation of a bound atom (see `smt.LiaTheory`).
   */
  def decidesUpper(x: Var, c: BigInt): Option[(Boolean, Set[Int])] =
    val value = Delta(Rational(floorDiv(c, scale(x))))
    val u = upper(x)
    val l = lower(x)
    if u != null && u.value <= value then Some((true, u.reasons))
    else if l != null && l.value > value then Some((false, l.reasons))
    else None

  private def assertBound(x: Var, bound: Bound, isUpper: Boolean): Result =
    val c = bound.value
    val same = if isUpper then upper(x) else lower(x)
    val opposite = if isUpper then lower(x) else upper(x)
    if same != null && (if isUpper then same.value <= c else same.value >= c) then return Result.Sat // not tighter
    if opposite != null && (if isUpper then c < opposite.value else c > opposite.value) then
      return unsat(bound.reasons ++ opposite.reasons, pair(bound, opposite.nn))
    if levels.nonEmpty then trail += Undo(x, isUpper, same)
    if isUpper then upper(x) = bound else lower(x) = bound
    boundMagnitude = boundMagnitude.max(c.r.num.abs)
    moved += x
    if rows(x) == null && (if isUpper then compareValue(x, c) > 0 else compareValue(x, c) < 0) then update(x, c)
    suspect(x)
    tightened += x
    Result.Sat

  /** The certificate of two opposite bounds of a variable that cross. */
  private def pair(a: Bound, b: Bound): Certificate =
    Certificate.Comb(Array(Rational.one, Rational.one), Array(a.certificate.nn, b.certificate.nn))

  /** The certificate of the bound or its opposite on `x` that decides `x ≤ c`
   *  (see [[decidesUpper]]) against the hypothesis that it does not: `reason`,
   *  `x > c` when `holds`, `x ≤ c` otherwise.
   */
  def decidedCertificate(x: Var, c: BigInt, holds: Boolean, reason: Int): Certificate =
    val bound = (if holds then upper(x) else lower(x)).nn
    Certificate.Comb(
      Array(Rational(scale(x)), Rational.one),
      Array(bound.certificate.nn, Certificate.Hyp(reason, x, c, holds, !holds))
    )

  /** Derives bounds from the rows, as Dutertre and de Moura's bound
   *  propagation: the bounds of the variables of a row bound its basic
   *  variable, and the bound of the basic variable with the bounds of the other
   *  variables bound each variable of the row, all rounded to integers. Only
   *  the rows mentioning a variable whose bound tightened since the last
   *  propagation are visited, the derived bounds queueing their rows in turn, a
   *  bounded number of times per variable, since a cyclic system can tighten
   *  forever; the simplex decides the rest. The premises of a derived bound are
   *  every bound used (for a variable of the row, its own bound is included as
   *  well: simpler, and still sound).
   */
  private def propagateBounds(): Result = boundary:
    // Each row is propagated once per call. The mark of the call says which, in an array kept between
    // calls: allocating and zeroing one per variable at every call was a fifth of the time of a script
    // that checks often over a problem that stays (bench/results/lia).
    visitedIn = growVisited(visitedIn)
    visitMark += 1
    var i = 0
    while i < tightened.length do
      val x = tightened(i)
      i += 1
      // The rows mentioning `x`: those of the basic variables of its column, and its own if it is basic.
      val column = columns(x)
      var k = if rows(x) == null then 0 else -1 // -1: its own row first
      while k < column.size do
        val b = if k < 0 then x else column(k)
        k += 1
        if visitedIn(b) != visitMark then
          visitedIn(b) = visitMark
          if !keepGoing() then
            tightened.clear()
            break(Result.Unknown)
          propagateRow(b) match
            case Result.Sat => ()
            case unsat =>
              tightened.clear()
              break(unsat)
    tightened.clear()
    Result.Sat

  private var moved = ArrayBuffer.empty[Var]
  private var movedSpare = ArrayBuffer.empty[Var]

  /** The variables whose bounds have been written since this was last called: a
   *  bound asserted, derived, or undone by a pop. A client that watches the
   *  bounds — the theory looking for the atoms they decide — takes them instead
   *  of walking every variable at every call.
   *
   *  Taking them empties the list, so there is one such client: a second would
   *  find what the first had already taken, or nothing. The two lists are
   *  swapped and reused, so a call allocates nothing, and the list handed out
   *  stays the caller's until the call after next.
   */
  def takeMoved(): ArrayBuffer[Var] =
    val taken = moved
    moved = movedSpare
    movedSpare = taken
    moved.clear()
    taken

  /** The call of [[propagateBounds]] each row was last propagated in, and that
   *  call's mark: a row is propagated once per call, and the array outlives the
   *  call so that no call pays for the variables it never looks at.
   */
  private var visitedIn = new Array[Int](0)
  private var visitMark = 0

  private def growVisited(a: Array[Int]): Array[Int] =
    if a.length >= numVars then a else java.util.Arrays.copyOf(a, math.max(8, 2 * numVars))

  /** Derives the bounds the row of `b` implies (see [[propagateBounds]]). */
  private def propagateRow(b: Var): Result = boundary:
    val row = rows(b).nn
    entries += row.size
    // Whether every variable has the bound needed for the lowest and for the highest value of the row: a row
    // with neither derives nothing, and most rows are such, so finding that out does no arithmetic.
    var hasLow = true
    var hasHigh = true
    var i = 0
    while i < row.size do
      val j = row.varAt(i)
      val positive = row.coefAt(i).signum > 0
      val forLow = if positive then lower(j) else upper(j)
      val forHigh = if positive then upper(j) else lower(j)
      if forLow == null then hasLow = false
      if forHigh == null then hasHigh = false
      if !hasLow && !hasHigh then break(Result.Sat)
      i += 1
    // The lowest and highest values of the row given the bounds.
    var low = Delta.zero
    var high = Delta.zero
    i = 0
    while i < row.size do
      val j = row.varAt(i)
      val a = row.coefAt(i)
      if hasLow then low = low + (if a.signum > 0 then lower(j) else upper(j)).nn.value * a
      if hasHigh then high = high + (if a.signum > 0 then upper(j) else lower(j)).nn.value * a
      i += 1
    // The bounds behind `low` or `high`, plus `extra`. Most visits derive nothing, so only those that do build this.
    def premises(forLowest: Boolean, extra: Bound | Null): Array[Bound] =
      val out = new Array[Bound](if extra == null then row.size else row.size + 1)
      var k = 0
      while k < row.size do
        val j = row.varAt(k)
        out(k) = (if (row.coefAt(k).signum > 0) == forLowest then lower(j) else upper(j)).nn
        k += 1
      if extra != null then out(row.size) = extra
      out
    // The factors of the premises for a bound of `b`, then for one of the `j`-th variable (see `premises`): the
    // absolute coefficients of the row, the variable's own bound left out, the bound of `b` last, all divided by
    // the variable's coefficient.
    def factors(j: Int): Array[Rational] =
      val n = if j < 0 then row.size else row.size + 1
      val out = new Array[Rational](n)
      val by = if j < 0 then Rational.one else row.coefAt(j).abs
      var k = 0
      while k < row.size do
        out(k) = if k == j then Rational.zero else row.coefAt(k).abs / by
        k += 1
      if j >= 0 then out(row.size) = Rational.one / by
      out
    def derive(x: Var, c: Delta, premises: Array[Bound], isUpper: Boolean, j: Int): Unit =
      val rounded = if isInt(x) then Delta(Rational(if isUpper then c.floor else c.ceil)) else c
      val certificate =
        if !proofs then null
        else
          val combined = comb(factors(j), premises.map(_.certificate.nn))
          if isInt(x) then Certificate.Round(combined) else combined
      assertBound(x, Bound(rounded, -1, premises, reasons, certificate), isUpper) match
        case Result.Sat => ()
        case unsat => break(unsat)
    if hasLow && (lower(b) == null || low > lower(b).nn.value) then derive(b, low, premises(true, null), false, -1)
    if hasHigh && (upper(b) == null || high < upper(b).nn.value) then derive(b, high, premises(false, null), true, -1)
    // a × x_j = b − (the rest of the row), bounded by a bound of b and the lowest or highest value of the rest.
    val u = upper(b)
    val l = lower(b)
    val upperRoom = if u != null && hasLow then u.value - low else null
    val lowerRoom = if l != null && hasHigh then high - l.value else null
    if upperRoom == null && lowerRoom == null then break(Result.Sat)
    // Taken together before the first derivation, which changes the bounds they read.
    var withUpper: Array[Bound] | Null = null
    var withLower: Array[Bound] | Null = null
    i = 0
    while i < row.size do
      val j = row.varAt(i)
      val a = row.coefAt(i)
      val forLow = if a.signum > 0 then lower(j) else upper(j)
      val forHigh = if a.signum > 0 then upper(j) else lower(j)
      // What x_j can move the row by: with no more room than that, a bound of b says something of x_j. Most
      // variables of a row over bits have less, so most of the divisions below need not happen.
      val moves = if forLow != null && forHigh != null then (forHigh.value - forLow.value) * a else null
      val fromUpper = upperRoom != null && (moves == null || upperRoom < moves)
      val fromLower = lowerRoom != null && (moves == null || lowerRoom < moves)
      if (fromUpper || fromLower) && withUpper == null && withLower == null then
        if upperRoom != null then withUpper = premises(true, u)
        if lowerRoom != null then withLower = premises(false, l)
      // a × x_j ≤ u − (low − a × forLow), and a × x_j ≥ l − (high − a × forHigh)
      if fromUpper then derive(j, (upperRoom.nn + forLow.nn.value * a) / a, withUpper.nn, a.signum > 0, i)
      if fromLower then derive(j, (forHigh.nn.value * a - lowerRoom.nn) / a, withLower.nn, a.signum < 0, i)
      i += 1
    Result.Sat

  /** Sets the non-basic `x` to `v`, updating the basic variables. */
  private def update(x: Var, v: Delta): Unit =
    val moved = v.r - values(x)
    val movedD = if anyReal then v.d - valuesD(x) else Rational.zero
    val column = columns(x)
    entries += column.size
    var i = 0
    while i < column.size do
      val b = column(i)
      val a = rows(b).nn(x)
      values(b) = values(b) + moved * a
      if anyReal then valuesD(b) = valuesD(b) + movedD * a
      suspect(b)
      i += 1
    values(x) = v.r
    if anyReal then valuesD(x) = v.d

  /** Sets the basic `b` to `v` by moving the non-basic `n` of its row, then
   *  makes `n` basic in its place (`PivotAndUpdate` in the paper).
   */
  private def pivotAndUpdate(b: Var, n: Var, v: Delta): Unit =
    val a = rows(b).nn(n)
    val theta = (v.r - values(b)) / a
    val thetaD = if anyReal then (v.d - valuesD(b)) / a else Rational.zero
    values(b) = v.r
    values(n) = values(n) + theta
    if anyReal then
      valuesD(b) = v.d
      valuesD(n) = valuesD(n) + thetaD
    val column = columns(n)
    entries += column.size
    var i = 0
    while i < column.size do
      val k = column(i)
      if k != b then
        val c = rows(k).nn(n)
        values(k) = values(k) + theta * c
        if anyReal then valuesD(k) = valuesD(k) + thetaD * c
        suspect(k)
      i += 1
    pivot(b, n)
    suspect(n)

  /** Swaps the basic `b` and the non-basic `n` of its row: solves the row for
   *  `n` and substitutes the result in the other rows mentioning `n`.
   */
  private def pivot(b: Var, n: Var): Unit =
    val rowB = rows(b).nn
    val a = rowB(n)
    tableau += 1
    rows(b) = null
    var i = 0
    while i < rowB.size do
      leave(rowB.varAt(i), rowB.slots(i))
      i += 1
    // n = (b - Σ_{j ≠ n} a_j x_j) / a
    val rowN = Row(rowB.size + 1)
    add(n, rowN, b, Rational.one / a)
    i = 0
    while i < rowB.size do
      val j = rowB.varAt(i)
      if j != n then add(n, rowN, j, -rowB.coefAt(i) / a)
      i += 1
    rows(n) = rowN
    val ks = columns(n).snapshot
    columns(n).clear() // `rowN` does not mention `n`: the substitutions below leave its column alone
    for k <- ks do
      val rowK = rows(k).nn
      val c = rowK.removeAt(rowK.indexOf(n))
      i = 0
      while i < rowN.size do
        add(k, rowK, rowN.varAt(i), c * rowN.coefAt(i))
        i += 1

  /** Decides the bounds: `Sat`, and [[value]] is an integer solution, or
   *  `Unsat` with its explanation. Bound propagation first tightens the bounds
   *  by the rows; the simplex (Bland's rule, so it terminates) then decides the
   *  rational relaxation; a fractional value is then split, depth first, into
   *  `x ≤ ⌊v⌋` or `x ≥ ⌈v⌉`, the side toward zero first, the explanations of
   *  two failed branches combining into one without the branch itself. The open
   *  branches are kept on an explicit stack (a recursion would grow with their
   *  number: thousands for a wide bit-vector lowered to an integer). Branch and
   *  bound may not terminate on unbounded variables.
   */
  /** Asked at every step — a pivot, a row propagation, a branch — whether to go
   *  on: a budget of steps (fuel), a deadline, ... `false` makes the check
   *  return `Unknown`.
   */
  var keepGoing: () => Boolean = () => true

  /** Splitting on demand (Barrett, Nieuwenhuis, Oliveras and Tinelli 2006): for
   *  a client that can decide a branch itself, as an atom of its own search.
   *  [[check]] then answers `Split(x, c)` for a split at its top that already
   *  failed on both sides once: the two refutations came back merged in one
   *  conflict, where the client's search cannot learn the short one alone, and
   *  meets the same split at its next check.
   */
  var splitOnDemand: Boolean = false
  private val failedSplits = HashSet.empty[(Var, BigInt)]

  /** Forgets the splits that failed, for a client starting another search over
   *  assertions it may have changed (`push`, `pop`): kept across the check-sats
   *  of a session, they steered the later ones into longer searches.
   */
  def forgetFailedSplits(): Unit = failedSplits.clear()

  /** The bounds visited, with their premises, collecting the reasons of derived
   *  bounds: the work of explaining, which a budget counts besides the steps
   *  (see [[keepGoing]]).
   */
  def reasonWork: Long = reasons.n
  private val reasons = Solver.Counter()

  /** The entries of the tableau read or written (by a pivot, an update of the
   *  basic values, a row propagation), the work of a step, for a budget.
   */
  def rowWork: Long = entries
  private var entries = 0L

  /** For the tests: pretend the small-model box is this many bits wide. */
  private[lia] var boxBitsOverride: Long = -1

  /** How many bits a solution needs at most, when every variable is an integer:
   *  a generous envelope of Papadimitriou's small-model bound (JACM 1981) — a
   *  feasible system of `m` constraints over `n` variables with entries of
   *  absolute value at most `a` has a solution with entries at most
   *  `n·(m·a)^(2m+1)`. The bound itself is astronomical and never computed; its
   *  bit length is enough to prune a branch against, and the pruning is what
   *  makes [[check]] a decision procedure for pure integers, fuel allowing: no
   *  solution lives past the box, so exhausting it is a sound unsat.
   */
  /** The version of the tableau: every row written bumps it, so a value read
   *  from the rows can say which tableau it was read from.
   */
  private var tableau = 0

  /** The largest constant of a bound ever asserted, in the solver's units. The
   *  box is computed from it rather than from the bounds in force: a bound
   *  asserted after the box was computed would otherwise leave the box too
   *  small, and a solution past it is pruned as none. It only grows, so the
   *  cache is keyed on it, and it moves rarely once a problem's constants have
   *  been seen.
   */
  private var boundMagnitude = BigInt(2)

  /** [[smallModelBoxBits]] of the tableau, variables and bound magnitude it was
   *  computed from: the box walks every row and multiplies its coefficients,
   *  which a check that pivots nothing would pay again for the same answer. A
   *  larger box is always sound, so its entries only ever grow: every variable
   *  counts for two bounds, whether or not it has them now.
   */
  private var boxBits = -1L
  private var boxBitsOf = -1
  private var boxBitsVars = -1
  private var boxBitsMagnitude = BigInt(-1)

  private def cachedBoxBits(): Long =
    if boxBitsOf != tableau || boxBitsVars != numVars || boxBitsMagnitude != boundMagnitude then
      boxBits = smallModelBoxBits()
      boxBitsOf = tableau
      boxBitsVars = numVars
      boxBitsMagnitude = boundMagnitude
    boxBits

  private def smallModelBoxBits(): Long =
    var a = BigInt(2)
    var m = 0
    var x = 0
    while x < numVars do
      val row = rows(x)
      if row != null then
        m += 1
        var l = BigInt(1)
        var i = 0
        while i < row.size do
          l = l / (l gcd row.coefAt(i).den) * row.coefAt(i).den
          i += 1
        i = 0
        while i < row.size do
          val c = row.coefAt(i)
          a = a.max((c.num * (l / c.den)).abs)
          i += 1
        a = a.max(l)
      x += 1
    m += 2 * numVars // a lower and an upper bound per variable, as many as there could be
    a = a.max(boundMagnitude)
    val size = BigInt(m + numVars + 2) * (a + 2)
    (2L * (m + numVars) + 6) * size.bitLength

  /** Every reason asserted, bounds and disequalities: the explanation when the
   *  small-model box took part in an unsat — the box argument is about the
   *  whole system, never a subset of it.
   */
  private def assertedReasons(): Set[Int] =
    val out = Set.newBuilder[Int]
    var x = 0
    while x < numVars do
      val l = lower(x)
      val u = upper(x)
      if l != null then out ++= l.reasons.filter(_ >= 0)
      if u != null then out ++= u.reasons.filter(_ >= 0)
      x += 1
    for (_, _, reason) <- distinct do out += reason
    out.result()

  /** Whether a check looks for an integer solution of the equations in force
   *  once branch and bound slides (see [[integerEquations]]).
   */
  private[lia] var equationCheck = true

  def check(): Result =
    val boxBits: Long =
      if anyReal then -1L
      else if boxBitsOverride >= 0 then boxBitsOverride
      else cachedBoxBits()
    var boxPruned = false
    def pastBox(c: BigInt): Boolean =
      val past = boxBits >= 0 && c.abs.bitLength > boxBits
      if past then boxPruned = true
      past
    val open = ArrayBuffer.empty[Branch]
    var equationsChecked = !equationCheck

    /** Decides the relaxation and splits on the first fractional unknown, or
     *  else on the first violated disequality.
     */
    def step(sweep: Boolean): Result | Branch = relaxationAndWindows() match
      case Result.Sat =>
        var x = 0
        while x < numVars && (isSlack(x) || !isInt(x) || deltaValue(x).isInteger) do x += 1
        // Inside a branch, what the rows say now before branching again (see `propagateRows`): the bounds it
        // finds go when the branch does. Outside of one they would stay after the check, and the search went
        // another, longer way for them on the sessions measured.
        val swept = if sweep && x < numVars then propagateRows() else Result.Sat
        if swept != Result.Sat then swept
        else if tightened.nonEmpty then step(false)
        else if x < numVars then
          // A second branch on an unknown is branch and bound sliding along it, maybe without end:
          // the equations alone may have no integer solution.
          val sliding = !equationsChecked && open.exists(_.x == x)
          val refuted = if sliding then integerEquations() else Result.Sat
          equationsChecked ||= sliding && refuted == Result.Sat // a refutation is found again on the other side
          if refuted != Result.Sat then refuted
          else
            branches += 1
            val v = deltaValue(x)
            // The side toward zero first: flooring a negative value first can dive
            // away from zero without end along an unbounded direction.
            Branch(x, v.floor, v.ceil, -branches, Set.empty, up = v.floor.signum < 0)
        else
          distinct.find((x, c, _) =>
            values(x) * Rational(if isInt(x) then scale(x) else BigInt(1)) == Rational(c)
              && (!anyReal || valuesD(x).isZero)
          ) match
            case Some((x, c, reason)) =>
              branches += 1
              if isInt(x) then Branch(x, c - scale(x), c + scale(x), -branches, Set(reason))
              else Branch(x, c, c, -branches, Set(reason), strict = true)
            case None => Result.Sat
      case unsat => unsat

    def relaxationAndWindows(): Result = checkRelaxation() match
      case Result.Sat => integerWindows()
      case unsat => unsat
    def side(branch: Branch, up: Boolean): Result | Branch =
      val c = if up then branch.ceil else branch.floor
      // No solution past the box; with proofs, which have no certificate for the box, the check gives up.
      if pastBox(c) then if proofs then Result.Unknown else Result.Unsat(Set.empty)
      else
        val asserted =
          if up then assertLower(branch.x, c, branch.strict, branch.reason)
          else assertUpper(branch.x, c, branch.strict, branch.reason)
        asserted match
          case Result.Sat => step(open.nonEmpty)
          case unsat => unsat
    var current: Result | Branch = step(false)
    while true do
      current match
        case Result.Sat =>
          for _ <- open do pop() // the assignment stays valid: bounds only loosen
          return Result.Sat
        case Result.Unknown =>
          for _ <- open do pop()
          return Result.Unknown
        case Result.Split(_, _) => throw AssertionError("a split is returned, never a step")
        case Result.Unsat(reasons) if open.isEmpty =>
          return Result.Unsat(if boxPruned then assertedReasons() else reasons)
        case Result.Unsat(reasons) =>
          val branch = open.last
          pop()
          if branch.left == null then // the left side failed: try the right one
            branch.left = reasons
            if proofs then branch.leftCertificate = conflictCertificate
            push()
            current = side(branch, !branch.up)
          else // both sides failed
            open.remove(open.length - 1)
            if open.isEmpty && splitOnDemand && branch.because.isEmpty then failedSplits += ((branch.x, branch.floor))
            current = unsat(
              (branch.left.nn ++ reasons) - branch.reason ++ branch.because, {
                val first = branch.leftCertificate.nn
                val second = conflictCertificate.nn
                val (low, high) = if branch.up then (second, first) else (first, second)
                val except = if branch.because.isEmpty then -1 else branch.because.head
                val at = (branch.floor + branch.ceil) / 2
                Certificate.Split(
                  branch.reason,
                  branch.x,
                  branch.floor,
                  branch.ceil,
                  low,
                  high,
                  except,
                  at,
                  branch.strict
                )
              }
            )
        case branch: Branch if !keepGoing() =>
          for _ <- open do pop()
          return Result.Unknown
        // Nothing is asserted yet, and the split stays in the set: it comes back if the client cannot take it now.
        case branch: Branch
            if open.isEmpty && splitOnDemand && branch.because.isEmpty && failedSplits((branch.x, branch.floor)) =>
          return Result.Split(branch.x, branch.floor)
        case branch: Branch =>
          open += branch
          push()
          current = side(branch, branch.up)
    throw AssertionError("unreachable")

  /** Bound propagation on every row as the simplex left it: it saw the rows
   *  before the pivots, and a pivoted row can tie together variables no
   *  original row did (`x = -y`, both at most 0, so both 0).
   */
  private def propagateRows(): Result =
    var b = 0
    while b < numVars do
      if rows(b) != null then
        propagateRow(b) match
          case Result.Sat => ()
          case unsat =>
            tightened.clear()
            return unsat
      b += 1
    Result.Sat

  /** Decides the rational relaxation of the bounds: bound propagation, then the
   *  simplex; `Sat` leaves the integrality to [[check]].
   */
  def checkRelaxation(): Result = propagateBounds() match
    case Result.Sat => simplex()
    case unsat => unsat

  /** A cut on the integer content of the mixed rows, for the problems branch
   *  and bound alone cannot close: an integer combination confined to a window
   *  holding none of its values (`is_int x` and `not (is_int (+ x 1))` — an
   *  integer difference in an open unit interval). The real variables are
   *  eliminated from the bounds and the rows — substituted away where a row
   *  defines them, Fourier–Motzkin pairs elsewhere — leaving inequalities over
   *  integer variables only, whose right sides round down after dividing by the
   *  gcd of the coefficients: opposite inequalities that cross after the
   *  rounding are inconsistent, and the bounds they came from explain it.
   *  Vacuous on a pure-integer problem, and skipped unless some row mixes the
   *  two kinds; the work is capped, a cut being an aid, not an obligation.
   */
  private def integerWindows(): Result = boundary:
    if !anyReal || !anyInt then break(Result.Sat)
    var mixed = false
    var b = 0
    while b < numVars && !mixed do
      val row = rows(b)
      mixed = row != null && row.existsVar(x => isInt(x) != isInt(b))
      b += 1
    if !mixed then break(Result.Sat)
    // The system: every bound as `Σ c·x ≤ d` with its reasons, every row touching a real as an equation.
    // With proofs, each with its certificate: the rows are identities over the unknowns, substituting by one
    // changes nothing there.
    val inequalities = ArrayBuffer.empty[(HashMap[Var, Rational], Delta, Set[Int], Certificate | Null)]
    val equations = ArrayBuffer.empty[HashMap[Var, Rational]]
    val reals = HashSet.empty[Var]
    b = 0
    while b < numVars do
      val row = rows(b)
      if row != null && (!isInt(b) || row.existsVar(x => !isInt(x))) then
        val eq = HashMap.empty[Var, Rational]
        var i = 0
        while i < row.size do
          eq(row.varAt(i)) = row.coefAt(i)
          i += 1
        eq(b) = Rational(-1)
        equations += eq
        for x <- eq.keys if !isInt(x) do reals += x
      b += 1
    for x <- 0 until numVars do
      if reals(x) || !isInt(x) then
        val u = upper(x)
        val l = lower(x)
        if u != null then inequalities += ((HashMap(x -> Rational.one), u.value, u.reasons, u.certificate))
        if l != null then inequalities += ((HashMap(x -> Rational(-1)), -l.value, l.reasons, l.certificate))
    // Eliminate each real: by the first equation defining it, its bounds following the substitution,
    // or by pairing its upper and lower inequalities when no equation mentions it.
    val cap = 256 // a cut is an aid, not an obligation: beyond this, give up quietly
    def substitute(into: HashMap[Var, Rational], x: Var, pivot: HashMap[Var, Rational]): Unit =
      into.get(x) match
        case None => ()
        case Some(c) =>
          val f = c / pivot(x)
          for (y, a) <- pivot do
            val updated = into.getOrElse(y, Rational.zero) - a * f
            if updated.isZero then into.remove(y) else into(y) = updated
    for x <- reals.toList.sorted do // a fixed order: the same conflict on every machine
      equations.find(_.contains(x)) match
        case Some(pivot) =>
          equations -= pivot
          for eq <- equations do substitute(eq, x, pivot)
          for (terms, _, _, _) <- inequalities do substitute(terms, x, pivot)
        case None =>
          val (touching, rest) = inequalities.toList.partition(_._1.contains(x))
          val (uppers, lowers) = touching.partition(_._1(x).signum > 0) // c·x ≤ ... vs −c·x ≤ ...
          if uppers.length * lowers.length + rest.length > cap then break(Result.Sat)
          inequalities.clear()
          inequalities ++= rest
          for (ut, ud, ur, uc) <- uppers; (lt, ld, lr, lc) <- lowers do
            val terms = ut.clone()
            val f = ut(x) / -lt(x)
            for (y, a) <- lt do
              val updated = terms.getOrElse(y, Rational.zero) + a * f
              if updated.isZero then terms.remove(y) else terms(y) = updated
            terms.remove(x)
            val certificate =
              if proofs then Certificate.Comb(Array(Rational.one, f), Array(uc.nn, lc.nn)) else null
            inequalities += ((terms, ud + ld * f, ur ++ lr, certificate))
    // Integer-only inequalities: divide by the gcd, round down, and look for a crossing pair.
    // With proofs, each with its certificate and the factor that took it to the key.
    val best = HashMap.empty[List[(Var, BigInt)], (BigInt, Set[Int], Certificate | Null, Rational)]
    for (terms, d, reasons, certificate) <- inequalities do
      if terms.isEmpty then
        if d < Delta.zero then break(unsat(reasons, certificate.nn))
      else if terms.keysIterator.forall(isInt(_)) then
        var l = BigInt(1)
        for (_, a) <- terms do l = l / (l gcd a.den) * a.den
        var g = BigInt(0)
        for (_, a) <- terms do g = g gcd (a.num * (l / a.den)).abs
        val key = terms.toList.map((y, a) => (y, a.num * (l / a.den) / g)).sortBy(_._1)
        val bound = (d * Rational(l) / Rational(g)).floor
        val better = best.get(key) match
          case Some((known, _, _, _)) => bound < known
          case None => true
        val factor = Rational(l, g)
        if better then best(key) = (bound, reasons, certificate, factor)
        best.get(key.map((y, n) => (y, -n))) match
          case Some((opposite, others, otherCertificate, otherFactor)) if bound + opposite < 0 =>
            def rounded = Certificate.Comb(
              Array(factor, otherFactor),
              Array(Certificate.Round(certificate.nn), Certificate.Round(otherCertificate.nn))
            )
            break(unsat(reasons ++ others, rounded))
          case _ => ()
    Result.Sat

  /** Whether the equations in force have an integer solution, as equations
   *  alone: the exact test for linear Diophantine equations, as in Griggio, "A
   *  Practical Approach to Satisfiability Modulo Linear Integer Arithmetic"
   *  (JSAT 2012). The relaxation is blind to `2x = 2y + 1`, and branch and
   *  bound walks the values of `x` to refute it.
   *
   *  The equations are the rows of the tableau over integer variables, and
   *  `x = c` for each variable the bounds fix. A row whose basic variable is
   *  not fixed and whose coefficients are integers is left out: it only defines
   *  that variable, which no other row mentions. Each equation is rewritten by
   *  the ones solved so far, fails if the gcd of its coefficients does not
   *  divide its constant, and is then solved for a variable of coefficient ±1,
   *  after reducing the coefficients by the smallest one through a fresh
   *  variable until there is one.
   */
  private def integerEquations(): Result = boundary:
    val solved = HashMap.empty[Int, Equation] // x ↦ the equation `x + … = c` it was solved from
    var fresh = numVars
    var work = 0
    def eliminate(equation: Equation): Unit =
      while
        work += equation.coefs.valuesIterator.map(_.bitLength / 64 + 1).sum
        if work > Solver.equationWork then break(Result.Sat)
        val g = equation.coefs.valuesIterator.foldLeft(BigInt(0))(_ gcd _)
        if equation.constant != 0 && (g == 0 || equation.constant % g != 0) then
          break(unsat(equation.reasons, refutation(equation.factors.nn)))
        if equation.coefs.isEmpty then return
        val (x, a) = equation.coefs.minBy((y, b) => (!solved.contains(y), b.abs, y)) // solved ones first
        if solved.contains(x) then // x + rest = c: subtract a times it
          val by = solved(x)
          for (y, b) <- by.coefs do
            val sum = equation.coefs.getOrElse(y, BigInt(0)) - a * b
            if sum == 0 then equation.coefs -= y else equation.coefs(y) = sum
          equation.constant -= a * by.constant
          equation.reasons ++= by.reasons
          val factors = equation.factors
          if factors != null then
            for (y, f) <- by.factors.nn do
              val sum = factors.getOrElse(y, Rational.zero) - f * Rational(a)
              if sum.isZero then factors -= y else factors(y) = sum
        else if a.abs == g then // ±1 once divided by the gcd: solved
          equation.coefs.mapValuesInPlace((_, b) => b / a)
          equation.constant /= a
          val factors = equation.factors
          if factors != null then factors.mapValuesInPlace((_, f) => f / Rational(a))
          solved(x) = equation
        else // x = t - Σ q y, where each other coefficient is q a + r: the equation becomes a t + Σ r y = c
          val definition = Equation(HashMap(x -> BigInt(1), fresh -> BigInt(-1)), 0, Set.empty, newFactors())
          for (y, b) <- equation.coefs.toArray if y != x do
            val q = (b.abs + a.abs / 2) / a.abs * (b.signum * a.signum) // b / a rounded: |r| ≤ |a| / 2
            if q != 0 then definition.coefs(y) = q
            if b == q * a then equation.coefs -= y else equation.coefs(y) = b - q * a
          equation.coefs -= x
          equation.coefs(fresh) = a
          solved(x) = definition
          fresh += 1
        solved.get(x).forall(_ ne equation)
      do ()
    def newFactors(): HashMap[Var, Rational] | Null = if proofs then HashMap.empty else null
    // The equation `Σ f·x = Σ f·c` of the fixed variables, an integer combination over the unknowns whose
    // constant is not a multiple of the gcd of its coefficients: its two sides, each rounded, cross.
    def refutation(factors: HashMap[Var, Rational]): Certificate =
      def side(up: Boolean): Certificate =
        val parts = factors.toArray
        Certificate.Round(
          Certificate.Comb(
            parts.map(_._2.abs),
            parts.map((x, f) => (if (f.signum > 0) == up then upper(x) else lower(x)).nn.certificate.nn)
          )
        )
      Certificate.Comb(Array(Rational.one, Rational.one), Array(side(true), side(false)))
    def isFixed(x: Var): Boolean =
      val l = lower(x)
      val u = upper(x)
      l != null && u != null && l.value == u.value && l.value.isInteger
    val mentioned = HashSet.empty[Var]
    def fix(x: Var): Unit =
      if isFixed(x) && mentioned.add(x) then
        val reasons = lower(x).nn.reasons ++ upper(x).nn.reasons
        val factors = newFactors()
        if factors != null then factors(x) = Rational.one
        eliminate(Equation(HashMap(x -> BigInt(1)), lower(x).nn.value.r.num, reasons, factors))
    for b <- 0 until numVars do
      val row = rows(b)
      if row != null && isInt(b) && !row.existsVar(x => !isInt(x)) then
        val terms = (0 until row.size).map(i => (row.varAt(i), row.coefAt(i)))
        val l = terms.foldLeft(BigInt(1))((l, term) => l / (l gcd term._2.den) * term._2.den)
        if l != 1 || isFixed(b) then // l·b = Σ l·a·x, then what the bounds fix among its variables
          eliminate(
            Equation(HashMap.from(terms.map((x, a) => (x, a.num * (l / a.den)))) += b -> -l, 0, Set.empty, newFactors())
          )
          (b +: terms.map(_._1)).foreach(fix)
    Result.Sat

  /** Repairs the basic variables violating their bounds, smallest first, by
   *  pivoting with the smallest non-basic variable of their row that can move
   *  in the right direction (`Check` in the paper); when none can, the row's
   *  bounds explain the infeasibility.
   */
  private def simplex(): Result =
    while true do
      while suspects.nonEmpty && (rows(suspects.min) == null || !violates(suspects.min)) do suspects.removeMin()
      if suspects.isEmpty then return Result.Sat
      val b = suspects.min // stays on the heap: it still violates if this returns, and goes next round if it pivots
      val row = rows(b).nn
      val l = lower(b)
      val u = upper(b)
      val tooLow = l != null && compareValue(b, l.value) < 0
      val bound = if tooLow then l.nn else u.nn
      // To raise `b`, raise a non-basic variable with a positive coefficient or lower one with a negative coefficient (the converse to lower `b`).
      var n = -1
      var i = 0
      while i < row.size do // sorted: the first that can move is the smallest (Bland's rule)
        val j = row.varAt(i)
        val a = row.coefAt(i)
        if n == -1 && (if a.signum > 0 == tooLow then canRaise(j) else canLower(j)) then n = j
        i += 1
      if n == -1 then
        var reasons = bound.reasons
        i = 0
        while i < row.size do
          val j = row.varAt(i)
          reasons = reasons ++ (if row.coefAt(i).signum > 0 == tooLow then upper(j) else lower(j)).nn.reasons
          i += 1
        // The bound of `b`, and the row's absolute coefficients for the bounds of its variables.
        return unsat(
          reasons,
          comb(
            Array.tabulate(row.size + 1)(k => if k == row.size then Rational.one else row.coefAt(k).abs),
            Array.tabulate(row.size + 1)(k =>
              if k == row.size then bound.certificate.nn
              else
                val j = row.varAt(k)
                (if row.coefAt(k).signum > 0 == tooLow then upper(j) else lower(j)).nn.certificate.nn
            )
          )
        )
      if !keepGoing() then return Result.Unknown
      pivotAndUpdate(b, n, bound.value)
    throw AssertionError("unreachable")

  /** Compares the value of `x` (rational and infinitesimal parts) to `c`. */
  private def compareValue(x: Var, c: Delta): Int =
    val first = values(x).compare(c.r)
    if first != 0 || !anyReal then first else valuesD(x).compare(c.d)

  private def deltaValue(x: Var): Delta =
    Delta(values(x), if anyReal then valuesD(x) else Rational.zero)

  private def violates(x: Var): Boolean =
    val l = lower(x)
    val u = upper(x)
    (l != null && compareValue(x, l.value) < 0) || (u != null && compareValue(x, u.value) > 0)

  private def suspect(x: Var): Unit = if violates(x) then suspects += x

  private def canRaise(x: Var): Boolean =
    val u = upper(x)
    u == null || compareValue(x, u.value) < 0

  private def canLower(x: Var): Boolean =
    val l = lower(x)
    l == null || compareValue(x, l.value) > 0

  /** The number of open levels. */
  def level: Int = levels.length

  def push(): Unit = levels += ((trail.length, distinct.length))

  /** Removes the bounds and disequalities asserted since the last [[push]]. */
  def pop(): Unit =
    require(levels.nonEmpty, "pop without a matching push")
    val (mark, distinctMark) = levels.remove(levels.length - 1)
    distinct.takeInPlace(distinctMark)
    while trail.length > mark do
      val undo = trail.remove(trail.length - 1)
      if undo.isUpper then upper(undo.x) = undo.old else lower(undo.x) = undo.old
      moved += undo.x
    tightened.clear() // popping only loosens bounds
