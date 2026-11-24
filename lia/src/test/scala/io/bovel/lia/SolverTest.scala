package io.bovel.lia

import scala.util.Random

import Solver.Result

class SolverTest extends munit.FunSuite:
  /** A bound on the value of an expression: `Σ coefficients × variables ⋈ c`,
   *  as a test-side description.
   */
  case class Constraint(terms: List[(BigInt, Int)], isUpper: Boolean, c: BigInt, distinct: Boolean = false):
    def holds(assignment: Int => BigInt): Boolean =
      val v = terms.map((a, x) => a * assignment(x)).sum
      if distinct then v != c else if isUpper then v <= c else v >= c

  /** Asserts the constraints with their index as reason, over `n` variables. */
  def solverOf(n: Int, constraints: List[Constraint]): (Solver, Result) =
    val solver = Solver()
    val vars = List.fill(n)(solver.newVar())
    var result: Result = Result.Sat
    for (k, i) <- constraints.zipWithIndex do
      val x = k.terms match
        case (a, x) :: Nil if a == 1 => vars(x)
        case terms => solver.newSlack(terms.map((a, x) => (a, vars(x))))
      val r =
        if k.distinct then solver.assertDistinct(x, k.c, i)
        else if k.isUpper then solver.assertUpper(x, k.c, i)
        else solver.assertLower(x, k.c, i)
      if r != Result.Sat && result == Result.Sat then result = r
    (solver, result)

  def solve(n: Int, constraints: List[Constraint]): (Solver, Result) =
    val (solver, asserted) = solverOf(n, constraints)
    (solver, if asserted == Result.Sat then solver.check() else asserted)

  test("infeasible bounds on a sum"):
    val k = List(
      Constraint(List((1, 0)), false, 1), // x ≥ 1
      Constraint(List((1, 1)), false, 1), // y ≥ 1
      Constraint(List((1, 0), (1, 1)), true, 1) // x + y ≤ 1
    )
    assertEquals(solve(2, k)._2, Result.Unsat(Set(0, 1, 2)))

  test("a feasible system and its model"):
    val k = List(
      Constraint(List((1, 0), (1, 1)), false, 3), // x + y ≥ 3
      Constraint(List((1, 0), (-1, 1)), true, -1), // x - y ≤ -1
      Constraint(List((1, 0)), false, 0), // x ≥ 0
      Constraint(List((1, 1)), true, 3) // y ≤ 3
    )
    val (solver, result) = solve(2, k)
    assertEquals(result, Result.Sat)
    assert(k.forall(_.holds(solver.value)), (solver.value(0), solver.value(1)))

  test("bounds on an expression are tightened by the gcd of its coefficients"):
    val k =
      List(Constraint(List((2, 0), (2, 1)), true, 3), Constraint(List((2, 0), (2, 1)), false, 3)) // 3 ≤ 2x + 2y ≤ 3
    assertEquals(solve(2, k)._2, Result.Unsat(Set(0, 1)))

  test("branch and bound"):
    // x + 2y = 1 and x = 2y: 4y = 1, feasible over the rationals only.
    val k = List(
      Constraint(List((1, 0), (2, 1)), true, 1),
      Constraint(List((1, 0), (2, 1)), false, 1),
      Constraint(List((1, 0), (-2, 1)), true, 0),
      Constraint(List((1, 0), (-2, 1)), false, 0)
    )
    assertEquals(solve(2, k)._2, Result.Unsat(Set(0, 1, 2, 3)))
    // x + 2y = 1 and x ≥ 2y: y = 0, x = 1 among others.
    val (solver, result) = solve(2, k.take(3))
    assertEquals(result, Result.Sat)
    assert(k.take(3).forall(_.holds(solver.value)))

  /** Random constraints over `n` variables in a box, with the brute force over
   *  the box as the oracle.
   */
  def randomConstraints(rnd: Random, n: Int, m: Int, box: Int): List[Constraint] =
    val bounds = (0 until n).flatMap(x =>
      List(Constraint(List((1, x)), false, -box), Constraint(List((1, x)), true, box))
    )
    val others = List.fill(m):
      val terms = rnd.shuffle((0 until n).toList).take(1 + rnd.nextInt(3)).map(x => (BigInt(rnd.nextInt(7) - 3), x))
      Constraint(
        terms.filter(_._1 != 0).map((a, x) => (a, x)) match
          case Nil => List((BigInt(1), rnd.nextInt(n)))
          case t => t
        ,
        rnd.nextBoolean(),
        rnd.nextInt(2 * box + 1) - box,
        rnd.nextInt(4) == 0
      )
    bounds.toList ++ others

  def bruteForce(n: Int, box: Int, constraints: List[Constraint]): Boolean =
    def go(x: Int, assignment: List[BigInt]): Boolean =
      if x == n then constraints.forall(_.holds(assignment.reverse))
      else (-box to box).exists(v => go(x + 1, BigInt(v) :: assignment))
    go(0, Nil)

  test("random systems against brute force"):
    val rnd = Random(7)
    var sat = 0
    var unsat = 0
    for round <- 0 until 300 do
      val n = 2 + rnd.nextInt(3)
      val box = 2
      val k = randomConstraints(rnd, n, 2 + rnd.nextInt(5), box)
      val (solver, result) = solve(n, k)
      val expected = bruteForce(n, box, k)
      result match
        case Result.Sat =>
          assert(expected, s"round $round: sat but brute force finds no solution: $k")
          assert(k.forall(_.holds(solver.value)), s"round $round: model violates a constraint")
          sat += 1
        case Result.Unknown | Result.Split(_, _) => fail(s"round $round: the solver gave up")
        case Result.Unsat(reasons) =>
          assert(!expected, s"round $round: unsat but brute force finds a solution: $k")
          assert(reasons.forall(r => r >= 0 && r < k.length), s"round $round: reasons $reasons")
          // The explanation is unsatisfiable by itself.
          assertEquals(
            solve(n, reasons.toList.sorted.map(k))._2.getClass,
            classOf[Result.Unsat],
            s"round $round: explanation $reasons of $k"
          )
          unsat += 1
    assert(sat > 50 && unsat > 50, (sat, unsat))

  /** A solver over `n` variables where each expression is fixed to a constant,
   *  the bounds of the `i`th one asserted with the reasons `2i` and `2i + 1`.
   */
  def equations(n: Int, fixed: List[(List[(BigInt, Int)], BigInt)]): Solver =
    val solver = Solver()
    val vars = List.fill(n)(solver.newVar())
    for ((terms, c), i) <- fixed.zipWithIndex do
      val s = solver.newSlack(terms.map((a, x) => (a, vars(x))))
      assertEquals(solver.assertUpper(s, c, 2 * i), Result.Sat)
      assertEquals(solver.assertLower(s, c, 2 * i + 1), Result.Sat)
    solver

  test("equations without an integer solution are refuted with no bound on the variables"):
    // x even and odd: x = 2y, x = 2z + 1. Branch and bound alone slides along x for ever.
    val parity = equations(3, List((List((1, 0), (-2, 1)), 0), (List((1, 0), (-2, 2)), 1)))
    assertEquals(parity.check(), Result.Unsat(Set(0, 1, 2, 3)))

  test("the equations that take no part in a refutation are left out of it"):
    // x + y = 1 and x = y, and z = 3x + 5.
    val halves = equations(
      3,
      List((List((1, 0), (1, 1)), 1), (List((1, 0), (-1, 1)), 0), (List((1, 2), (-3, 0)), 5))
    )
    assertEquals(halves.check(), Result.Unsat(Set(0, 1, 2, 3)))

  test("the equation check reduces coefficients of either sign"):
    // No coefficient of the first equation is ±1, so the check reduces them by the smallest one.
    // 4x + 6y = 9z and 9z = 6w + 3: the left is even, the right odd.
    val odd = equations(4, List((List((4, 0), (6, 1), (-9, 2)), 0), (List((9, 2), (-6, 3)), 3)))
    assertEquals(odd.check(), Result.Unsat(Set(0, 1, 2, 3)))

  test("a bound is moved onto the lattice the equations leave"):
    // Two residues of one number modulo 4: n = r + 4k and n + 4 = s + 4j with r and s in [0, 3], and r ≠ s.
    // The equations make r − s a multiple of 4, and the bounds keep it within 3 of zero. Branch and bound
    // alone walks k and j, which have no bound (issue 150).
    val residues = List(
      Constraint(List((1, 0), (-1, 1), (-4, 2)), true, 0),
      Constraint(List((1, 0), (-1, 1), (-4, 2)), false, 0),
      Constraint(List((1, 0), (-1, 3), (-4, 4)), true, -4),
      Constraint(List((1, 0), (-1, 3), (-4, 4)), false, -4),
      Constraint(List((1, 1)), false, 0),
      Constraint(List((1, 1)), true, 3),
      Constraint(List((1, 3)), false, 0),
      Constraint(List((1, 3)), true, 3)
    )
    def checked(n: Int, constraints: List[Constraint]): Result =
      val (solver, asserted) = solverOf(n, constraints)
      assertEquals(asserted, Result.Sat)
      var steps = 200
      solver.keepGoing = () =>
        steps -= 1; steps >= 0
      solver.check()
    assertEquals(
      checked(5, residues :+ Constraint(List((1, 1), (-1, 3)), true, 0, distinct = true)),
      Result.Unsat((0 to 8).toSet)
    )
    // Three bits of a 64-bit number, read two ways: x = 2q + r, q = 4p + b and x = 8t + s, with 2b + r ≠ s.
    // The quotients are bounded, by 2^61 and more (issue 159).
    val top = BigInt(1) << 64
    def within(x: Int, most: BigInt) = List(Constraint(List((1, x)), false, 0), Constraint(List((1, x)), true, most))
    def equal(terms: List[(BigInt, Int)]) = List(Constraint(terms, true, 0), Constraint(terms, false, 0))
    val bits =
      within(0, top - 1) ++ within(1, top / 2 - 1) ++ within(2, 1) ++ within(3, top / 8 - 1) ++ within(4, 3) ++
        within(5, top / 8 - 1) ++ within(6, 7) ++
        equal(List((1, 0), (-2, 1), (-1, 2))) ++ equal(List((1, 1), (-4, 3), (-1, 4))) ++
        equal(List((1, 0), (-8, 5), (-1, 6)))
    val read = checked(7, bits :+ Constraint(List((2, 4), (1, 2), (-1, 6)), true, 0, distinct = true))
    assert(read.isInstanceOf[Result.Unsat], read)
    // A lattice leaves the solutions there are: x = 4k + 1 within [2, 9] is 5 or 9, and 9 once 5 is excluded.
    val one = List(
      Constraint(List((1, 0), (-4, 1)), true, 1),
      Constraint(List((1, 0), (-4, 1)), false, 1),
      Constraint(List((1, 0)), false, 2),
      Constraint(List((1, 0)), true, 9)
    )
    val (first, firstResult) = solve(2, one)
    assertEquals(firstResult, Result.Sat)
    assert(Set(BigInt(5), BigInt(9))(first.value(0)), first.value(0))
    val (second, secondResult) = solve(2, one :+ Constraint(List((1, 0)), true, 5, distinct = true))
    assertEquals(secondResult, Result.Sat)
    assertEquals(second.value(0), BigInt(9))
    val none = one ++ List(Constraint(List((1, 0)), true, 5, distinct = true), Constraint(List((1, 0)), true, 8))
    assert(solve(2, none)._2.isInstanceOf[Result.Unsat])

  test("the equation check agrees with branch and bound"):
    val rnd = Random(23)
    var refuted = 0
    for round <- 0 until 400 do
      val n = 2 + rnd.nextInt(3)
      val fixed = List.fill(1 + rnd.nextInt(3)):
        val terms = (0 until n).toList.flatMap: x =>
          val a = rnd.nextInt(13) - 6
          if a == 0 then Nil else List((BigInt(a), x))
        (if terms.isEmpty then List((BigInt(2), 0)) else terms, BigInt(rnd.nextInt(9) - 4))
      // The result with the bounds of the reasons kept, and the solver if it took a check to tell.
      def solve(check: Boolean, keep: Int => Boolean): (Result, Option[Solver]) =
        val s = Solver()
        s.equationCheck = check
        val vars = List.fill(n)(s.newVar())
        // Every variable within [-8, 8], or branch and bound alone may not end.
        val boxed = vars.iterator.zipWithIndex.flatMap: (x, i) =>
          Iterator(100 + 2 * i, 101 + 2 * i).map: reason =>
            if !keep(reason) then Result.Sat
            else if reason % 2 == 0 then s.assertUpper(x, 8, reason)
            else s.assertLower(x, -8, reason)
        val asserted = boxed ++ fixed.zipWithIndex.iterator.flatMap: (equation, i) =>
          val slack = s.newSlack(equation._1.map((a, x) => (a, vars(x))))
          Iterator(2 * i, 2 * i + 1).filter(keep).map: reason =>
            if reason % 2 == 0 then s.assertUpper(slack, equation._2, reason)
            else s.assertLower(slack, equation._2, reason)
        asserted.find(_ != Result.Sat).fold((s.check(), Some(s)))((_, None))
      val (expected, _) = solve(false, _ => true)
      solve(true, _ => true) match
        case (Result.Sat, fast) =>
          assertEquals(expected, Result.Sat, fixed)
          for (terms, c) <- fixed do assertEquals(terms.map((a, x) => a * fast.get.value(x)).sum, c, fixed)
        case (Result.Unsat(reasons), fast) =>
          assert(expected.isInstanceOf[Result.Unsat], (fixed, expected))
          // The explanation is unsatisfiable on its own (branch and bound needs the box to tell).
          assert(solve(false, r => r >= 100 || reasons(r))._1.isInstanceOf[Result.Unsat], (fixed, reasons))
          if fast.nonEmpty then refuted += 1
        case (result, _) => fail(s"$fixed: $result")
    assert(refuted > 50, refuted)

  test("push and pop"):
    val rnd = Random(11)
    for round <- 0 until 100 do
      val n = 2 + rnd.nextInt(3)
      val base = randomConstraints(rnd, n, 1 + rnd.nextInt(3), 3)
      val (solver, asserted) = solverOf(n, base)
      if asserted == Result.Sat && solver.check() == Result.Sat then
        val more = randomConstraints(rnd, n, 1 + rnd.nextInt(3), 3).drop(2 * n)
        solver.push()
        var result: Result = Result.Sat
        for (k, i) <- more.zipWithIndex do
          val x = solver.newSlack(k.terms)
          val r =
            if k.distinct then solver.assertDistinct(x, k.c, 100 + i)
            else if k.isUpper then solver.assertUpper(x, k.c, 100 + i)
            else solver.assertLower(x, k.c, 100 + i)
          if r != Result.Sat && result == Result.Sat then result = r
        if result == Result.Sat then result = solver.check()
        assertEquals(result.isInstanceOf[Result.Sat.type], bruteForce(n, 3, base ++ more), s"round $round")
        solver.pop()
        assertEquals(solver.check(), Result.Sat, s"round $round: not satisfiable again after pop")
        assert(base.forall(_.holds(solver.value)), s"round $round: model after pop")

  test("a mixed row confining an integer difference to an empty window is unsat"):
    val solver = Solver()
    val n1 = solver.newVar()
    val n2 = solver.newVar()
    val x = solver.newVar(integer = false)
    // x = n1 - n2, and 0 < x < 1: an integer difference in an open unit interval.
    val s = solver.newSlack(List((BigInt(1), n1), (BigInt(-1), n2), (BigInt(-1), x)), integer = false)
    assertEquals(solver.assertUpper(s, 0, 1), Result.Sat)
    assertEquals(solver.assertLower(s, 0, 2), Result.Sat)
    assertEquals(solver.assertLower(x, 0, true, 3), Result.Sat)
    assertEquals(solver.assertUpper(x, 1, true, 4), Result.Sat)
    solver.check() match
      case Result.Unsat(reasons) => assert(reasons.subsetOf(Set(1, 2, 3, 4)), reasons)
      case other => fail(s"expected unsat, got $other")

  test("branch and bound halves the range of a bounded unknown it slides along"):
    // Satisfiable, but the vertices are fractional all the way down a 2^32 range: one unit at a time never ends.
    val top = BigInt(1) << 32
    val box = (0 until 4).toList.flatMap(x =>
      List(Constraint(List((1, x)), false, 0), Constraint(List((1, x)), true, top))
    )
    val k = box ++ List(
      Constraint(List((2, 0), (-1, 1), (1, 2), (3, 3)), false, 2), // 2x - y + z + 3w ≥ 2
      Constraint(List((-2, 0), (2, 1), (-3, 2)), false, top + 1) // -2x + 2y - 3z ≥ 2^32 + 1
    )
    val (solver, asserted) = solverOf(4, k)
    assertEquals(asserted, Result.Sat)
    var steps = 3000
    solver.keepGoing = () =>
      steps -= 1; steps >= 0
    assertEquals(solver.check(), Result.Sat)
    assert(k.forall(_.holds(solver.value)))

  test("the small-model box turns a sliding branch and bound into a sound unsat"):
    // x even and x odd: integer-infeasible, rationally satisfiable everywhere, and no single
    // expression's gcd sees it — the branches slide.
    def parity(): Solver =
      val s = Solver()
      s.equationCheck = false // the equation check refutes this one at once: the test is of the box
      val x = s.newVar()
      val y = s.newVar()
      val z = s.newVar()
      val even = s.newSlack(List((BigInt(1), x), (BigInt(-2), y)))
      val odd = s.newSlack(List((BigInt(1), x), (BigInt(-2), z)))
      assertEquals(s.assertUpper(even, 0, 1), Result.Sat)
      assertEquals(s.assertLower(even, 0, 2), Result.Sat)
      assertEquals(s.assertUpper(odd, 1, 3), Result.Sat)
      assertEquals(s.assertLower(odd, 1, 4), Result.Sat)
      s
    val diverging = parity()
    var steps = 10000
    diverging.keepGoing = () =>
      steps -= 1; steps >= 0
    assertEquals(diverging.check(), Result.Unknown) // without the box: to the fuel
    val boxed = parity()
    boxed.boxBitsOverride = 8 // a test-sized box: past it, exhaustion is unsat
    boxed.check() match
      case Result.Unsat(reasons) => assert(reasons.subsetOf(Set(1, 2, 3, 4)), reasons)
      case other => fail(s"expected unsat, got $other")

  test("splitting on demand hands a split that failed on both sides to the client"):
    // x = 2y and x = 2z + 1 with 0 ≤ y, z ≤ 3: integer-infeasible, and no single expression's gcd sees it.
    def parity(): Solver =
      val s = Solver()
      val x = s.newVar()
      val y = s.newVar()
      val z = s.newVar()
      val even = s.newSlack(List((BigInt(1), x), (BigInt(-2), y)))
      val odd = s.newSlack(List((BigInt(1), x), (BigInt(-2), z)))
      for (v, lo, hi, reason) <- List((even, 0, 0, 1), (odd, 1, 1, 3), (y, 0, 3, 5), (z, 0, 3, 7)) do
        assertEquals(s.assertLower(v, lo, reason), Result.Sat)
        assertEquals(s.assertUpper(v, hi, reason + 1), Result.Sat)
      s
    // Without it, a check answers by itself, however often it is asked.
    val alone = parity()
    for _ <- 0 until 3 do assert(alone.check().isInstanceOf[Result.Unsat])

    val solver = parity()
    solver.splitOnDemand = true
    var splits = 0
    var reason = 100

    /** Refutes the problem as a client would: both sides of every split handed
     *  over, each asserted with a reason of its own. Returns the reasons used.
     */
    def refute(): Set[Int] = solver.check() match
      case Result.Unsat(reasons) => reasons
      case Result.Split(x, c) =>
        splits += 1
        reason += 2
        val (left, right) = (reason, reason + 1)
        solver.push()
        assertEquals(solver.assertUpper(x, c, left), Result.Sat)
        val l = refute()
        solver.pop()
        solver.push()
        assertEquals(solver.assertLower(x, c + 1, right), Result.Sat)
        val r = refute()
        solver.pop()
        (l - left) ++ (r - right)
      case other => fail(s"expected unsat or a split, got $other")
    assert(refute().subsetOf((1 to 8).toSet)) // the first check: nothing failed before, so no split
    assertEquals(splits, 0)
    // A split that failed comes up again within a few checks (the relaxation may start elsewhere): it is
    // the client's then, and the refutation of its two sides is one of the problem.
    var checks = 0
    while splits == 0 && checks < 20 do
      assert(refute().subsetOf((1 to 8).toSet))
      checks += 1
    assert(splits > 0)
