package io.bovel.cdclt

class ProofTest extends munit.FunSuite:
  val helpers = SolverTest()
  import helpers.AtMostTheory

  /** Solves with a proof, and on `Unsat` checks it: the derived steps by unit
   *  propagation, the lemmas with `lemma`, and the conclusion against
   *  `expected` (the empty clause by default).
   */
  def solveAndCheck(
      solver: Solver,
      assumptions: Array[Lit] = Array.empty,
      lemma: Array[Lit] => Boolean = _ => false
  ): Solver.Result =
    val result = solver.solve(assumptions, () => true)
    if result == Solver.Result.Unsat then
      val proof = solver.proof.nn
      assertEquals(proof.check(l => if lemma(l.clause) then None else Some("does not hold")), None)
      val conclusion = proof.steps(proof.conclusion).clause.toSet
      assert(conclusion.forall(l => assumptions.contains(l.neg)), s"conclusion $conclusion")
    result

  def randomClauses(rnd: scala.util.Random, n: Int, m: Int): Seq[Seq[Lit]] =
    Seq.fill(m)(Seq.fill(3)(Lit(rnd.nextInt(n), rnd.nextBoolean())))

  test("x and not x"):
    val s = Solver(1, proofs = true)
    s.addClause(Lit(0))
    s.addClause(Lit(0, false))
    assertEquals(solveAndCheck(s), Solver.Result.Unsat)

  test("random 3-SAT: every unsat has a proof"):
    val rnd = scala.util.Random(7)
    var unsats = 0
    for _ <- 0 until 200 do
      val n = 10 + rnd.nextInt(30)
      val s = Solver(n, proofs = true, restartInterval = 1 + rnd.nextInt(50))
      for c <- randomClauses(rnd, n, (4.6 * n).toInt) do s.addClause(c*)
      if solveAndCheck(s) == Solver.Result.Unsat then unsats += 1
    assert(unsats > 50, s"$unsats unsats")

  /** A clause of [[AtMostTheory]] holds when its negation makes more than `k`
   *  atoms of a group true.
   */
  def atMostLemma(groups: Seq[(Seq[Var], Int)])(clause: Array[Lit]): Boolean =
    val forcedTrue = clause.filter(!_.positive).map(_.variable).toSet
    groups.exists((atoms, k) => atoms.distinct.count(forcedTrue) > k)

  test("random problems with a theory: lemmas and derivations check"):
    val rnd = scala.util.Random(8)
    var unsats = 0
    for _ <- 0 until 300 do
      val n = 4 + rnd.nextInt(10)
      val groups =
        Seq.fill(1 + rnd.nextInt(3))((Seq.fill(2 + rnd.nextInt(4))(rnd.nextInt(n)).distinct, 1 + rnd.nextInt(2)))
      val s = Solver(n, AtMostTheory(groups), restartInterval = 1 + rnd.nextInt(5), proofs = true)
      for c <- randomClauses(rnd, n, 3 * n) do s.addClause(c*)
      if solveAndCheck(s, lemma = atMostLemma(groups)) == Solver.Result.Unsat then unsats += 1
    assert(unsats > 30, s"$unsats unsats")

  test("under assumptions, the conclusion is the clause of the failed ones"):
    val rnd = scala.util.Random(9)
    var unsats = 0
    for _ <- 0 until 300 do
      val n = 10 + rnd.nextInt(10)
      val s = Solver(n, proofs = true)
      for c <- randomClauses(rnd, n, (3.5 * n).toInt) do s.addClause(c*)
      val assumptions = Array.fill(3)(Lit(rnd.nextInt(n), rnd.nextBoolean())).distinctBy(_.variable)
      if solveAndCheck(s, assumptions) == Solver.Result.Unsat then unsats += 1
      // Solving again without them: the proof goes on from the same steps.
      solveAndCheck(s)
    assert(unsats > 30, s"$unsats unsats")

  test("incremental: clauses added between solves"):
    val rnd = scala.util.Random(10)
    for _ <- 0 until 100 do
      val n = 15
      val s = Solver(n, proofs = true)
      var done = false
      while !done do
        for c <- randomClauses(rnd, n, 5) do s.addClause(c*)
        done = solveAndCheck(s) == Solver.Result.Unsat
