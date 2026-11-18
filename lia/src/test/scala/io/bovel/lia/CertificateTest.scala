package io.bovel.lia

import scala.collection.mutable.HashMap
import scala.util.Random

import Solver.Result

class CertificateTest extends munit.FunSuite:
  /** A random system of bounds and disequalities on random combinations of `n`
   *  integer variables (and `reals` real ones), asserted with proofs on, then
   *  checked: every `Unsat` has a certificate that derives a contradiction from
   *  the bounds and disequalities of its reasons. Returns whether it was
   *  `Unsat`. A `box` of that many bits stands for the small-model box.
   */
  def run(rnd: Random, n: Int, reals: Int, m: Int, range: Int, box: Long = -1): Boolean =
    val solver = Solver()
    solver.proofs = true
    solver.boxBitsOverride = box
    val vars = IndexedSeq.fill(n)(solver.newVar()) ++ IndexedSeq.fill(reals)(solver.newVar(integer = false))
    val asserted = HashMap.empty[Int, Certificate.Hyp]
    val distinct = HashMap.empty[Int, (Var, BigInt)]
    var result: Result = Result.Sat
    var k = 0
    while k < m && result == Result.Sat do
      val terms =
        List.fill(1 + rnd.nextInt(3))((BigInt(rnd.nextInt(2 * range + 1) - range), vars(rnd.nextInt(vars.length))))
          .filter(_._1 != 0)
          .distinctBy(_._2)
      if terms.nonEmpty then
        val x = terms match
          case (a, x) :: Nil if a == 1 => x
          case _ => solver.newSlack(terms, integer = terms.forall((_, y) => solver.isInteger(y)))
        val c = BigInt(rnd.nextInt(4 * range + 1) - 2 * range)
        if rnd.nextInt(5) == 0 then
          distinct(k) = (x, c)
          result = solver.assertDistinct(x, c, k)
        else
          val upper = rnd.nextBoolean()
          val strict = rnd.nextInt(4) == 0
          asserted(k) = Certificate.Hyp(k, x, c, strict, upper)
          result = if upper then solver.assertUpper(x, c, strict, k) else solver.assertLower(x, c, strict, k)
      k += 1
    if result == Result.Sat then result = solver.check()
    result match
      case Result.Unsat(reasons) =>
        val checker = Certificate.Checker(
          solver.form,
          solver.isInteger,
          h => if asserted.get(h.reason).contains(h) then None else Some(s"not asserted: $h"),
          (r, x, c) => if distinct.get(r).contains((x, c)) then None else Some(s"not asserted: $x ≠ $c")
        )
        assertEquals(checker.check(solver.conflictCertificate.nn, reasons), None)
        true
      case _ => false

  test("random integer systems: every unsat is certified"):
    val rnd = Random(1)
    var unsats = 0
    for _ <- 0 until 2000 do
      if run(rnd, 2 + rnd.nextInt(4), 0, 3 + rnd.nextInt(8), 1 + rnd.nextInt(5)) then unsats += 1
    assert(unsats > 300, s"$unsats unsats")

  test("random mixed systems: every unsat is certified"):
    val rnd = Random(2)
    var unsats = 0
    for _ <- 0 until 2000 do
      if run(rnd, 1 + rnd.nextInt(3), 1 + rnd.nextInt(2), 3 + rnd.nextInt(8), 1 + rnd.nextInt(5)) then unsats += 1
    assert(unsats > 300, s"$unsats unsats")

  test("with proofs, the check gives up rather than prune past the small-model box"):
    val rnd = Random(3)
    var unsats = 0
    for _ <- 0 until 2000 do
      if run(rnd, 2 + rnd.nextInt(4), 0, 3 + rnd.nextInt(8), 1 + rnd.nextInt(5), box = 2) then unsats += 1
    assert(unsats > 100, s"$unsats unsats")
