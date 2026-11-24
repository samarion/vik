package io.bovel.bench.vik

import java.util.concurrent.TimeUnit

import scala.compiletime.uninitialized
import scala.util.Random

import io.bovel.vik.*
import org.openjdk.jmh.annotations.*
import io.bovel.vik.Formula.*
import io.bovel.vik.Solver
import io.bovel.vik.Term.*

/** Uninterpreted functions over integers (the combination of the e-graph and
 *  the LIA solver): ten random formula sets of `n` formulas over `n` integer
 *  constants in `[-5, 5]` and `f : Int -> Int`, comparisons and equalities
 *  between applications and combinations (`f(x + 1) <= f(y)`, `f(x) = y - 1`,
 *  ...), a mix of satisfiable and unsatisfiable sets. The shared integer terms
 *  grow with `n` and the equality atoms of the combination with their square:
 *  `n = 20` takes minutes per set.
 */
@State(Scope.Thread)
@BenchmarkMode(Array(Mode.AverageTime))
@OutputTimeUnit(TimeUnit.MILLISECONDS)
@Fork(3)
@Warmup(iterations = 5, time = 1)
@Measurement(iterations = 5, time = 1)
class UfliaBench:

  @Param(Array("5", "10"))
  var n: Int = uninitialized

  private var sets: List[List[Formula]] = uninitialized

  @Setup(Level.Trial)
  def setup(): Unit =
    val rnd = Random(4)
    def const(): Term = Const(s"x${rnd.nextInt(n)}")
    def term(depth: Int): Term = rnd.nextInt(if depth > 0 then 4 else 2) match
      case 0 => const()
      case 1 => Num(rnd.nextInt(11) - 5)
      case 2 => App(Const("f"), List(term(depth - 1)))
      case _ => Term.linear(
          List((BigInt(1), term(depth - 1)), (BigInt(rnd.nextInt(3) - 1), term(depth - 1))),
          rnd.nextInt(3) - 1
        )
    def atom(): Formula = rnd.nextInt(3) match
      case 0 => term(2) <= term(2)
      case 1 => term(2) === term(2)
      case _ => term(2) < term(2)
    def formula(): Formula = rnd.nextInt(3) match
      case 0 => atom()
      case 1 => Or(List(atom(), atom()))
      case _ => Implies(atom(), atom())
    sets = List.fill(10)(List.fill(n)(formula()))

  private def solver(): Solver =
    val s = Solver()
    for i <- 0 until n do s.declare(s"x$i", Nil, Sort.Int)
    s.declare("f", List(Sort.Int), Sort.Int)
    s

  @Benchmark
  def solve(): Int =
    sets.count { formulas =>
      val s = solver()
      formulas.foreach(s.assert)
      for i <- 0 until n do
        s.assert(Const(s"x$i") >= Num(-5))
        s.assert(Const(s"x$i") <= Num(5))
      s.solve() == s.Result.Sat
    }
