package io.bovel.bench.vik

import java.util.concurrent.TimeUnit

import scala.compiletime.uninitialized
import scala.util.Random

import io.bovel.vik.*
import org.openjdk.jmh.annotations.*
import io.bovel.vik.Formula.*
import io.bovel.vik.Solver
import io.bovel.vik.Term.*

/** Datatypes: random formulas over the finite datatypes `Color` (three
 *  constants) and `Pair` (two colors) with `n` pair constants, a mix of
 *  satisfiable and unsatisfiable instances (`finite`); and chains of `n` lists
 *  `l_i = cons(a_i, l_{i+1})` closed by `l_n = nil` or by `l_n = l_0`
 *  (acyclicity), with injectivity questions on their heads (`lists`).
 */
@State(Scope.Thread)
@BenchmarkMode(Array(Mode.AverageTime))
@OutputTimeUnit(TimeUnit.MILLISECONDS)
@Fork(3)
@Warmup(iterations = 5, time = 1)
@Measurement(iterations = 5, time = 1)
class AdtBench:

  @Param(Array("10", "30"))
  var n: Int = uninitialized

  val color = Datatype("Color", List("red", "green", "blue").map(Constructor(_, Nil)))
  val pair = Datatype("Pair", List(Constructor("mk", List(("fst", Sort.Named("Color")), ("snd", Sort.Named("Color"))))))
  val list = Datatype(
    "List",
    List(Constructor("nil", Nil), Constructor("cons", List(("head", Sort.Named("U")), ("tail", Sort.Named("List")))))
  )

  private var finiteFormulas: List[List[Formula]] = uninitialized
  private var listFormulas: List[(List[Formula], Boolean)] = uninitialized

  def app(f: String, args: Term*): Term = App(Const(f), args.toList)
  def is(c: String, t: Term): Formula = Pred(app(s"(_ is $c)", t))

  @Setup(Level.Trial)
  def setup(): Unit =
    val rnd = Random(1)
    val colors = List("red", "green", "blue")
    def colorTerm(): Term = rnd.nextInt(4) match
      case 0 => app("fst", pairTerm(1))
      case 1 => app("snd", pairTerm(1))
      case _ => Const(colors(rnd.nextInt(3)))
    def pairTerm(depth: Int = 2): Term = rnd.nextInt(if depth > 0 then 3 else 2) match
      case 0 | 1 => Const(s"p${rnd.nextInt(n)}")
      case _ => app("mk", colorTerm(), colorTerm())
    def atom(): Formula = rnd.nextInt(4) match
      case 0 => colorTerm() === colorTerm()
      case 1 => pairTerm() === pairTerm()
      case 2 => is(colors(rnd.nextInt(3)), colorTerm())
      case _ => Not(pairTerm() === pairTerm())
    def formula(depth: Int): Formula =
      if depth == 0 then atom()
      else
        rnd.nextInt(3) match
          case 0 => And(List(formula(depth - 1), formula(depth - 1)))
          case 1 => Or(List(formula(depth - 1), formula(depth - 1)))
          case _ => Not(formula(depth - 1))
    finiteFormulas = List.fill(10)(List.fill(n)(formula(2)))
    listFormulas = List.tabulate(10) { k =>
      val cyclic = k % 2 == 1
      val chain = List.tabulate(n)(i =>
        Const(s"l$i") === app("cons", Const(s"a$i"), Const(s"l${(i + 1) % (if cyclic then n else n + 1)}"))
      )
      val closing = if cyclic then Nil else List(Const(s"l$n") === Const("nil"))
      val heads = List.tabulate(n / 2)(i =>
        Or(List(Const(s"a$i") === Const(s"a${i + 1}"), app("head", Const(s"l$i")) !== Const(s"a$i")))
      )
      (chain ++ closing ++ heads, cyclic)
    }

  private def finiteSolver(): Solver =
    val s = Solver()
    s.declare(color)
    s.declare(pair)
    for i <- 0 until n do s.declare(s"p$i", Nil, Sort.Named("Pair"))
    s

  private def listSolver(): Solver =
    val s = Solver()
    s.declare("U", Nil, Sort.Named("U"))
    s.declare(list)
    for i <- 0 to n do
      s.declare(s"l$i", Nil, Sort.Named("List"))
      s.declare(s"a$i", Nil, Sort.Named("U"))
    s

  /** Ten random formula sets over the finite datatypes, `n` formulas each. */
  @Benchmark
  def finite(): Int =
    finiteFormulas.count { formulas =>
      val s = finiteSolver()
      formulas.foreach(s.assert)
      s.solve() == s.Result.Sat
    }

  /** Ten list chains of `n` conses, half of them cyclic (unsat). */
  @Benchmark
  def lists(): Int =
    listFormulas.count { (formulas, _) =>
      val s = listSolver()
      formulas.foreach(s.assert)
      s.solve() == s.Result.Sat
    }
