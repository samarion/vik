package io.bovel.vik

import scala.util.Random

import Formula.*
import Term.*

/** Uninterpreted functions over integers, and datatypes with integer fields:
 *  the combination of the e-graph and the LIA solver.
 */
class UfliaTest extends munit.FunSuite:
  def app(f: String, args: Term*): Term = App(Const(f), args.toList)
  val (x, y, z, a, b) = (Const("x"), Const("y"), Const("z"), Const("a"), Const("b"))
  def f(t: Term): Term = app("f", t)

  def solver(): Solver =
    val s = Solver()
    for c <- List("x", "y", "z") do s.declare(c, Nil, Sort.Int)
    s.declare("f", List(Sort.Int), Sort.Int)
    s.declare("g", List(Sort.Int, Sort.Int), Sort.Int)
    s.declare("a", Nil, Sort.Named("U"))
    s.declare("b", Nil, Sort.Named("U"))
    s.declare("h", List(Sort.Int), Sort.Named("U"))
    s

  def sat(s: Solver, formulas: Formula*): Boolean =
    formulas.foreach(s.assert)
    s.solve() == s.Result.Sat

  test("equalities flow from arithmetic to congruence"):
    assert(!sat(solver(), f(x) !== f(y), x <= y, y <= x))
    assert(sat(solver(), f(x) !== f(y), x <= y))
    assert(!sat(solver(), f(x + Num(1)) !== f(y), IntEq(y, x + Num(1))))
    assert(!sat(solver(), app("h", x) !== app("h", y), IntEq(x * 2, y * 2)))
    assert(!sat(solver(), app("g", x, y) !== app("g", y, x), x <= y, y <= x))

  test("equalities flow from congruence to arithmetic"):
    assert(!sat(solver(), x === y, f(x) < f(y)))
    assert(!sat(solver(), x === y, f(x) + Num(1) <= f(y)))
    assert(!sat(solver(), app("h", x) === a, app("h", y) === b, a !== b, IntEq(x, y)))
    assert(sat(solver(), app("h", x) === a, app("h", y) === b, a !== b, x < y))

  test("arithmetic on function values"):
    assert(!sat(solver(), f(x) === Num(3), f(x) + Num(1) <= Num(3)))
    assert(!sat(solver(), f(x) >= Num(1), f(y) <= Num(0), x === y))
    assert(sat(solver(), f(x) >= Num(1), f(y) <= Num(0), x !== y))
    assert(!sat(solver(), Not(f(x) === f(y)), f(x) <= f(y), f(y) <= f(x)))

  test("datatypes with integer fields"):
    val list =
      Datatype(
        "List",
        List(Constructor("nil", Nil), Constructor("cons", List(("head", Sort.Int), ("tail", Sort.Named("List")))))
      )
    def ls(): Solver =
      val s = Solver()
      s.declare(list)
      s.declare("l", Nil, Sort.Named("List"))
      s.declare("m", Nil, Sort.Named("List"))
      s.declare("x", Nil, Sort.Int)
      s
    val (l, m, nil) = (Const("l"), Const("m"), Const("nil"))
    def is(c: String, t: Term): Formula = Pred(app(s"(_ is $c)", t))
    assert(!sat(ls(), l === app("cons", Num(3), nil), app("head", l) < Num(2)))
    assert(!sat(ls(), l === app("cons", x, nil), m === app("cons", x + Num(1), nil), l === m))
    assert(sat(ls(), l === app("cons", x, nil), m === app("cons", x + Num(1), nil), l !== m))
    assert(!sat(ls(), is("cons", l), app("head", l) >= Num(5), l === app("cons", Num(4), m)))
    assert(sat(ls(), is("cons", l), app("head", l) >= Num(5)))

  /** Random formulas over `x`, `y` in `[-1, 1]` and `f : Int -> Int` with
   *  values in `[-1, 1]`, decided by brute force over the 9 assignments and the
   *  27 functions.
   */
  test("random formulas against brute force"):
    val rnd = Random(21)
    def intTerm(): Term = rnd.nextInt(5) match
      case 0 => x
      case 1 => y
      case 2 => f(intTerm())
      case 3 => Num(rnd.nextInt(3) - 1)
      case _ => Term.linear(List((BigInt(1), intTerm()), (BigInt(rnd.nextInt(3) - 1), intTerm())), rnd.nextInt(3) - 1)
    def atom(): Formula = rnd.nextInt(3) match
      case 0 => intTerm() <= intTerm()
      case 1 => intTerm() === intTerm()
      case _ => intTerm() < intTerm()
    def formula(depth: Int): Formula =
      if depth == 0 then atom()
      else
        rnd.nextInt(4) match
          case 0 => And(List(formula(depth - 1), formula(depth - 1)))
          case 1 => Or(List(formula(depth - 1), formula(depth - 1)))
          case 2 => Not(formula(depth - 1))
          case _ => Implies(formula(depth - 1), formula(depth - 1))
    val values = List(-1, 0, 1).map(BigInt(_))
    val functions = for a <- values; b <- values; c <- values yield Map(BigInt(-1) -> a, BigInt(0) -> b, BigInt(1) -> c)
    def eval(t: Term, vx: BigInt, vy: BigInt, fn: Map[BigInt, BigInt]): Option[BigInt] = t match
      case Const("x") => Some(vx)
      case Const("y") => Some(vy)
      case Num(v) => Some(v)
      case Linear(terms, c) =>
        val parts = terms.map((k, u) => eval(u, vx, vy, fn).map(_ * k))
        if parts.forall(_.isDefined) then Some(parts.flatten.sum + c) else None
      case App(Const("f"), List(u)) => eval(u, vx, vy, fn).flatMap(v => fn.get(v)) // outside [-1, 1]: no value
      case _ => None
    def holds(g: Formula, vx: BigInt, vy: BigInt, fn: Map[BigInt, BigInt]): Option[Boolean] = g match
      case Le(l, r) => for a <- eval(l, vx, vy, fn); b <- eval(r, vx, vy, fn) yield a <= b
      case Eq(l, r) => for a <- eval(l, vx, vy, fn); b <- eval(r, vx, vy, fn) yield a == b
      case Not(h) => holds(h, vx, vy, fn).map(!_)
      case And(hs) => hs.map(holds(_, vx, vy, fn)).foldLeft(Option(true))((acc, o) => for p <- acc; q <- o yield p && q)
      case Or(hs) => hs.map(holds(_, vx, vy, fn)).foldLeft(Option(false))((acc, o) => for p <- acc; q <- o yield p || q)
      case Implies(h, k) => for p <- holds(h, vx, vy, fn); q <- holds(k, vx, vy, fn) yield !p || q
      case _ => None
    var checked = 0
    var sats = 0
    for round <- 0 until 150 do
      val g = formula(2)
      // The brute force is complete only when every function value used lies in [-1, 1]: skip formulas that
      // apply f outside the box under some assignment.
      val outcomes = for vx <- values; vy <- values; fn <- functions yield holds(g, vx, vy, fn)
      if outcomes.forall(_.isDefined) then
        val expected = outcomes.exists(_.contains(true))
        val s = solver()
        val bounds = List(
          x >= Num(-1),
          x <= Num(1),
          y >= Num(-1),
          y <= Num(1),
          f(x) >= Num(-1),
          f(x) <= Num(1),
          f(y) >= Num(-1),
          f(y) <= Num(1)
        )
        val fRange = List(f(Num(-1)), f(Num(0)), f(Num(1))).flatMap(t => List(t >= Num(-1), t <= Num(1)))
        // Every application in the formula is bounded too, so that the solver's models are the brute force's.
        def apps(t: Term): List[Term] = t match
          case a @ App(_, args) => a :: args.flatMap(apps)
          case Linear(terms, _) => terms.flatMap((_, u) => apps(u))
          case _ => Nil
        def appsOf(h: Formula): List[Term] = h match
          case Le(l, r) => apps(l) ++ apps(r)
          case Eq(l, r) => apps(l) ++ apps(r)
          case Not(h) => appsOf(h)
          case And(hs) => hs.flatMap(appsOf)
          case Or(hs) => hs.flatMap(appsOf)
          case Implies(h, k) => appsOf(h) ++ appsOf(k)
          case _ => Nil
        val nested = (List(f(f(x)), f(f(y))) ++ appsOf(g)).distinct.flatMap(t => List(t >= Num(-1), t <= Num(1)))
        assertEquals(sat(s, (g :: bounds ++ fRange ++ nested)*), expected, s"round $round: $g")
        checked += 1
        if expected then sats += 1
    assert(checked > 60 && sats > 10 && sats < checked, (checked, sats))
