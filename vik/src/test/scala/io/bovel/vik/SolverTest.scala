package io.bovel.vik

import Formula.*
import Term.*

class SolverTest extends munit.FunSuite:
  val a = Const("a")
  val b = Const("b")
  val c = Const("c")
  val f = Const("f")
  def fa(t: Term) = App(f, List(t))
  def p(t: Term) = Pred(App(Const("p"), List(t)))

  def solve(formulas: Formula*): Solver#Result =
    val s = Solver()
    for f <- formulas do s.assert(f)
    s.solve()

  def isSat(formulas: Formula*): Boolean = solve(formulas*) match
    case r: Solver#Result => r.toString == "Sat"

  test("trivial"):
    assert(isSat())
    assert(isSat(True))
    assert(!isSat(False))
    assert(isSat(a === b))
    assert(!isSat(a === b, a !== b))

  test("transitivity and congruence"):
    assert(!isSat(a === b, b === c, a !== c))
    assert(!isSat(a === b, fa(a) !== fa(b)))
    assert(isSat(a === b, fa(a) !== fa(c)))
    assert(!isSat(a === b, p(a), !p(b)))

  test("boolean structure"):
    assert(isSat((a === b) || (b === c), a !== c, a !== b, (b === c) && (a !== c)))
    assert(!isSat((a === b) || (b === c), a !== b, b !== c))
    assert(isSat((a === b) ==> (fa(a) === fa(b))))
    assert(!isSat(Not((a === b) ==> (fa(a) === fa(b)))))
    assert(isSat(Ite(a === b, fa(a) === c, fa(b) === c)))
    assert(!isSat((a === b) <=> (a !== b)))

  test("diamonds"):
    // x0 = xn through n diamonds, each x_i = y_i = x_{i+1} or x_i = z_i = x_{i+1}; then x0 != xn.
    val n = 6
    val x = Array.tabulate(n + 1)(i => Const(s"x$i"))
    val diamonds = (0 until n).map { i =>
      val y = Const(s"y$i")
      val z = Const(s"z$i")
      ((x(i) === y) && (y === x(i + 1))) || ((x(i) === z) && (z === x(i + 1)))
    }
    assert(isSat(diamonds*))
    assert(!isSat((diamonds :+ (x(0) !== x(n)))*))

  test("arrays equal by extensionality under a function"):
    // Two arrays met only as the arguments of a function into an uninterpreted sort, into Bool, into an
    // array: equal by extensionality, so are the applications (issue 39).
    def run(text: String) = Session.run(io.bovel.smtlib.Parser.parse(s"""
      (declare-sort U 0)
      (declare-const a (Array Int Int)) (declare-const b (Array Int Int))
      (declare-fun f ((Array Int Int)) U) (declare-fun p ((Array Int Int)) Bool)
      (declare-fun g ((Array Int Int)) (Array Int Int))
      (assert (= a (store b 0 (select b 0))))
      $text
      (check-sat)"""))
    assertEquals(run("(assert (not (= (f a) (f b))))"), List("unsat"))
    assertEquals(run("(assert (not (= (p a) (p b))))"), List("unsat"))
    assertEquals(run("(assert (not (= (select (g a) 1) (select (g b) 1))))"), List("unsat"))
    assertEquals(run("(assert (= (f a) (f b)))"), List("sat"))

  test("push and pop"):
    val s = Solver()
    s.assert(a === b)
    s.push()
    s.assert(a !== b)
    assertEquals(s.solve().toString, "Unsat")
    s.pop()
    assertEquals(s.solve().toString, "Sat")
    intercept[IllegalArgumentException](s.pop())

  test("random formulas over predicates agree with brute force"):
    val rnd = scala.util.Random(9)
    val ps = Array.tabulate(5)(i => Pred(Const(s"q$i")))
    def random(depth: Int): Formula =
      if depth == 0 then ps(rnd.nextInt(ps.length))
      else
        rnd.nextInt(6) match
          case 0 => Not(random(depth - 1))
          case 1 => And(List.fill(2 + rnd.nextInt(2))(random(depth - 1)))
          case 2 => Or(List.fill(2 + rnd.nextInt(2))(random(depth - 1)))
          case 3 => Implies(random(depth - 1), random(depth - 1))
          case 4 => Iff(random(depth - 1), random(depth - 1))
          case _ => Ite(random(depth - 1), random(depth - 1), random(depth - 1))
    def eval(f: Formula, m: Array[Boolean]): Boolean = f match
      case True => true
      case False => false
      case Not(g) => !eval(g, m)
      case And(gs) => gs.forall(eval(_, m))
      case Or(gs) => gs.exists(eval(_, m))
      case Implies(l, r) => !eval(l, m) || eval(r, m)
      case Iff(l, r) => eval(l, m) == eval(r, m)
      case Ite(c, t, e) => if eval(c, m) then eval(t, m) else eval(e, m)
      case Pred(Const(name)) => m(name.drop(1).toInt)
      case _ => throw IllegalArgumentException(f.toString)
    var sats = 0
    for _ <- 0 until 200 do
      val formulas = List.fill(1 + rnd.nextInt(3))(random(3))
      val expected = (0 until 32).exists(bits =>
        formulas.forall(eval(_, Array.tabulate(5)(i => (bits & (1 << i)) != 0)))
      )
      assertEquals(isSat(formulas*), expected, formulas.toString)
      if expected then sats += 1
    assert(sats > 50)

  test("simplifier: constants local to a conjunction are eliminated"):
    val y = Const("y")
    val z = Const("z")
    val diamond = ((a === y) && (y === b)) || ((a === z) && (z === b))
    assertEquals(Simplifier.simplify(List(diamond))._1, List((a === b) || (a === b)))
    // Not when the constant escapes the conjunction (`a !== c` and `b !== c` pin `a` and `b`).
    val pinned = List(a !== c, b !== c)
    assertEquals(
      Simplifier.simplify(((a === y) && (y === b)) :: (y !== c) :: pinned)._1,
      ((a === y) && (y === b)) :: (y !== c) :: pinned
    )
    // `y = f(y)` cannot define `y`, but `y = b` can: `y` is local and becomes `b`.
    assertEquals(Simplifier.simplify(((y === fa(y)) && (y === b)) :: pinned)._1, (b === fa(b)) :: pinned)
    // A conjunction reduced to nothing is dropped.
    assertEquals(Simplifier.simplify(List(And(List(y === a))))._1, Nil)

  test("simplifier: random EUF formulas keep their satisfiability"):
    val rnd = scala.util.Random(13)
    val consts = Array.tabulate(12)(i => Const(s"k$i"))
    val g = Const("g")
    def term(depth: Int): Term =
      if depth == 0 || rnd.nextInt(3) == 0 then consts(rnd.nextInt(consts.length))
      else App(g, List(term(depth - 1)))
    def formula(depth: Int): Formula =
      if depth == 0 then if rnd.nextBoolean() then term(2) === term(2) else term(2) !== term(2)
      else
        rnd.nextInt(4) match
          case 0 => Not(formula(depth - 1))
          case 1 => And(List.fill(2 + rnd.nextInt(2))(formula(depth - 1)))
          case 2 => Or(List.fill(2 + rnd.nextInt(2))(formula(depth - 1)))
          case _ => Implies(formula(depth - 1), formula(depth - 1))
    var simplifiedSomething = 0
    for _ <- 0 until 300 do
      val formulas = List.fill(1 + rnd.nextInt(3))(formula(3))
      if Simplifier.simplify(formulas)._1 != formulas then simplifiedSomething += 1
      val plain = Solver(simplify = false)
      val simplified = Solver()
      for f <- formulas do
        plain.assert(f)
        simplified.assert(f)
      assertEquals(simplified.solve().toString, plain.solve().toString, formulas.toString)
    assert(
      simplifiedSomething > 5,
      s"only $simplifiedSomething simplified"
    ) // elimination applies in positive positions only

  test("unknown with a reason: the fuel, or the caller"):
    val s = Solver()
    for i <- 0 until 12 do s.declare(s"p$i", Nil, "Bool")
    val ps = (0 until 12).map(i => Pred(Const(s"p$i"))).toList
    s.assert(Or(ps))
    for (a, i) <- ps.zipWithIndex; b <- ps.drop(i + 1) do s.assert(Or(List(Not(a), Not(b))))
    assertEquals(s.solve(fuel = 1), s.Result.Unknown(s.Reason.Fuel))
    assertEquals(s.solve(() => false), s.Result.Unknown(s.Reason.Stopped))
    assertEquals(s.solve(), s.Result.Sat)

  test("a solve stopped inside the encoding answers unknown, and the next one answers"):
    // Not on Scala Native: its debug-mode test binary takes about 50 s here, against 5 s on the JVM and munit's
    // 30 s limit. Nothing in it is specific to a platform, and the JVM and Scala.js run it.
    assume(System.getProperty("java.vm.name") != "Scala Native", "slow on Scala Native's debug-mode test binary")
    // Forty-eight integers a cycle of bounds makes equal, and two of their images apart: unsat only with
    // the sharing atom of every pair of them, which a pass stopped part-way has noted and not yet encoded.
    // `keepGoing` says no at its n-th asking, for every n the encoding has: in the first encoding, between
    // two rounds of the passes, inside one.
    val xs = (0 until 48).map(i => Const(s"x$i")).toList
    def problem(): Solver =
      val s = Solver()
      s.declare("f", List("Int"), "Int")
      for i <- xs.indices do s.declare(s"x$i", Nil, "Int")
      for (x, y) <- xs.zip(xs.tail :+ xs.head) do s.assert(Le(x, y))
      s.assert(Or(for (x, i) <- xs.zipWithIndex; y <- xs.drop(i + 1) yield fa(x) !== fa(y)))
      s
    assertEquals(problem().solve().toString, "Unsat")
    for n <- 0 to 10 do
      val s = problem()
      var asked = 0
      val stopped = s.solve { () =>
        asked += 1; asked <= n
      }
      assertEquals(stopped, s.Result.Unknown(s.Reason.Stopped), s"stopped at asking $n")
      assertEquals(s.solve(), s.Result.Unsat, s"after a stop at asking $n")

  test("an equality an application lemma encoded first gets its witness when the problem negates it") {
    // The first check encodes `a = (store a 1 (select a 1))` for the lemma on `(select a 0)`, with no
    // witness; the assertion after it found the literal made, and the second check was sat.
    assertEquals(
      Session.run(io.bovel.smtlib.Parser.parse(
        """(declare-fun a () (Array Int Bool))
          |(assert (select (store a 1 (select a 1)) 0)) (assert (select a 0)) (check-sat)
          |(assert (not (= a (store a 1 (select a 1))))) (check-sat)""".stripMargin
      )),
      List("sat", "unsat")
    )
  }

  test("constant arrays") {
    def play(script: String) = Session.run(io.bovel.smtlib.Parser.parse(script))
    val decls = "(declare-const a (Array Int Int)) (declare-const b (Array Int Int)) (declare-const i Int)"
    // The value at every index
    assertEquals(
      play(s"$decls (assert (= a ((as const (Array Int Int)) 0))) (assert (= (select a i) 1)) (check-sat)"),
      List("unsat")
    )
    // Under a store: the written index alone differs
    assertEquals(
      play(
        s"$decls (assert (= a (store ((as const (Array Int Int)) 0) 3 1))) (assert (= (select a i) 1)) (assert (distinct i 3)) (check-sat)"
      ),
      List("unsat")
    )
    assertEquals(
      play(s"$decls (assert (= a (store ((as const (Array Int Int)) 0) 3 1))) (assert (= (select a i) 1)) (check-sat)"),
      List("sat")
    )
    // Two constant arrays are equal when their values are, with no index read
    assertEquals(
      play(
        s"$decls (assert (= a ((as const (Array Int Int)) 0))) (assert (= b ((as const (Array Int Int)) 1))) (assert (= a b)) (check-sat)"
      ),
      List("unsat")
    )
    // and finitely many stores do not make one of the other
    assertEquals(
      play(
        s"$decls (assert (= ((as const (Array Int Int)) 1) (store ((as const (Array Int Int)) 0) i 1))) (check-sat)"
      ),
      List("unsat")
    )
    // A set, as Stainless writes it
    assertEquals(
      play(
        "(declare-const s (Array Int Bool)) (declare-const x Int) (assert (= s (store ((as const (Array Int Bool)) false) 1 true))) (assert (select s x)) (assert (distinct x 1)) (check-sat)"
      ),
      List("unsat")
    )
    // Refused over a sort a script's stores can cover
    intercept[io.bovel.smtlib.Smt2Error] {
      play("(declare-const s (Array Bool Int)) (assert (= s ((as const (Array Bool Int)) 0))) (check-sat)")
    }
  }
