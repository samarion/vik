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

  test("arrays under a function with no integer or store around"):
    // The pass that pairs the arrays under a function or a constructor ran only beside an arithmetic term
    // or a store; and the equalities it made got their witnesses only when the same round of the passes
    // emitted a clause, which the last two scripts' rounds do not, with or without an integer (issue 133).
    def run(text: String) = Session.run(io.bovel.smtlib.Parser.parse(s"""
      (declare-const a1 (Array Bool Bool)) (declare-const a2 (Array Bool Bool))
      (declare-const a3 (Array Bool Bool)) (declare-const a4 (Array Bool Bool))
      (declare-const a5 (Array Bool Bool))
      $text
      (check-sat)"""))
    val agree = "(assert (= (select a1 true) (select a2 true))) (assert (= (select a1 false) (select a2 false)))"
    val p = "(declare-fun p ((Array Bool Bool)) Bool)"
    val f = "(declare-sort U 0) (declare-fun f ((Array Bool Bool)) U)"
    val mk = "(declare-datatype P ((mk (arr (Array Bool Bool)))))"
    assertEquals(run(s"$p (assert (distinct (p a1) (p a2))) $agree"), List("unsat"))
    assertEquals(run(s"$mk (assert (distinct (mk a1) (mk a2))) $agree"), List("unsat"))
    // Bool to Bool has four arrays: five applications cannot be distinct, four can.
    assertEquals(run(s"$mk (assert (distinct (mk a1) (mk a2) (mk a3) (mk a4) (mk a5)))"), List("unsat"))
    assertEquals(run(s"$f (assert (distinct (f a1) (f a2) (f a3) (f a4) (f a5)))"), List("unsat"))
    assertEquals(
      run(s"$f (declare-const x Int) (assert (> x 0)) (assert (distinct (f a1) (f a2) (f a3) (f a4) (f a5)))"),
      List("unsat")
    )
    assertEquals(run(s"$f (assert (distinct (f a1) (f a2) (f a3) (f a4)))"), List("sat"))

  test("theory sharing gives an array equality first used in a lemma its witness"):
    val constructor = "(declare-datatype D ((C (arr (Array Int Int)))))"
    val function = "(declare-sort U 0) (declare-fun f ((Array Int Int)) U) (declare-const i Int)"
    val cases = List(
      (constructor, "C", "(store a 0 (select a 0))"),
      (function, "f", "(store a i (select a i))"),
      (s"$constructor (declare-const v Int) (assert (= v (select a 1)))", "C", "(store a 1 v)")
    )
    for
      (setup, symbol, store) <- cases
      (left, right) <- List(("a", store), (store, "a"))
    do
      val script = s"""
        (declare-const a (Array Int Int))
        $setup
        (assert (not (= ($symbol $left) ($symbol $right))))
        (check-sat)"""
      assertEquals(Session.run(io.bovel.smtlib.Parser.parse(script)), List("unsat"), script)

  test("shared array equalities get witnesses after push and remain valid after pop"):
    val store = "(store a i (select a i))"
    val script = s"""
      (declare-sort U 0)
      (declare-const a (Array Int Bool))
      (declare-const i Int)
      (declare-fun f ((Array Int Bool)) U)
      (assert (select a 0))
      (assert (select $store 0))
      (check-sat)
      (push 1)
      (assert (not (= (f $store) (f a))))
      (check-sat)
      (pop 1)
      (push 1)
      (assert (not (= (f a) (f $store))))
      (check-sat)
      (pop 1)
      (assert (not (= (f a) (f (store a 0 false)))))
      (check-sat)"""
    assertEquals(Session.run(io.bovel.smtlib.Parser.parse(script)), List("sat", "unsat", "unsat", "sat"))

  test("store chains over the same base differ only at their write indices"):
    val script = """
      (declare-const a (Array Int (Array Bool Bool)))
      (declare-const x (Array Bool Bool))
      (declare-const y (Array Bool Bool))
      (assert (select x true))
      (assert (not (select y true)))
      (push 1)
      (assert (distinct (store (store a 0 x) 1 y) (store (store a 1 y) 0 x)))
      (check-sat)
      (pop 1)
      (assert (distinct (store (store a 0 x) 1 y) (store (store a 0 x) 1 x)))
      (check-sat)"""
    assertEquals(Session.run(io.bovel.smtlib.Parser.parse(script)), List("unsat", "sat"))

  test("an array equality shares reads that arrived in an earlier check"):
    val script = """
      (declare-const a (Array Int Int))
      (declare-const b (Array Int Int))
      (declare-const i Int)
      (declare-const j Int)
      (push 1)
      (assert (<= i j))
      (assert (<= j i))
      (assert (distinct (select a i) (select b j)))
      (check-sat)
      (push 1)
      (assert (= a b))
      (check-sat)
      (pop 1)
      (check-sat)"""
    assertEquals(Session.run(io.bovel.smtlib.Parser.parse(script)), List("sat", "unsat", "sat"))

  test("push and pop"):
    val s = Solver()
    s.assert(a === b)
    s.push()
    s.assert(a !== b)
    assertEquals(s.solve().toString, "Unsat")
    s.pop()
    assertEquals(s.solve().toString, "Sat")
    intercept[IllegalArgumentException](s.pop())

  test("model-based arithmetic equates the numeric results of congruent applications"):
    val s = Session(Solver(simplify = false))
    assertEquals(
      s.run("""
        (declare-sort U 0)
        (declare-const a U) (declare-const b U)
        (declare-fun f (U) Int)
        (assert (= a b))
        (assert (= (f a) 0))
        (assert (= (f b) 1))
        (check-sat)
      """),
      List("unsat")
    )

  test("model-based arithmetic compares linear arguments and numerals with model output off"):
    val s = Session(Solver(simplify = false))
    assertEquals(
      s.run("""
        (declare-sort U 0)
        (declare-const x Int)
        (declare-fun f (Int) U)
        (assert (= x 0))
        (assert (distinct (f (+ x 1)) (f 1)))
        (check-sat)
      """),
      List("unsat")
    )
    assert(!s.solver.produceModels)

  test("model-based arithmetic checks nested calls with mixed Boolean and integer arguments"):
    val s = Session(Solver(simplify = false), checkModels = true)
    assertEquals(
      s.run("""
        (declare-const x Int) (declare-const y Int)
        (declare-fun f (Int) Int)
        (declare-fun p (Bool Int) Bool)
        (assert (distinct x y))
        (assert (= (f x) 7))
        (assert (= (f y) 7))
        (assert (p true (f x)))
        (assert (not (p false (f y))))
        (check-sat)
        (push 1)
        (assert (not (p true (f y))))
        (check-sat)
        (pop 1)
        (check-sat)
      """),
      List("sat", "unsat", "sat")
    )

  test("model-based arithmetic can choose disequality and keep its definition across checks"):
    val s = Session(Solver(simplify = false), checkModels = true)
    assertEquals(
      s.run("""
        (declare-sort U 0)
        (declare-const a Int) (declare-const b Int)
        (declare-fun f (Int) U)
        (assert (distinct (f a) (f b)))
        (check-sat)
        (push 1)
        (assert (! (= a b) :named same))
        (check-sat)
        (get-unsat-core)
        (pop 1)
        (check-sat)
      """),
      List("sat", "unsat", "(same)", "sat")
    )

  test("model-based arithmetic encodes explicit equality before it reaches level zero"):
    val s = Solver(simplify = false)
    s.declare("a", Nil, Sort.Int)
    s.declare("b", Nil, Sort.Int)
    s.assert(a === b)
    assertEquals(s.solve(), s.Result.Sat)
    s.push()
    s.assert(b === a)
    s.assert(a <= Num(0))
    s.assert(b >= Num(1))
    assertEquals(s.solve(), s.Result.Unsat)
    s.pop()
    assertEquals(s.solve(), s.Result.Sat)

  test("model-based arithmetic combines with an array introduced between checks"):
    val s = Session(Solver(simplify = false))
    assertEquals(
      s.run("""
        (declare-const x Int)
        (assert (= x 0))
        (check-sat)
        (push 1)
        (declare-const a (Array Int Int))
        (assert (distinct (select (store a x 1) 0) 1))
        (check-sat)
        (pop 1)
        (check-sat)
      """),
      List("sat", "unsat", "sat")
    )

  test("model-based arithmetic checks the undeclared integer terms of the Solver API"):
    val s = Solver(simplify = false)
    assertEquals(s.solve(), s.Result.Sat)
    s.assert(a === b)
    s.assert(a <= Num(0))
    s.assert(b >= Num(1))
    assertEquals(s.solve(), s.Result.Unsat)

  test("an equality of undeclared terms decided before they are known as integers (issue 221)"):
    // The first check decides `a = b` for good, as an equality of the e-graph only. Its arithmetic meaning,
    // which arrives with `a ≤ 0`, has to reach the simplex all the same: as an atom's meaning it did not.
    val s = Solver(simplify = false)
    s.assert(a === b)
    assertEquals(s.solve(), s.Result.Sat)
    s.assert(a <= Num(0))
    s.assert(b >= Num(1))
    assertEquals(s.solve(), s.Result.Unsat)

  test("model-based arithmetic compares the undeclared integer arguments of an undeclared function"):
    val s = Solver(simplify = false)
    s.assert(Not(fa(a) === fa(b)))
    assertEquals(s.solve(), s.Result.Sat)
    s.assert(a <= b)
    s.assert(b <= a)
    assertEquals(s.solve(), s.Result.Unsat)

  test("model-based arithmetic compares integer arguments of a function into the reals"):
    // `x` and `y` are equal in arithmetic only: the final check finds the two rows of `f`, and splits.
    val s = Session(Solver(simplify = false), checkModels = true)
    assertEquals(
      s.run("""
        (declare-const x Int) (declare-const y Int)
        (declare-fun f (Int) Real)
        (assert (<= x y)) (assert (<= y x))
        (assert (distinct (f x) (f y)))
        (check-sat)
      """),
      List("unsat")
    )

  test("model-based arithmetic finds two datatype values apart with equal integer fields"):
    // Their values make the datatype's: equal fields are one value, against `x ≠ y`. The final check equates
    // the fields, and congruence over the constructor finds `x = y`.
    val s = Session(Solver(simplify = false), checkModels = true)
    assertEquals(
      s.run("""
        (declare-datatypes ((Pair 0)) (((mk (f1 Int) (f2 Int)))))
        (declare-const x Pair) (declare-const y Pair) (declare-const w Int)
        (assert (not (= x y)))
        (assert (= (f1 x) (f1 y)))
        (assert (= (f2 x) 0))
        (assert (= (+ (f2 y) w) 0))
        (assert (<= w 0)) (assert (<= 0 w))
        (check-sat)
      """),
      List("unsat")
    )

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

  test("a term of a range of the integers lies in the range (issues 145 and 154)"):
    val x = Const("x")
    // A declared constant, from its declaration on and below every level: no `pop` takes the range back.
    val s = Solver()
    s.push()
    s.declare("x", Nil, Sort.IntRange(0, 3))
    s.assert(x >= Num(4))
    assertEquals(s.solve(), s.Result.Unsat)
    s.pop()
    s.assert(x >= Num(3))
    assertEquals(s.solve(), s.Result.Sat)
    assertEquals(s.model().get.constants("x"), Num(3))
    // An application, when the solver first meets it.
    s.declare("f", List(Sort.Int), Sort.IntRange(0, 1))
    s.push()
    s.assert(App(Const("f"), List(x)) >= Num(2))
    assertEquals(s.solve(), s.Result.Unsat)
    s.pop()
    // The range goes with the declaration: the same name at another sort is another constant.
    s.undeclare("x")
    s.declare("x", Nil, Sort.Int)
    s.assert(x >= Num(4))
    assertEquals(s.solve(), s.Result.Sat)

  test("unknown with a reason: the fuel, or the caller"):
    val s = Solver()
    for i <- 0 until 12 do s.declare(s"p$i", Nil, Sort.Bool)
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
      s.declare("f", List(Sort.Int), Sort.Int)
      for i <- xs.indices do s.declare(s"x$i", Nil, Sort.Int)
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
