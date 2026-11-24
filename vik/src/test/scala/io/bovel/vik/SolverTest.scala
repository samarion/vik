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
    // Over a finite sort: an index beyond the writes while the stores leave one, every value once they
    // may fill the sort. Two writes cover `Bool`; four cover a `(_ BitVec 2)`, three do not; and two
    // constant arrays of different values differ at an index two writes leave (z3test's
    // const_array_store_chain_unsat).
    assertEquals(
      play(
        "(declare-const s (Array Bool Int)) (assert (= s (store (store ((as const (Array Bool Int)) 0) true 1) false 1))) (assert (= s ((as const (Array Bool Int)) 1))) (check-sat)"
      ),
      List("sat")
    )
    assertEquals(
      play(
        "(declare-const s (Array Bool Int)) (assert (= s (store ((as const (Array Bool Int)) 0) true 1))) (assert (= s ((as const (Array Bool Int)) 1))) (check-sat)"
      ),
      List("unsat")
    )
    def filled(n: Int, width: Int) = (0 until n).foldLeft(s"((as const (Array (_ BitVec $width) Int)) 0)")((a, k) =>
      s"(store $a (_ bv$k $width) 1)"
    )
    assertEquals(
      play(s"(assert (= ${filled(3, 2)} ((as const (Array (_ BitVec 2) Int)) 1))) (check-sat)"),
      List("unsat")
    )
    assertEquals(play(s"(assert (= ${filled(4, 2)} ((as const (Array (_ BitVec 2) Int)) 1))) (check-sat)"), List("sat"))
    // Indices the search may make equal leave room for the index beyond them
    assertEquals(
      play(
        "(declare-const i (_ BitVec 2)) (declare-const j (_ BitVec 2)) (declare-const k (_ BitVec 2)) (declare-const l (_ BitVec 2)) " +
          "(assert (= (store (store (store (store ((as const (Array (_ BitVec 2) Int)) 0) i 1) j 1) k 1) l 1) ((as const (Array (_ BitVec 2) Int)) 1))) " +
          "(check-sat) (assert (= i j)) (check-sat)"
      ),
      List("sat", "unsat")
    )
    assertEquals(
      play(
        "(declare-const x (_ BitVec 8)) (declare-const y (_ BitVec 8)) (declare-const i (_ BitVec 2)) (declare-const j (_ BitVec 2)) " +
          "(assert (distinct x y)) (assert (= (store ((as const (Array (_ BitVec 2) (_ BitVec 8))) x) i x) (store ((as const (Array (_ BitVec 2) (_ BitVec 8))) y) j y))) (check-sat)"
      ),
      List("unsat")
    )
    // A 12-bit sort, which was refused: neither small nor large enough for one of the two alone
    assertEquals(
      play(s"(assert (= ${filled(5, 12)} ((as const (Array (_ BitVec 12) Int)) 1))) (check-sat)"),
      List("unsat")
    )
  }

  test("integer division and remainder by a numeral, and the absolute value") {
    def play(script: String) = Session.run(io.bovel.smtlib.Parser.parse(
      "(declare-fun x () Int) (declare-fun y () Int) " + script
    ))
    assertEquals(
      play(
        "(assert (= y (div x 2))) (assert (= (mod x 2) 1)) (assert (= (abs x) 7)) (assert (< x 0)) (check-sat) " +
          "(get-value (x y (div x (- 2)) (mod x (- 2)) (abs y)))"
      ),
      List("sat", "((x (- 7)) (y (- 4)) ((div x (- 2)) 4) ((mod x (- 2)) 1) ((abs y) 4))")
    )
    assertEquals(play("(assert (not (= x (+ (* 3 (div x 3)) (mod x 3))))) (check-sat)"), List("unsat"))
    assertEquals(play("(assert (or (< (mod x (- 3)) 0) (> (mod x (- 3)) 2))) (check-sat)"), List("unsat"))
    assertEquals(play("(assert (not (= (abs x) (abs (- x))))) (check-sat)"), List("unsat"))
    assertEquals(play("(assert (= (div x 2) (div (+ x 1) 2))) (assert (= (mod x 2) 1)) (check-sat)"), List("unsat"))
  }

  test("the maps of arrays, of any operator") {
    def play(script: String) = Session.run(io.bovel.smtlib.Parser.parse(
      "(define-sort B () (Array Int Int)) (declare-fun a () B) (declare-fun b () B) (declare-fun c () B) " +
        "(declare-fun i () Int) (declare-fun f (Int Int) Int) " +
        "(define-fun mx ((x Int) (y Int)) Int (ite (< x y) y x)) " + script
    ))
    // The sum of bags, with z3's sorted operator; the value is the model's.
    assertEquals(
      play(
        "(assert (= c ((_ map (+ (Int Int) Int)) a b))) (assert (= (select a 3) 2)) (assert (= (select b 3) 5)) " +
          "(check-sat) (get-value ((select c 3))) (assert (not (= (select c 3) 7))) (check-sat)"
      ),
      List("sat", "(((select c 3) 7))", "unsat")
    )
    assertEquals(play("(assert (not (= ((_ map +) a b) ((_ map +) b a)))) (check-sat)"), List("unsat"))
    assertEquals(play("(assert (not (= ((_ map +) a ((as const B) 0)) a))) (check-sat)"), List("unsat"))
    assertEquals(play("(assert (not (= ((_ map -) a a) ((as const B) 0)))) (check-sat)"), List("unsat"))
    // To another element sort, of a declared function, of a defined one.
    assertEquals(
      play("(assert (select ((_ map <=) a b) i)) (assert (> (select a i) (select b i))) (check-sat)"),
      List("unsat")
    )
    assertEquals(
      play("(assert (not (= (select ((_ map f) a b) i) (f (select a i) (select b i))))) (check-sat)"),
      List("unsat")
    )
    assertEquals(play("(assert (< (select ((_ map mx) a b) i) (select a i))) (check-sat)"), List("unsat"))
    assertEquals(
      play("(assert (= ((_ map mx) a b) a)) (assert (> (select b i) (select a i))) (check-sat)"),
      List("unsat")
    )
    assertEquals(
      play("(assert (= ((_ map mx) a b) a)) (assert (= (select b i) (select a i))) (check-sat)"),
      List("sat")
    )
    // Arrays of different element sorts, and bit-vector elements.
    assertEquals(
      play(
        "(declare-fun s () (Array Int Bool)) (assert (select s i)) " +
          "(assert (not (= (select ((_ map ite) s a b) i) (select a i)))) (check-sat)"
      ),
      List("unsat")
    )
    assertEquals(
      play(
        "(declare-fun v () (Array Int (_ BitVec 8))) (declare-fun w () (Array Int (_ BitVec 8))) " +
          "(assert (= (select ((_ map bvadd) v w) i) #x00)) (assert (= (select v i) #xff)) (check-sat) " +
          "(assert (not (= (select w i) #x01))) (check-sat)"
      ),
      List("sat", "unsat")
    )
  }

  test("the difference of bags, as Inox writes it") {
    // `max(0, a - b)` at every index: `(d + |d|) div 2` for the difference `d`, the 2 a constant array.
    def play(script: String) = Session.run(io.bovel.smtlib.Parser.parse(
      "(define-sort B () (Array Int Int)) (declare-fun a () B) (declare-fun b () B) (declare-fun i () Int) " +
        "(define-fun diff ((x B) (y B)) B (let ((d ((_ map (- (Int Int) Int)) x y))) " +
        "((_ map (div (Int Int) Int)) ((_ map (+ (Int Int) Int)) d ((_ map (abs (Int) Int)) d)) ((as const B) 2)))) " +
        script
    ))
    assertEquals(
      play(
        "(push 1) (assert (< (select (diff a b) i) 0)) (check-sat) (pop 1) " +
          "(push 1) (assert (>= (select a i) (select b i))) " +
          "(assert (not (= (select (diff a b) i) (- (select a i) (select b i))))) (check-sat) (pop 1) " +
          "(assert (= (select a i) 5)) (assert (= (select b i) 2)) (assert (= (select (diff a b) i) 3)) (check-sat) " +
          "(get-value ((select (diff a b) i) (select (diff b a) i)))"
      ),
      List("unsat", "unsat", "sat", "(((select (diff a b) i) 3) ((select (diff b a) i) 0))")
    )
    assertEquals(play("(assert (not (= (diff a a) ((as const B) 0)))) (check-sat)"), List("unsat"))
  }

  test("the Boolean maps of arrays") {
    def play(script: String) = Session.run(io.bovel.smtlib.Parser.parse(
      "(define-sort S () (Array Int Bool)) (declare-fun a () S) (declare-fun b () S) (declare-fun c () S) " +
        "(declare-fun x () Int) (define-fun empty () S ((as const S) false)) " + script + " (check-sat)"
    ))
    assertEquals(
      play("(assert (= c ((_ map or) a b))) (assert (select a x)) (assert (not (select c x)))"),
      List("unsat")
    )
    assertEquals(play("(assert (not (= ((_ map or) a b) ((_ map or) b a))))"), List("unsat"))
    assertEquals(play("(assert (= ((_ map or) a b) empty)) (assert (not (= a empty)))"), List("unsat"))
    assertEquals(play("(assert (= ((_ map and) a ((_ map not) a)) c)) (assert (not (= c empty)))"), List("unsat"))
    assertEquals(
      play("(assert (= ((_ map implies) a b) ((as const S) true))) (assert (select a x)) (assert (not (select b x)))"),
      List("unsat")
    )
    assertEquals(
      play(
        "(assert (= c ((_ map or) a (store empty 3 true)))) (assert (not (select a 3))) (assert (= b ((_ map and) c ((_ map not) a))))"
      ),
      List("sat")
    )
  }

  test("a constant array or a map over any finite sort is read at its every value once the writes may fill it") {
    def play(script: String) = Session.run(io.bovel.smtlib.Parser.parse(script))
    val record = "(declare-datatypes ((R 0)) (((mk (fld (_ BitVec 1)))))) "
    val colors = "(declare-datatypes ((C 0)) (((r) (g) (b)))) "
    val f = "(define-fun f () (Array Bool Bool) ((as const (Array Bool Bool)) false)) "
    def filled(sort: String, indices: List[String]) =
      indices.foldLeft(s"((as const (Array $sort Int)) 0)")((a, i) => s"(store $a $i 1)")
    def isOne(sort: String, indices: List[String]) =
      s"(assert (= ${filled(sort, indices)} ((as const (Array $sort Int)) 1))) (check-sat)"
    val boolArrays = List("f", "((as const (Array Bool Bool)) true)", "(store f true true)", "(store f false true)")
    // Writes at every value: satisfiable (cvc5), and were answered `unsat` while these sorts passed for
    // infinite. A value left: unsatisfiable (cvc5; z3 4.15.1 answers `sat`).
    assertEquals(play(record + isOne("R", List("(mk #b0)", "(mk #b1)"))), List("sat"))
    assertEquals(play(record + isOne("R", List("(mk #b0)"))), List("unsat"))
    assertEquals(play(f + isOne("(Array Bool Bool)", boolArrays)), List("sat"))
    assertEquals(play(f + isOne("(Array Bool Bool)", boolArrays.take(3))), List("unsat"))
    assertEquals(play(colors + isOne("C", List("r", "g", "b"))), List("sat"))
    assertEquals(play(colors + isOne("C", List("r", "g"))), List("unsat"))
    assertEquals(
      play(
        "(declare-datatypes ((U 0)) (((u)))) (assert (= (store ((as const (Array (Array Int U) Int)) 0) ((as const (Array Int U)) u) 1) " +
          "((as const (Array (Array Int U) Int)) 1))) (check-sat)"
      ),
      List("sat")
    )
    // Values of several constructors: 1 + 2 + 2 of them
    val mixed = "(declare-datatypes ((D 0)) (((a) (b (p Bool)) (c (q (_ BitVec 1)))))) "
    val ds = List("a", "(b true)", "(b false)", "(c #b0)", "(c #b1)")
    assertEquals(play(mixed + isOne("D", ds)), List("sat"))
    assertEquals(play(mixed + isOne("D", ds.init)), List("unsat"))
    // Indices the search may make equal, and a read at another index of the sort
    assertEquals(
      play(
        record + "(declare-const i R) (declare-const j R) " + isOne("R", List("i", "j")) +
          " (push 1) (assert (= i j)) (check-sat) (pop 1) (assert (distinct i j)) (check-sat)"
      ),
      List("sat", "unsat", "sat")
    )
    assertEquals(
      play(
        colors + "(declare-const a (Array C Int)) (declare-const x C) " +
          "(assert (= a (store (store (store ((as const (Array C Int)) 0) r 1) g 2) b 3))) (assert (> (select a x) 3)) (check-sat)"
      ),
      List("unsat")
    )
    // A map
    assertEquals(
      play(
        colors + "(declare-const s (Array C Bool)) (declare-const t (Array C Bool)) " +
          "(assert (= ((_ map or) s t) ((as const (Array C Bool)) true))) (assert (not (select s r))) (assert (not (select t g))) " +
          "(check-sat) (assert (not (select s b))) (assert (not (select t b))) (check-sat)"
      ),
      List("sat", "unsat")
    )
    assertEquals(
      play(
        f + "(declare-const a (Array (Array Bool Bool) Int)) " +
          s"(assert (= a ${filled("(Array Bool Bool)", boolArrays)})) " +
          "(assert (= ((_ map (+ (Int Int) Int)) a ((as const (Array (Array Bool Bool) Int)) 1)) ((as const (Array (Array Bool Bool) Int)) 2))) (check-sat)"
      ),
      List("sat")
    )
    // A recursive datatype and an uninterpreted sort have room beyond any writes
    assertEquals(
      play(
        "(declare-datatypes ((L 0)) (((nil) (cons (hd Bool) (tl L))))) " + isOne("L", List("nil", "(cons true nil)"))
      ),
      List("unsat")
    )
    assertEquals(play("(declare-sort U 0) (declare-const u U) " + isOne("U", List("u"))), List("unsat"))
  }

  test("a map over a Boolean index is read at both values") {
    def play(script: String) = Session.run(io.bovel.smtlib.Parser.parse(script))
    assertEquals(play("(declare-const a (Array Bool Bool)) (assert (= a ((_ map not) a))) (check-sat)"), List("unsat"))
    assertEquals(
      play(
        "(declare-const a (Array Bool Bool)) (declare-const b (Array Bool Bool)) (assert (= b ((_ map not) a))) (assert (select a true)) (assert (select b false)) (check-sat)"
      ),
      List("sat")
    )
  }

  test("a map's operator as it stands where the map is") {
    def play(script: String) = Session.run(io.bovel.smtlib.Parser.parse(script))
    // A constant that only the operator mentions is not the simplifier's to eliminate.
    assertEquals(
      play(
        """(declare-const t (Array Int Bool)) (declare-const u (Array Int Bool)) (declare-const a (Array Int Bool))
          |(define-fun g ((x Bool)) Bool (and x (select t 7)))
          |(assert (and (= t u) (select u 7))) (assert (select a 0)) (assert (not (select ((_ map g) a) 0)))
          |(check-sat)""".stripMargin
      ),
      List("unsat")
    )
    // A macro defined anew after a `pop` is a new operator.
    assertEquals(
      play(
        """(declare-const a (Array Int Int))
          |(push 1) (define-fun h ((x Int)) Int (+ x 1)) (define-fun g ((x Int)) Int (h x))
          |(assert (= (select ((_ map g) a) 0) 0)) (pop 1)
          |(define-fun h ((x Int)) Int (+ x 2)) (define-fun g ((x Int)) Int (h x))
          |(assert (not (= (select ((_ map g) a) 0) (+ (select a 0) 2)))) (check-sat)""".stripMargin
      ),
      List("unsat")
    )
    // A bit-vector operation of each width is its own.
    assertEquals(
      play(
        """(declare-const a (Array Int (_ BitVec 8))) (declare-const b (Array Int (_ BitVec 16)))
          |(assert (= (select ((_ map bvnot) a) 0) #x00)) (assert (= (select b 0) #x0001))
          |(assert (= (select ((_ map bvnot) b) 0) #x00fe)) (check-sat)""".stripMargin
      ),
      List("unsat")
    )
    // Over constant arrays of numerals only, the operator's own constants are constants.
    assertEquals(
      play(
        """(declare-const p Bool) (declare-const c (Array Int Int)) (define-fun g ((x Int)) Int (ite p x 0))
          |(assert (= c ((_ map g) ((as const (Array Int Int)) 1)))) (assert (= (select c 0) 1)) (check-sat)
          |(assert (not p)) (check-sat)""".stripMargin
      ),
      List("sat", "unsat")
    )
    // A write at a fixed index of an element that is an array.
    assertEquals(
      play(
        """(declare-const f (Array Int (Array Int Int))) (declare-const c (Array Int (Array Int Int)))
          |(define-fun g ((x (Array Int Int))) (Array Int Int) (store x 0 1))
          |(assert (= c ((_ map g) f))) (assert (= (select (select c 3) 0) 2)) (check-sat)""".stripMargin
      ),
      List("unsat")
    )
    // A read at an element is refused: its instances would make indices without end.
    for operator <- List("g", "(select ((Array Int Int) Int) Int)") do
      intercept[io.bovel.smtlib.Unsupported](play(
        s"""(declare-const f (Array Int (Array Int Int))) (declare-const a (Array Int Int))
           |(declare-const b (Array Int Int)) (declare-const c (Array Int Int))
           |(define-fun g ((x Int)) Int (select b x))
           |(assert (= c ${if operator == "g" then "((_ map g) a)" else s"((_ map $operator) f a)"}))
           |(assert (= (select c 0) 5)) (check-sat)""".stripMargin
      ))
  }

  test("a map over arrays of arrays, of the sort of their elements, read at a fixed index") {
    // A witness between two element arrays is an index the map is read at, whose element there is
    // another array: the lemmas' equalities between elements get none until the final check asks.
    def play(script: String) = Session.run(io.bovel.smtlib.Parser.parse(
      """(declare-const f (Array Int (Array Int Int))) (declare-const c (Array Int Int))
        |(define-fun g ((x (Array Int Int))) Int (select x 0)) (assert (= c ((_ map g) f)))""".stripMargin + script
    ))
    assertEquals(play("(assert (not (= (select c 1) (select (select f 1) 0)))) (check-sat)"), List("unsat"))
    assertEquals(
      play(
        "(assert (= (select c 1) (select (select f 1) 0))) (assert (not (= (select f 1) (select f 2)))) (check-sat)"
      ),
      List("sat")
    )
    assertEquals(
      play(
        """(assert (= f (store ((as const (Array Int (Array Int Int))) ((as const (Array Int Int)) 5))
          |  1 ((as const (Array Int Int)) 7))))
          |(assert (or (not (= (select c 1) 7)) (not (= (select c 2) 5)))) (check-sat)""".stripMargin
      ),
      List("unsat")
    )
  }

  test("two arrays under a function, whose equality a lemma made first") {
    // The final check gives the two their equality atom and its witness, whoever encoded the
    // equality first: an application lemma (`a = s`) or a store's read-over-write (`s[j] = a[j]`).
    def play(script: String) = Session.run(io.bovel.smtlib.Parser.parse(script))
    assertEquals(
      play(
        """(declare-const a (Array Bool Int)) (declare-const b (Array Bool Int)) (declare-const i Bool)
          |(declare-const v Int) (declare-fun h ((Array Bool Int)) Int)
          |(define-fun s () (Array Bool Int) (store b i v))
          |(assert (= (select a true) (select s true))) (assert (= (select a false) (select s false)))
          |(assert (not (= (h a) (h s)))) (check-sat)""".stripMargin
      ),
      List("unsat")
    )
    assertEquals(
      play(
        """(declare-const a (Array Int (Array Bool Int))) (declare-const v (Array Bool Int))
          |(declare-const i Int) (declare-const j Int) (declare-fun h ((Array Bool Int)) Int)
          |(define-fun s () (Array Int (Array Bool Int)) (store a i v)) (assert (= i j))
          |(assert (= (select (select s j) true) (select (select a j) true)))
          |(assert (= (select (select s j) false) (select (select a j) false)))
          |(assert (not (= (h (select s j)) (h (select a j))))) (check-sat)""".stripMargin
      ),
      List("unsat")
    )
    // The element a store holds is an array the arithmetic shares with the others: the map's
    // `q[true] = p[true] + 1` and `m[0][true] = 7` meet when `m[0]` and `p` do.
    assertEquals(
      play(
        """(set-option :check-models true)
          |(declare-const p (Array Bool Int)) (declare-const q (Array Bool Int))
          |(declare-const m (Array Int (Array Bool Int))) (define-fun g ((x Int)) Int (+ x 1))
          |(assert (= ((_ map g) p) q)) (assert (= (select (select m 0) true) 7))
          |(assert (= (select (store m 1 p) 1) p)) (check-sat)""".stripMargin
      ),
      List("sat")
    )
  }

  test("two arrays over a finite datatype, the same at every index, under a function") {
    // The final check compares array values by their normal form, over every value of a small finite
    // index sort: "0 with 1 at A" and "1 with 0 at B" are one array over `A | B`.
    def play(script: String) = Session.run(io.bovel.smtlib.Parser.parse(
      """(declare-datatypes ((E 0)) (((A) (B)))) (declare-fun h ((Array E Int)) Int)
        |(declare-const x (Array E Int)) (declare-const y (Array E Int))""".stripMargin + script
    ))
    assertEquals(
      play(
        """(assert (not (= (h (store ((as const (Array E Int)) 0) A 1))
          |  (h (store ((as const (Array E Int)) 1) B 0))))) (check-sat)""".stripMargin
      ),
      List("unsat")
    )
    val read = "(assert (= x (store ((as const (Array E Int)) 0) A 1))) (assert (not (= (h x) (h y))))"
    assertEquals(
      play(s"(assert (= (select x A) (select y A))) (assert (= (select x B) (select y B))) $read (check-sat)"),
      List("unsat")
    )
    assertEquals(
      play(s"(set-option :check-models true) (assert (= (select x A) (select y A))) $read (check-sat)"),
      List("sat")
    )
  }

  test("a store or a constant array of a popped level, again after the pop") {
    def play(script: String) = Session.run(io.bovel.smtlib.Parser.parse(script))
    for (inside, after) <- List(
        ("(select ((as const (Array Int Int)) 1) 0)", "((as const (Array Int Int)) 2)"),
        ("(select (store a 1 2) 1)", "(store a 1 2)")
      )
    do
      assertEquals(
        play(
          s"""(declare-const a (Array Int Int)) (declare-const b (Array Int Int))
             |(push 1) (assert (= $inside 1)) (pop 1)
             |(assert (= b $after)) (assert (= (select b 1) 2)) (check-sat)""".stripMargin
        ),
        List("sat")
      )
  }

  test("a script's own map!N and const!N are its own, beside the maps and constant arrays") {
    // Stainless writes an identifier `map` or `const` this way.
    assertEquals(
      Session.run(io.bovel.smtlib.Parser.parse(
        """(declare-fun map!1 () (Array Int Bool)) (declare-fun const!2 () (Array Int Bool))
          |(assert (= map!1 ((_ map not) const!2))) (assert (= const!2 ((as const (Array Int Bool)) true)))
          |(assert (select map!1 0)) (check-sat)""".stripMargin
      )),
      List("unsat")
    )
  }
