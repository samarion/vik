package io.bovel.smtlib

/** What the parser refuses, and what it reads as the script's own. */
class ParserTest extends munit.FunSuite:
  private def parse(text: String): Script = Parser.parse(text)

  test("a script's function named like an operator is its own symbol"):
    // In a logic without arithmetic, `+` is whatever the script declares (issue 41).
    val script = parse("(declare-sort U 0) (declare-fun + (U U) U) (declare-const a U) (assert (= (+ a a) a))")
    script.commands.last match
      case Command.Assert(Formula.Eq(List(Term.App(Term.Const("+"), List(Term.Const("a"), Term.Const("a"))), _))) => ()
      case other => fail(s"read as the operator: $other")
    val defined = parse(
      "(declare-sort U 0) (declare-fun g (U) U) (define-fun to_real ((x U)) U (g x)) (declare-const a U) (assert (= (to_real a) a))"
    )
    assert(Printer.print(defined).contains("(to_real a)"))

  test("the reserved words and the Core symbols cannot be declared"):
    for name <- List("and", "=", "ite", "let", "forall", "true") do
      intercept[Smt2Error](parse(s"(declare-fun $name (Bool Bool) Bool)"))
      intercept[Smt2Error](parse(s"(define-fun $name ((x Bool)) Bool x)"))

  test("the binder of a match stays clear of the names bound around it"):
    // A let-bound `match!2`, a macro parameter `match!1` (issue 42): the case body reads them, not the scrutinee.
    val script = parse("""
      (declare-datatype L ((nil) (cons (h Int) (t L))))
      (define-fun g ((match!1 L) (x L)) L (match x ((nil nil) ((cons a b) match!1))))
      (declare-const x L) (declare-const y L)
      (assert (= (let ((match!1 y) (match!2 y)) (match x ((nil nil) ((cons a b) match!2)))) x))""")
    val binders = "\\(match!(\\d+) x\\)".r.findAllMatchIn(Printer.print(script)).map(_.group(1).nn.toInt).toList
    // The macro's binder, then the assertion's: neither is a name bound around its match.
    assertEquals(binders.length, 2)
    assert(binders.head != 1 && binders(1) != 1 && binders(1) != 2, binders.toString)

  test("an instance's name is refused as a script symbol, in either order"):
    // `f@Int` is the instance of `f` at Int (issue 43).
    intercept[Smt2Error](
      parse("(declare-sort-parameter A) (declare-fun f@Int (Int) Int) (declare-fun f (A) A) (assert (= (f 1) 5))")
    )
    intercept[Smt2Error](
      parse("(declare-sort-parameter A) (declare-fun f (A) A) (assert (= (f 1) 5)) (declare-fun f@Int (Int) Int)")
    )

  test("an index that does not fit is refused"):
    // `(_ rotate_left 4294967296)` was a rotation by nothing (issue 44).
    intercept[Smt2Error](parse("(declare-const x (_ BitVec 3)) (assert (= ((_ rotate_left 4294967296) x) x))"))
    intercept[Smt2Error](parse("(declare-const x (_ BitVec 4294967299))"))
    intercept[Smt2Error](parse("(declare-const x (_ BitVec 3)) (assert (= ((_ extract 4294967296 0) x) x))"))
    intercept[Smt2Error](parse("(push 4294967297)"))

  test("an ill-sorted script is refused"):
    // Each of these got a definite answer before the parser checked sorts; z3 refuses them all.
    val declarations = """
      (declare-sort U 0) (declare-sort V 0) (declare-const u U) (declare-const v V)
      (declare-const b Bool) (declare-const i Int) (declare-const r Real)
      (declare-const x (_ BitVec 8)) (declare-const y (_ BitVec 4))
      (declare-const a (Array Int U))
      (declare-fun f (U) U) (declare-fun g (Int) Int)
      (define-fun m ((p U)) U p)
      (declare-datatype D ((d (field U)))) (declare-datatype E ((e (other Int)))) (declare-const t D)
      """
    for ill <- List(
        "(= u v)", // the shape of corpus file alpha-beta_reduce-932bafde0fe6
        "(= (f u) v)",
        "(= (ite b u v) u)",
        "(distinct u v)",
        "(= u i)",
        "(= i b)",
        "(= x y)",
        "(= x 1)",
        "(= (f v) u)", // arguments
        "(= (g u) 1)",
        "(= (g r) 1)", // a Real is no Int, though z3 truncates it
        "(= (m v) u)",
        "(= (d v) t)",
        "(= (field (e 1)) u)",
        "((_ is d) (e 1))",
        "(= (select a u) u)",
        "(= (select a 1) v)",
        "(= (select (store a 1 v) 1) u)",
        "(= (+ i u) 1)", // theory operations
        "(= (+ i b) 1)",
        "(<= b b)",
        "(<= x x)",
        "(is_int u)",
        "(= (bvadd x y) x)",
        "(= (bvadd x i) x)",
        "(bvult x y)",
        "(= ((_ extract 8 0) x) x)",
        "(= ((_ extract 0 1) x) x)", // threw an ArithmeticException in the lowering
        "(= ((_ repeat 0) x) x)",
        "(= ((_ int2bv 8) r) x)",
        "(= (let ((w u)) (f (g w))) u)",
        "(= (as i Bool) b)"
      )
    do intercept[Smt2Error](parse(s"$declarations (assert $ill)"))
    for ill <- List("(define-fun c () Int 1.5)", "(define-fun c () U 1)", "(define-fun c ((p V)) U p)") do
      intercept[Smt2Error](parse(s"$declarations $ill"))
    intercept[Smt2Error](parse(s"$declarations (check-sat-assuming ((= u v)))"))

  test("an Int fits where a Real is expected, and the well-sorted scripts stay"):
    val declarations = """
      (declare-const b Bool) (declare-const i Int) (declare-const r Real) (declare-const x (_ BitVec 8))
      (declare-fun h (Real) Real) (define-fun n ((p Real)) Real p) (define-fun e () Real 0)
      (declare-datatype D ((d (field Real)))) (declare-const a (Array Real Real))
      """
    for fine <- List(
        "(= i r)",
        "(distinct i r)",
        "(= (ite b 1 r) 1.5)",
        "(= (+ i r) 1)",
        "(< i r 2)",
        "(= (h 1) (n i))",
        "(= (field (d 1)) 1.0)",
        "(= (select (store a 1 2) 1) 2.0)",
        "(= (to_real i) (to_real r))",
        "(= (to_int i) (to_int r))",
        "(is_int i)",
        "(= (/ i 2) 1.5)",
        "(= (bvadd x x x) ((_ extract 7 0) (concat x x)))",
        "(= (bvcomp x x) #b1)",
        "(= ((_ repeat 2) x) ((_ zero_extend 8) x))",
        "(= (ubv_to_int x) i)",
        "(= ((_ int2bv 8) i) x)"
      )
    do parse(s"$declarations (assert $fine)")

  test("an instance of a declared sort is one sort, however it is written"):
    parse("""
      (declare-sort-parameter X) (declare-sort Box 1) (define-sort IntBox () Int)
      (declare-fun unbox ((Box X)) X) (declare-const b (Box IntBox)) (declare-const c (Box Int))
      (assert (= (unbox b) (unbox c) 1))
      """)
    intercept[Smt2Error](
      parse("(declare-sort Box 1) (declare-const b (Box Int)) (declare-const c (Box Bool)) (assert (= b c))")
    )

  test("an indexed identifier that is no bit-vector literal is an error, not a crash"):
    for script <- List(
        "(assert (= (_ bvfoo 8) #x00))",
        "(assert (= #x00 (_ bv 8)))",
        "(assert (= #x00 (_ bv-1 8)))"
      )
    do intercept[Smt2Error](parse(script))
    parse("(assert (= (_ bv255 8) #xFF))")

  test("a sort must be declared"):
    for script <- List(
        "(declare-const a Mystery)",
        "(declare-fun f (Mystery) Bool)",
        "(declare-const a (Mystery Int))",
        "(declare-const a (Array Int Mystery))",
        "(define-fun f () Mystery 1)",
        "(define-fun f ((x Mystery)) Bool true)",
        "(declare-datatype D ((c (f Mystery))))",
        "(declare-datatypes ((L 1)) ((par (T) ((c (f Mystery))))))(declare-const a (L Int))",
        "(push)(declare-sort U 0)(pop)(declare-const a U)",
        "(declare-sort U 0)(reset)(declare-const a U)",
        "(declare-datatype D ((c)))(reset)(declare-const a D)"
      )
    do intercept[Smt2Error](parse(script))

  test("a declared sort takes its arity"):
    for script <- List(
        "(declare-sort U 0)(declare-const a (U Int))",
        "(declare-sort B 1)(declare-const a B)",
        "(declare-sort B 1)(declare-const a (B Int Int))",
        "(declare-sort B 1)(declare-datatype D ((c (f B))))"
      )
    do intercept[Smt2Error](parse(script))

  test("a datatype declares each constructor and each selector once"):
    // The second `f` replaced the first, so `(f (A 5))` was any integer (issue 146).
    for script <- List(
        "(declare-datatype D ((A (f Int)) (B (f Int))))",
        "(declare-datatype D ((A (f Int) (f Bool))))",
        "(declare-datatype D ((A) (A (f Int))))",
        "(declare-datatypes ((D 0) (E 0)) (((A)) ((B (f Int)) (C (f Int)))))",
        "(declare-datatype D (par (T) ((A (f T)) (B (f T)))))",
        "(declare-datatypes ((D 1) (E 0)) ((par (T) ((A (f T)))) ((B (g Int)) (C (g Int)))))"
      )
    do intercept[Smt2Error](parse(script))
    val e = intercept[Smt2Error](parse("(declare-datatype D ((A (f Int)) (B (f Int))))"))
    assertEquals(e.getMessage, "f: a selector declared twice in the datatype D")

  test("a symbol is declared once"):
    // The second `a` replaced the first: `A` was left with the constructor of `B`, and two of its values
    // could not differ (issue 230).
    for script <- List(
        "(declare-datatype A ((a (f Int))))(declare-datatype B ((a)))",
        "(declare-datatypes ((A 0) (B 0)) (((a (f Int))) ((a))))",
        "(declare-datatypes ((D 0) (E 0)) (((A (f Int))) ((B (f Int)))))",
        "(declare-datatype D ((A (B Int)) (B (A Int))))",
        "(declare-datatypes ((L 1) (M 1)) ((par (X) ((a (f X)))) (par (Y) ((a)))))",
        "(declare-datatype L (par (X) ((a (f X)))))(declare-datatype B ((a)))",
        "(declare-datatype B ((a)))(declare-datatype L (par (X) ((a (f X)))))",
        "(declare-datatypes ((L 1) (B 0)) ((par (X) ((a (f X)))) ((a))))",
        "(declare-fun a () Int)(declare-datatype A ((a)))",
        "(declare-datatype A ((a (f Int))))(declare-fun f (A) Int)",
        "(declare-datatype A ((a)))(define-fun a () Int 1)",
        "(define-fun a () Int 1)(declare-datatype A ((a)))",
        "(declare-fun g () Int)(declare-fun g () Bool)",
        "(declare-const g Int)(declare-const g Int)",
        "(declare-fun g () Int)(define-fun g () Int 2)",
        "(define-fun g () Int 2)(declare-const g Int)",
        "(define-fun g () Int 1)(define-fun g () Int 2)",
        // The declarations stay over a `reset-assertions` (issue 178), as in z3.
        "(declare-const g Int)(reset-assertions)(declare-const g Int)"
      )
    do intercept[Smt2Error](parse(script))
    val e = intercept[Smt2Error](parse("(declare-datatype A ((a (f Int))))(declare-datatype B ((a)))"))
    assertEquals(e.getMessage, "a: a symbol declared twice")
    // A popped symbol is free again.
    parse("(push 1)(declare-datatype A ((a)))(pop 1)(declare-datatype B ((a)))(declare-const x B)")
    parse("(push 1)(declare-const g Int)(pop 1)(declare-const g Bool)")

  test("a sort is declared once"):
    // The second `A` replaced the first, and a script with no assertion was unsat (issue 176).
    val par = "(par (T) ((a (x T))))"
    for script <- List(
        "(declare-datatypes ((A 0) (A 0)) (((a)) ((b))))",
        "(declare-datatype A ((a)))(declare-datatype A ((b)))",
        "(declare-sort A 0)(declare-datatype A ((a)))",
        "(declare-datatype A ((a)))(declare-sort A 0)",
        "(declare-sort A 0)(declare-sort A 1)",
        "(define-sort A () Int)(declare-datatype A ((a)))",
        "(declare-sort A 0)(define-sort A () Int)",
        "(define-sort A () Int)(define-sort A () Bool)",
        s"(declare-datatypes ((A 1) (A 0)) ($par ((b))))",
        s"(declare-datatypes ((A 1) (A 1)) ($par (par (T) ((b (y T))))))",
        s"(declare-datatype A $par)(declare-datatype A ((b)))",
        s"(declare-datatype A $par)(declare-sort A 0)",
        s"(declare-sort A 0)(declare-datatype A $par)",
        // The declarations stay over a `reset-assertions` (issue 178), and their names with them, as in z3.
        "(declare-datatype A ((a)))(reset-assertions)(declare-datatype A ((b)))"
      )
    do intercept[Smt2Error](parse(script))
    val e = intercept[Smt2Error](parse("(declare-datatypes ((A 0) (A 0)) (((a)) ((b))))"))
    assertEquals(e.getMessage, "A: a sort declared twice")
    // A popped name is free again, and so is the name of a theory's sort in a logic without the theory.
    parse("(push 1)(declare-sort A 0)(pop 1)(declare-datatype A ((a)))")
    parse("(set-logic QF_UF)(declare-sort Int 0)(declare-const x Int)")
    // A datatype's parameter may be named like a sort of the script (issue 152).
    parse("(declare-sort A 0)(declare-datatype L (par (A) ((nil) (cons (hd A) (tl (L A))))))")
    parse(s"(declare-datatypes ((A 1) (B 0)) ($par ((b (y (A Int))))))(declare-const z B)")

  test("a datatype is well-founded"):
    // No constructor of these can be applied first: they have no value, and SMT-LIB excludes them (issue 147).
    val box = "(declare-datatype Box (par (X) ((box (unbox X)))))"
    for script <- List(
        "(declare-datatype T ())",
        "(declare-datatype T ((c (f T))))",
        "(declare-datatype T ((c (n Int) (f T)) (d (g T))))",
        "(declare-datatypes ((A 0) (B 0)) (((a (x B))) ((b (y A)))))",
        "(declare-datatypes ((T 0)) (((c (f (Array Int T))))))",
        "(declare-datatype T ((c (f (Array T Int)))))",
        s"$box (declare-datatype T ((c (f (Box T)))))",
        "(declare-datatypes ((A 0) (B 0) (Box 1)) (((a (x B))) ((b (y A))) (par (X) ((box (unbox X))))))",
        // A parametric datatype is read where it is instantiated, and refused there.
        "(declare-datatype L (par (X) ((cons (head X) (tail (L X)))))) (declare-const x (L Int))",
        s"$box (declare-datatype W (par (X) ((w (u (Box (W X))))))) (declare-const x (W Int))",
        "(declare-datatype Opt (par (X) ((none) (some (val X)))))" +
          "(declare-datatype L (par (X) ((cons (head X) (tail (L X))))))" +
          "(assert (= (as none (Opt (L Int))) (as none (Opt (L Int)))))"
      )
    do
      val e = intercept[Smt2Error](parse(script))
      assert(e.getMessage.contains("is not well-founded"), e.getMessage)
    // A value through a later member of the group, through an instance, and under an array.
    parse("(declare-datatypes ((A 0) (B 0)) (((a (x B))) ((b (y A)) (e))))")
    parse("""
      (declare-datatype List (par (X) ((nil) (cons (head X) (tail (List X))))))
      (declare-datatype Tree ((node (children (List Tree)))))
      (declare-datatype Rose (par (X) ((rose (label X) (subtrees (List (Rose X)))))))
      (declare-const r (Rose Tree))
      """)
    parse("(declare-datatype T ((c (f (Array Int T))) (leaf)))")
    parse("(declare-sort U 0) (declare-datatype T ((c (u U) (s String) (b (_ BitVec 8)) (r Real))))")

  test("the datatypes a field may mention"):
    parse("""
      (declare-sort U 0) (declare-sort B 1)
      (declare-datatype R ((n) (m (next R))))
      (declare-datatypes ((A 0) (C 0)) (((a (c C))) ((e) (d (back A)))))
      (declare-datatypes ((L 1)) ((par (T) ((nil) (cons (head T) (tail (L T)))))))
      (declare-datatype F ((f (l (L F)) (u U) (b (B Int)) (arr (Array Int U)))))
      (declare-datatypes ((M 1) (N 0)) ((par (T) ((m1 (v T) (o N)))) ((n0) (n1 (w (M Int))))))
      (declare-datatype Unused ((s (t String))))
      (declare-const x (L Int)) (declare-const y (M Bool)) (declare-const z (B U))
      """)
