package io.bovel.vik

import io.bovel.smtlib.{Parser, Smt2Error, Unsupported}
import Formula.*
import Term.*

/** The lowering, shape by shape: names to de Bruijn indices, redexes reduced,
 *  `ite` named, and the fragment line — what parses but the solver does not
 *  speak — drawn with a message.
 */
class LoweringTest extends munit.FunSuite:
  def lowered(script: String): List[Formula] =
    Lowering(Parser.parse(script)).commands.collect { case Command.Assert(f) => f }

  test("a term-level ite becomes a defined constant before its assertion"):
    val commands = Lowering(Parser.parse(
      "(declare-const p Bool) (declare-const x Int) (declare-const y Int) (assert (= (ite p x y) 2))"
    )).commands
    assert(commands.exists { case Command.DeclareFun("ite!1", Nil, "Int") => true; case _ => false })
    val asserts = commands.collect { case Command.Assert(f) => f }
    assertEquals(asserts(0), Implies(Pred(Const("p")), IntEq(Const("ite!1"), Const("x"))))

  test("the integer normal form: chains, linear combinations"):
    val asserts = lowered("""
      (declare-const x Int) (declare-const y Int)
      (assert (<= (+ (* 2 x) y (- 3)) 5))
      (assert (< 0 x y))
      (assert (distinct x y 7))""")
    val (x, y) = (Const("x"), Const("y"))
    assertEquals(asserts(0), Le(Linear(List((2, x), (1, y)), -3), Num(5)))
    assertEquals(asserts(1), And(List(Lt(Num(0), x), Lt(x, y)))) // chained, pairwise
    assertEquals(asserts(2), IntDistinct(List(x, y, Num(7))))

  test("reset-assertions keeps what the declarations assert"):
    // The range of a bit-vector constant is an assertion, and reset-assertions drops the assertions:
    // without it said again, the constants are integers of any size and an unsat script answers sat.
    val commands = Lowering(Parser.parse(
      "(declare-const a (_ BitVec 8)) (declare-const b (_ BitVec 8)) (reset-assertions) (assert (= a b))"
    )).commands
    val after = commands.dropWhile(_ != Command.ResetAssertions).tail
    assertEquals(
      after.takeWhile(_ != Command.Assert(IntEq(Const("a"), Const("b")))),
      List(
        Command.Assert(And(List(Le(Num(0), Const("a")), Le(Const("a"), Num(255))))),
        Command.Assert(And(List(Le(Num(0), Const("b")), Le(Const("b"), Num(255)))))
      )
    )

  test("a pop keeps what a global declaration asserts (issue 145)"):
    // Under `:global-declarations` the constant outlives its level, and its range, asserted there, did not:
    // it is asserted below every level instead.
    val global = "(set-option :global-declarations true)"
    val x = "(declare-const x (_ BitVec 1))"
    def assertions(script: String): List[Command] = Lowering(Parser.parse(script)).commands.filter {
      case Command.Assert(_) | Command.AssertGlobal(_) => true
      case _ => false
    }
    val range = And(List(Le(Num(0), Const("x")), Le(Const("x"), Num(1))))
    assertEquals(assertions(s"$global(push 1)$x(pop 1)"), List(Command.AssertGlobal(range)))
    assertEquals(assertions(s"$global$x"), List(Command.AssertGlobal(range)))
    // The lowered script names it by a command of its own, which SMT-LIB does not have.
    assertEquals(Printer.print(Command.AssertGlobal(range)), "(assert-global (and (<= 0 x) (<= x 1)))")
    // Without the option the range is the level's, like the declaration.
    assertEquals(assertions(s"(push 1)$x(pop 1)"), List(Command.Assert(range)))
    // It holds after one `pop`, after two levels popped at once, and when the option is turned off
    // before the `pop`, which does not undo the declaration.
    val wide = "(assert (bvugt x #b1))(check-sat)"
    for script <- List(
        s"$global(push 1)$x(pop 1)$wide",
        s"$global(push 2)$x(pop 2)$wide",
        s"$global(push 2)$x(pop 1)(pop 1)$wide",
        s"$global(push 1)$x(set-option :global-declarations false)(pop 1)$wide",
        s"$global(push 1)$x(check-sat)(pop 1)$wide"
      )
    do assertEquals(Session.run(Parser.parse(script)).last, "unsat", script)
    // A `get-assertions` shows it once, at any depth.
    assertEquals(
      Session.run(Parser.parse(s"$global(push 1)$x(pop 1)(push 1)(pop 1)(get-assertions)")),
      List("((and (<= 0 x) (<= x 1)))")
    )

  private def minted(script: String, prefix: String): Int =
    Lowering(Parser.parse(script)).commands.count {
      case Command.DeclareFun(name, _, _) => name.startsWith(prefix + "!")
      case _ => false
    }
  private val rational = "(assert (>= a 0.5))"
  private val operation = "(assert (= y (bvadd x #x01)))"
  private val declared = "(declare-const a Real)(declare-const x (_ BitVec 8))(declare-const y (_ BitVec 8))"

  test("what a level minted is minted again after its pop (issue 83)"):
    assertEquals(minted(s"$declared(push 1)$rational(pop 1)$rational", "rat"), 2)
    assertEquals(minted(s"$declared(push 1)$operation(pop 1)$operation", "bv"), 2)

  test("what an outer level minted outlives the pops above it (issue 83)"):
    assertEquals(minted(s"$declared$rational(push 1)(pop 1)$rational", "rat"), 1)
    assertEquals(minted(s"$declared$operation(push 1)(pop 1)$operation", "bv"), 1)
    // Level by level: the second use finds the first's, and only the popped level's go.
    assertEquals(minted(s"$declared(push 1)$rational(push 1)$rational(pop 1)$rational(pop 1)$rational", "rat"), 2)
    assertEquals(
      minted(s"$declared$rational(push 1)$rational(assert (<= a 0.25))(pop 1)(assert (<= a 0.25))", "rat"),
      3
    )

  test("a definition popped is a definition stated again (issue 83)"):
    def answer(script: String): List[String] = Session.run(Parser.parse(script))
    val rationalAgain = "(assert (= a 0.5))(assert (= a 0.25))(check-sat)"
    assertEquals(answer(s"$declared(push 1)(assert (= a 0.5))(pop 1)$rationalAgain"), List("unsat"))
    val operationAgain = s"$operation(assert (= x #x00))(assert (= y #x02))(check-sat)"
    assertEquals(answer(s"$declared(push 1)$operation(pop 1)$operationAgain"), List("unsat"))
    // The range of an application, asserted at its first use.
    assertEquals(
      answer(
        "(declare-fun f (Int) (_ BitVec 8))(push 1)(assert (= (f 0) #x00))(pop 1)" +
          "(assert (> (ubv_to_int (f 0)) 255))(check-sat)"
      ),
      List("unsat")
    )

  test("the definitions die with their level under :global-declarations too (issue 83)"):
    // The constants stay declared there, and so a memo that followed the declarations would keep them.
    assertEquals(
      Session.run(Parser.parse(
        "(set-option :global-declarations true)(declare-const a Real)" +
          "(push 1)(assert (= a 0.5))(pop 1)(assert (= a 0.5))(assert (= a 0.25))(check-sat)"
      )),
      List("unsat")
    )

  test("what a failed command minted is defined below the next level (issue 83)"):
    val s = Session()
    s.run("(declare-const a Real)(declare-const n Int)")
    // `0.5` is minted, its definition still pending, when the product is refused.
    intercept[Smt2Error](s.assert("(= (+ a 0.5) (* n n))"))
    s.push()
    s.assert("(>= a 1.0)")
    s.pop()
    s.assert("(= a 0.5)")
    s.assert("(>= a 1.0)")
    assertEquals(s.checkSat(), Some(false))

  test("outside the fragment: nonlinear multiplication, integer division"):
    intercept[Smt2Error](lowered("(declare-const x Int) (assert (<= (* x x) 1))"))
    intercept[Unsupported](lowered("(declare-const x Int) (assert (= (div x 2) 1))"))
    // Bit-vectors are bounded, so the operations the integers refuse are lowered there.
    lowered("(declare-const a (_ BitVec 8)) (declare-const b (_ BitVec 8)) (assert (= (bvudiv a b) a))")
    lowered("(declare-const a (_ BitVec 8)) (declare-const b (_ BitVec 8)) (assert (= (bvmul a b) a))")

  test("to_real is the identity, to_int the pinned floor"):
    val commands = Lowering(Parser.parse(
      "(declare-const n Int) (declare-const x Real) (assert (= x (to_real n))) (assert (= (to_int x) 2))"
    )).commands
    val asserts = commands.collect { case Command.Assert(f) => f }
    assertEquals(asserts(0), IntEq(Const("x"), Const("n"))) // to_real vanishes: sorts carry the difference
    assert(commands.exists { case Command.DeclareFun("floor!1", Nil, "Int") => true; case _ => false })
    assertEquals(asserts(1), Le(Const("floor!1"), Const("x")))
    assertEquals(asserts(2), Less(Const("x"), Linear(List((BigInt(1), Const("floor!1"))), 1)))
    assertEquals(asserts(3), IntEq(Const("floor!1"), Num(2)))

  test("the casts fold on literals"):
    assertEquals(lowered("(assert (is_int 2.0))"), List(True))
    assertEquals(lowered("(assert (not (is_int 2.5)))").last, Not(False))
    assertEquals(lowered("(assert (= (to_int 2.5) 2))").last, IntEq(Num(2), Num(2)))
    assertEquals(lowered("(assert (= (to_int (- 5.5)) (- 6)))").last, IntEq(Num(-6), Num(-6)))

  test("the bit-vector conversions: identity, sign split, pinned modulo"):
    assertEquals(
      lowered("(declare-const x (_ BitVec 8)) (declare-const n Int) (assert (= (ubv_to_int x) n))").last,
      IntEq(Const("x"), Const("n")) // ubv_to_int vanishes: the lowered bit-vector is its unsigned value
    )
    assertEquals(lowered("(assert (= (sbv_to_int #xFF) (- 1)))").last, IntEq(Num(-1), Num(-1)))
    assertEquals(lowered("(assert (= (bv2int #xFF) (- 1)))").last, IntEq(Num(-1), Num(-1))) // signed, unlike z3
    assertEquals(lowered("(assert (= (sbv_to_int #x7F) 127))").last, IntEq(Num(127), Num(127)))
    assertEquals(lowered("(assert (= ((_ int_to_bv 8) 300) #x2C))").last, IntEq(Num(44), Num(44)))
    assertEquals(lowered("(assert (= ((_ int_to_bv 8) (- 1)) #xFF))").last, IntEq(Num(255), Num(255)))
    val asserts = lowered("(declare-const n Int) (assert (= ((_ int_to_bv 8) n) #x2A))")
    assertEquals(asserts.last, IntEq(Const("bv!1"), Num(42)))
    assert(asserts.contains(IntEq(Const("n"), Linear(List((1, Const("bv!1")), (256, Const("k!2"))), 0))), asserts)

  test("a script's symbol named like the lowering's own is refused, not merged (issue 21)"):
    val e =
      intercept[Smt2Error](Session.run(Parser.parse("(declare-fun store!1 ((Array Int Int) Int Int) (Array Int Int))")))
    assert(e.getMessage.contains("store!1"), e.getMessage)
    val f = intercept[Smt2Error](Session.run(Parser.parse(
      "(declare-datatypes ((Lst 1)) ((par (T) ((nil) (cons (hd T) (tl (Lst T)))))))" +
        "(declare-fun nil@Int () (Lst Int))"
    )))
    assert(f.getMessage.contains("nil@Int"), f.getMessage)

  test("the lowering's names pass over the script's own (issue 21)"):
    // `bit!1` is the script's constant; the bits of `bvand` get other names and its value stays free.
    assertEquals(
      Session.run(Parser.parse(
        "(declare-fun x () (_ BitVec 4))(declare-fun y () (_ BitVec 4))(declare-fun |bit!1| () Int)" +
          "(assert (= |bit!1| 7))(assert (= (bvand x y) #x0))(check-sat)"
      )),
      List("sat")
    )

  test("a lowered script writes a declared name with the bars it needs (issue 33)"):
    assertEquals(Printer.print(Command.DeclareSort("a b", 0)), "(declare-sort |a b| 0)")
    assertEquals(Printer.print(Command.DeclareFun("f g", List("|a b|"), "Int")), "(declare-fun |f g| (|a b|) Int)")

  test("a witness's name declared by the script after the witness is refused (issue 21)"):
    val e = intercept[Smt2Error](Session.run(Parser.parse(
      "(declare-const a (Array Int Int))(declare-const b (Array Int Int))(assert (not (= a b)))(check-sat)" +
        "(declare-const ext!0 Int)(assert (= ext!0 0))(check-sat)"
    )))
    assert(e.getMessage.contains("ext!0"), e.getMessage)

  test("a lowered script writes a datatype's names with the bars they need (issue 33)"):
    val lowered = Printer.print(Lowering(Parser.parse(
      "(declare-datatype |my type| ((|c 1| (|f 1| Int)) (|c 2|)))(declare-const x |my type|)" +
        "(assert ((_ is |c 1|) x))(assert (= (|f 1| x) 3))(check-sat)"
    )))
    assert(lowered.contains("(declare-datatypes ((|my type| 0)) (((|c 1| (|f 1| Int)) (|c 2|))))"), lowered)
    assert(lowered.contains("(_ is |c 1|)"), lowered)
