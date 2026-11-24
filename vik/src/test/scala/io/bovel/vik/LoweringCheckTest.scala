package io.bovel.vik

import io.bovel.smtlib.Parser
import io.bovel.smtlib as s2

class LoweringCheckTest extends munit.FunSuite:
  private val script = """
    (declare-const x (_ BitVec 8)) (declare-const y (_ BitVec 8)) (declare-const a Int) (declare-const r Real)
    (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
    (define-fun g ((u (_ BitVec 8))) (_ BitVec 8) (bvmul u (bvadd u #x01)))
    (assert (bvult (bvadd x y) (g x)))
    (push 1)
    (assert (= (bvand x y) (f (bvlshr x y))))
    (assert (bvslt (bvsdiv x y) (bvsmod x #xfd)))
    (assert (= (concat ((_ extract 3 0) x) ((_ extract 7 4) y)) ((_ rotate_left 3) (bvnot x))))
    (pop 1)
    (assert (let ((s (bvadd x y))) (= s (bvudiv s y))))
    (assert (< (to_int (* 1.5 r)) (ite (is_int r) a (+ a 2))))
    (check-sat)
  """

  /** The commands of `script`, each lowered and checked; `tamper` may change
   *  the lowering of each, and the intros the lowering recorded for it.
   */
  private def check(
      tamper: (List[Command], List[Lowering.Intro]) => (List[Command], List[Lowering.Intro]) = (c, i) => (c, i)
  ): List[String] =
    val lowerer = Lowerer()
    lowerer.tracing = true
    val checker = LoweringCheck()
    Parser.parse(script).commands.flatMap { c =>
      val lowered = lowerer.commands(List(c))
      val made = lowerer.intros.toList
      lowerer.intros.clear()
      val (l, m) = tamper(lowered, made)
      checker.command(c, l, m)
    }

  test("the lowering of a script checks"):
    assertEquals(check(), Nil)

  test("a definition that is not the rule's is refused"):
    var done = false
    val errors = check((lowered, made) =>
      val out = lowered.map {
        case Command.Assert(Formula.Or(cases)) if !done =>
          done = true
          Command.Assert(Formula.Or(cases.take(1))) // one overflow count fewer
        case c => c
      }
      (out, made)
    )
    assert(done)
    assert(errors.exists(_.contains("defining assertions")), errors)

  test("an assertion that is not the lowering of its surface one is refused"):
    val errors = check((lowered, made) =>
      (
        lowered.map {
          case Command.Assert(Formula.Le(l, r)) => Command.Assert(Formula.Le(r, l))
          case c => c
        },
        made
      )
    )
    assert(errors.exists(_.contains("not the lowering")), errors)

  test("a minted symbol with no intro is refused"):
    var dropped = false
    val errors = check((lowered, made) =>
      if made.nonEmpty && !dropped then
        dropped = true
        (lowered, made.tail)
      else (lowered, made)
    )
    assert(errors.nonEmpty)

  test("an intro that is not the one of the rule is refused"):
    var changed = false
    val errors = check((lowered, made) =>
      (
        lowered,
        made.map {
          case Lowering.Intro("modulo", List(v, w, lo: BigInt, hi), args, ss) if !changed =>
            changed = true
            Lowering.Intro("modulo", List(v, w, lo + 1, hi), args, ss)
          case i => i
        }
      )
    )
    assert(changed)
    assert(errors.nonEmpty)

  test("a session checks the lowering with the proof"):
    val session = Session(Solver(proofs = true))
    session.run(Parser.parse("(declare-const x (_ BitVec 4)) (assert (bvult (bvadd x #x1) x)) (assert (= x #x0))"))
    assertEquals(session.run(Parser.parse("(check-sat)")), List("unsat"))
    assertEquals(session.checkProof(), Nil)

  test("a command the lowering refuses leaves the later proofs alone"):
    // The floor of `to_int r` is minted before `div` is refused: neither it nor its definition may reach
    // the next command.
    val session = Session(Solver(proofs = true))
    session.run("(declare-const r Real) (declare-const a Int)")
    intercept[s2.Unsupported](session.run("(assert (and (= (to_int r) 1) (= (div a 2) 3)))"))
    assertEquals(session.run("(assert (< a 0)) (assert (> a 0)) (check-sat)"), List("unsat"))
    assertEquals(session.checkProof(), Nil)
    assert(session.proof().isRight, session.proof())

  test("no proof after a later sat"):
    val session = Session(Solver(proofs = true))
    val answers = session.run(Parser.parse("""
      (declare-const a Int)
      (push 1) (assert (< a 0)) (assert (> a 0)) (check-sat) (pop 1)
      (check-sat)
    """))
    assertEquals(answers, List("unsat", "sat"))
    assert(session.proof().isLeft, session.proof())

  test("the witnesses of extensionality over bit-vector indices check"):
    // Three arrays over a 1-bit index, pairwise different, each 0 or 1 everywhere: the witnesses must be
    // indices of the range, or the pigeonhole on 2 × 2 values would not close.
    val session = Session(Solver(proofs = true))
    val answers = session.run(Parser.parse("""
      (declare-const a (Array (_ BitVec 1) Bool)) (declare-const b (Array (_ BitVec 1) Bool))
      (declare-const c (Array (_ BitVec 1) Bool)) (declare-const d (Array (_ BitVec 1) Bool))
      (declare-const e (Array (_ BitVec 1) Bool))
      (assert (distinct a b c d e))
      (check-sat)
    """))
    assertEquals(answers, List("unsat"))
    assertEquals(session.checkProof(), Nil)
