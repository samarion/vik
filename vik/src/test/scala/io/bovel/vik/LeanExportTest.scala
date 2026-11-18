package io.bovel.vik

import io.bovel.smtlib.Parser

/** The proofs of a few `Unsat`s, from the script to its lowering and the
 *  solver's proof, written as Lean terms, each to a file of
 *  `target/lean-export` for `proofs/lean` to check (`proofs/lean/exported.sh`).
 */
class LeanExportTest extends munit.FunSuite:
  private val out =
    val dir = java.nio.file.Path.of("target", "lean-export")
    java.nio.file.Files.createDirectories(dir)
    Some(dir.toString)

  private def write(name: String, script: String): Unit =
    val session = Session(Solver(proofs = true))
    val answers = session.run(Parser.parse(script))
    assertEquals(answers.lastOption, Some("unsat"))
    val lean = session.leanProof() match
      case Right(text) => text
      case Left(why) => fail(s"no Lean proof: $why")
    for dir <- out do
      val header = s"import Vik\n\nnamespace Vik.Low.Exported.$name\n\nopen Vik.Low Vik.Surf Vik.Clausal\n\n"
      java.nio.file.Files.writeString(
        java.nio.file.Path.of(dir, s"$name.lean"),
        header + lean + s"\nend Vik.Low.Exported.$name\n"
      )

  test("bounds"):
    write("Bounds", "(declare-const x Int) (assert (<= x 0)) (assert (< 0 x)) (check-sat)")

  test("propositional"):
    write(
      "Props",
      "(declare-const p Bool) (declare-const q Bool) (assert (or p q)) (assert (not p)) (assert (not q)) (check-sat)"
    )

  test("congruence"):
    write(
      "Congruence",
      "(declare-sort U 0) (declare-fun f (U) U) (declare-const a U) (declare-const b U) " +
        "(assert (= a b)) (assert (not (= (f a) (f b)))) (check-sat)"
    )

  test("levels"):
    write("Levels", "(declare-const x Int) (assert (<= x 0)) (push 1) (assert (< 0 x)) (check-sat)")

  test("assumptions"):
    write(
      "Assuming",
      "(declare-const x Int) (declare-const p Bool) (assert (=> p (< 0 x))) (assert (<= x 0)) (check-sat-assuming (p))"
    )

  test("datatypes"):
    write(
      "Datatypes",
      "(declare-datatypes ((L 0)) (((nil) (cons (hd Int) (tl L))))) (declare-const x L) " +
        "(assert (not ((_ is nil) x))) (assert (not ((_ is cons) x))) (check-sat)"
    )

  test("injectivity"):
    write(
      "Injective",
      "(declare-datatypes ((L 0)) (((nil) (cons (hd Int) (tl L))))) (declare-const a Int) (declare-const b Int) " +
        "(assert (= (cons a nil) (cons b nil))) (assert (< a b)) (check-sat)"
    )

  test("arrays"):
    write(
      "Arrays",
      "(declare-const a (Array Int Int)) (declare-const i Int) (declare-const v Int) " +
        "(assert (not (= (select (store a i v) i) v))) (check-sat)"
    )

  test("extensionality"):
    write(
      "Extensionality",
      "(declare-const a (Array Int Int)) (declare-const b (Array Int Int)) (declare-const i Int) " +
        "(assert (not (= a b))) (assert (= a (store b i (select b i)))) (check-sat)"
    )

  test("let and define-fun"):
    write(
      "Defs",
      "(declare-const x Int) (define-fun pos ((y Int)) Bool (< 0 y)) (define-fun zero () Int 0) " +
        "(assert (let ((z x)) (<= z zero))) (assert (pos x)) (check-sat)"
    )

  test("ite"):
    write(
      "Ite",
      "(declare-const x Int) (declare-const p Bool) (assert (< (ite p x 1) 0)) (assert (<= 0 x)) (check-sat)"
    )

  test("reals"):
    write("Reals", "(declare-const r Real) (assert (< r 0.5)) (assert (> (* 2.0 r) 1.0)) (check-sat)")

  test("to_int"):
    write("ToInt", "(declare-const r Real) (assert (= (to_int r) 1)) (assert (< r 1.0)) (check-sat)")

  test("bit-vector comparisons"):
    write(
      "BvCmp",
      "(declare-const a (_ BitVec 4)) (assert (bvult a #x2)) (assert (bvugt a #x3)) (check-sat)"
    )

  test("bit-vector sums"):
    write(
      "BvAdd",
      "(declare-const a (_ BitVec 4)) (assert (= (bvadd a #x1) #x0)) (assert (bvult a #xe)) (check-sat)"
    )

  test("bit-vector operations"):
    write(
      "BvOps",
      "(declare-const a (_ BitVec 8)) (declare-const b (_ BitVec 8)) " +
        "(assert (= ((_ extract 3 0) a) #x5)) (assert (= (bvand a #x0f) #x06)) (check-sat)"
    )

  test("bit-vector division"):
    write(
      "BvDiv",
      "(declare-const a (_ BitVec 4)) (declare-const b (_ BitVec 4)) " +
        "(assert (= (bvudiv a b) #x3)) (assert (= (bvurem a b) #x1)) (assert (= b #x5)) (check-sat)"
    )

  test("bit-vector indices"):
    write(
      "BvIndex",
      """(declare-const a (Array (_ BitVec 1) Bool)) (declare-const b (Array (_ BitVec 1) Bool))
      (declare-const c (Array (_ BitVec 1) Bool)) (declare-const d (Array (_ BitVec 1) Bool))
      (declare-const e (Array (_ BitVec 1) Bool))
      (assert (distinct a b c d e))
      (check-sat)"""
    )
