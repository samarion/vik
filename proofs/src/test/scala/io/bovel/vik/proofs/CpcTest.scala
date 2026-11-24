package io.bovel.vik.proofs

import java.nio.file.{Files, Path}

import io.bovel.smtlib.Parser
import io.bovel.vik.{Cpc, Session, Solver}

/** The CPC proofs of a few `Unsat`s, each written to `target/cpc-export` and,
 *  when the environment variable `ETHOS` names the Ethos checker and `CPC` the
 *  signature `Cpc.eo`, checked by Ethos with `proofs/cpc/Vik.eo`. The compact
 *  proof is also written as a Lean file for `Vik.Cpc.Proof.check` (`CpcLean`).
 */
class CpcTest extends munit.FunSuite:
  private val out = Files.createDirectories(Path.of("target", "cpc-export"))

  private def check(name: String, script: String): Unit =
    val session = Session(Solver(proofs = true))
    val answers = session.run(Parser.parse(script))
    assertEquals(answers.lastOption, Some("unsat"))
    val certificate = session.proof() match
      case Right(text) => text
      case Left(why) => fail(s"no proof: $why")
    Files.writeString(out.resolve(s"$name.cert"), certificate)
    // The compact proof, and the plain one in CPC's rules only.
    for (suffix, compact) <- Seq("" -> true, "-plain" -> false) do
      val file = out.resolve(s"$name$suffix.cpc")
      Files.writeString(file, session.cpcProof(compact).fold(why => fail(s"no CPC proof: $why"), identity))
      for ethos <- sys.env.get("ETHOS"); cpc <- sys.env.get("CPC") do
        // From the repository's root or from `proofs`, as sbt forks the tests.
        val vik = Seq(Path.of("proofs", "cpc", "Vik.eo"), Path.of("cpc", "Vik.eo")).find(Files.exists(_))
          .getOrElse(fail("no proofs/cpc/Vik.eo")).toAbsolutePath
        val p = ProcessBuilder(ethos, s"--include=$cpc", s"--include=$vik", file.toAbsolutePath.toString)
          .redirectErrorStream(true).start()
        val text = String(p.getInputStream.readAllBytes())
        p.waitFor()
        assertEquals(text.trim.linesIterator.toList.lastOption, Some("correct"), s"$name$suffix: $text")
    val cpc = session.cpcProof(true).fold(why => fail(s"no CPC proof: $why"), identity)
    Files.writeString(out.resolve(s"$name.lean"), CpcLean(certificate, cpc, s"Vik.Cpc.Exported.$name"))

  test("propositional"):
    check(
      "Props",
      "(declare-const p Bool) (declare-const q Bool) (assert (or p q)) (assert (not p)) (assert (not q)) (check-sat)"
    )

  test("congruence"):
    check(
      "Congruence",
      "(declare-sort U 0) (declare-fun f (U) U) (declare-const a U) (declare-const b U) " +
        "(assert (= a b)) (assert (not (= (f a) (f b)))) (check-sat)"
    )

  test("chains"):
    check(
      "Chains",
      "(declare-sort U 0) (declare-fun f (U U) U) (declare-const a U) (declare-const b U) (declare-const c U) " +
        "(assert (= a b c)) (assert (distinct (f a b) (f c a))) (check-sat)"
    )

  test("Boolean terms"):
    check(
      "BoolTerms",
      "(declare-sort U 0) (declare-fun p (U) Bool) (declare-const a U) (declare-const b U) " +
        "(assert (p a)) (assert (= a b)) (assert (not (p b))) (check-sat)"
    )

  test("connectives"):
    check(
      "Connectives",
      "(declare-const p Bool) (declare-const q Bool) (declare-const r Bool) " +
        "(assert (= p (and q r))) (assert (ite p q (not r))) (assert (=> q (not r))) (assert (or p r)) (check-sat)"
    )

  test("levels"):
    check(
      "Levels",
      "(declare-sort U 0) (declare-const a U) (declare-const b U) (declare-const c U) (assert (= a b)) " +
        "(push 1) (assert (not (= a b))) (check-sat) (pop 1) (push 1) (assert (= b c)) (assert (not (= a c))) (check-sat)"
    )

  test("assumptions"):
    check(
      "Assuming",
      "(declare-sort U 0) (declare-const a U) (declare-const b U) (declare-const p Bool) " +
        "(assert (=> p (= a b))) (assert (not (= a b))) (check-sat-assuming (p))"
    )

  test("definitions"):
    check(
      "Defs",
      "(declare-sort U 0) (declare-fun f (U) U) (declare-const a U) (define-fun g ((y U)) U (f (f y))) " +
        "(define-fun c () U (f a)) (assert (let ((z (g a))) (not (= z (f c))))) (check-sat)"
    )

  test("term ite"):
    check(
      "Ite",
      "(declare-sort U 0) (declare-fun f (U) U) (declare-const a U) (declare-const b U) (declare-const p Bool) " +
        "(assert (not (= (f (ite p a b)) (f a)))) (assert (= a b)) (check-sat)"
    )

  test("simplifications"):
    check(
      "Simp",
      "(declare-sort U 0) (declare-fun f (U) U) (declare-fun p (U) Bool) (declare-const a U) (declare-const b U) " +
        "(declare-const d U) (declare-const g U) (declare-const q Bool) " +
        "(assert (and (= b (f a)) (p b))) " +
        "(assert (or (and (= d a) (not (p (f d)))) (=> q (and (= g (f a)) (not (p g)))))) (assert q) (check-sat)"
    )
