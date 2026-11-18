package io.bovel.vik

/** The solver driven over a stream (`-in`): one response per command, as it
 *  completes, `success` once asked for, and the Lean proof of the last `unsat`
 *  on `(get-proof)`.
 */
class InteractiveTest extends munit.FunSuite:
  private def serve(input: String, proofs: Boolean = false): List[String] =
    val bytes = java.io.ByteArrayOutputStream()
    val out = java.io.PrintStream(bytes, true, "UTF-8")
    Interactive(proofs).serve(java.io.StringReader(input), out)
    bytes.toString("UTF-8").linesIterator.toList

  test("commands split across lines, with strings, quoted symbols and comments"):
    val commands = Interactive.commands(java.io.StringReader("(a (b ; ) comment\n c)) (d \"x)\" |y)|)\n(e)")).toList
    assertEquals(commands, List("(a (b \n c))", "(d \"x)\" |y)|)", "(e)"))

  test("one response per command, success once asked"):
    val responses = serve(
      """(declare-const x Int)
        |(set-option :print-success true)
        |(declare-const y Int)
        |(assert (< x y))
        |(check-sat)
        |(push 1)
        |(assert (< y x))
        |(check-sat)
        |(pop 1)
        |(check-sat-assuming ((> x 0)))
        |(exit)""".stripMargin
    )
    assertEquals(
      responses,
      List("success", "success", "success", "sat", "success", "success", "unsat", "success", "sat", "success")
    )

  test("an unsupported command answers an error and the session goes on"):
    val responses =
      serve("(set-option :print-success true) (assert (frob 1)) (declare-const x Int) (assert (< x x)) (check-sat)")
    assertEquals(responses.length, 5)
    assert(responses(1).startsWith("(error"), responses(1))
    assertEquals(responses.drop(2), List("success", "success", "unsat"))

  test("a model is kept for the get-model after its check-sat"):
    val responses = serve("(declare-const x Int) (assert (= x 3)) (check-sat) (get-model)")
    assertEquals(responses.head, "sat")
    assert(responses.tail.mkString(" ").contains("3"), responses.mkString("\n"))

  test("get-proof needs --proofs"):
    val responses = serve("(declare-const x Int) (assert (< x x)) (check-sat) (get-proof)")
    assertEquals(responses.head, "unsat")
    assert(responses(1).startsWith("(error"), responses(1))

  test("get-proof answers the Lean proof of the last unsat, after check-sat-assuming popped"):
    val responses = serve(
      "(set-option :print-success true) (declare-const x Int) (assert (<= x 0)) (check-sat-assuming ((< 0 x))) (get-proof)",
      proofs = true
    )
    assertEquals(responses.take(4), List("success", "success", "success", "unsat"))
    val proof = responses.drop(4).mkString("\n")
    assert(proof.startsWith("\""), proof.take(200))
    assert(proof.contains("theorem no_model"), proof.take(2000))

  test("a model quotes the symbols that are not simple"):
    val responses = serve("(declare-const |eq[A]| Int) (assert (= |eq[A]| 3)) (check-sat) (get-model)")
    assert(responses.tail.mkString(" ").contains("|eq[A]|"), responses.mkString("\n"))
