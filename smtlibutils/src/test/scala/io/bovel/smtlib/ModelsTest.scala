package io.bovel.smtlib

import io.bovel.vik.{Command, Formula, Lowering, Session, Solver}

/** `get-model` and `get-value`, and the models' soundness: the assertions of a
 *  sat script hold under the model the solver reports.
 */
class ModelsTest extends munit.FunSuite:
  test("constants of every sort, and a function's graph"):
    val responses = Session.run(Parser.parse("""
      (set-logic ALL)
      (declare-sort U 0)
      (declare-const a U)
      (declare-const b U)
      (declare-const p Bool)
      (declare-const x Int)
      (declare-fun f (Int) Int)
      (assert (distinct a b))
      (assert p)
      (assert (= (f 1) 5))
      (assert (<= 3 x))
      (check-sat)
      (get-value (x p (f 1) (f 7)))
      (get-model)"""))
    assertEquals(responses.head, "sat")
    assert(responses(1).startsWith("((x "), responses(1))
    assert(responses(1).contains("(p true)"), responses(1))
    assert(responses(1).contains("((f 1) 5)"), responses(1))
    val model = responses(2)
    assert(model.contains("(define-fun p () Bool true)"), model)
    assert(model.contains("(define-fun f ((x!0 Int)) Int (ite (= x!0 1) 5 5))"), model)
    assert(model.contains("@U!"), model)

  test("the assertions of sat scripts hold under the model"):
    val scripts = List(
      "TwoSquares__smtlib.598294.smt2",
      "2018-Goel-hwbench__QF_UF_bug-1_ab_reg_max.smt2",
      "20172804-Barrett__tests__v10__v10l20080.cvc.smt2",
      "dillig__20-4.smt2",
      "swap__swap_invalid_t3_np_nf_ai_00002_009.cvc.smt2", // arrays: valued extensionally
      "storeinv__storeinv_invalid_t1_pp_nf_ai_00002_001.cvc.smt2"
    )
    for file <- scripts do
      val script = Lowering(Parser.parse(Corpus.read(Corpus.files.find(_.endsWith(file)).get)))
      val solver = Solver()
      var checked = false
      val asserted = scala.collection.mutable.ArrayBuffer.empty[Formula]
      for command <- script.commands do
        command match
          case Command.DeclareFun(name, argSorts, sort, auxiliary) => solver.declare(name, argSorts, sort, auxiliary)
          case Command.DeclareDatatypes(ds) => ds.foreach(solver.declare)
          case Command.Assert(f) =>
            solver.assert(f)
            asserted += f
          case Command.AssertNamed(_, f) =>
            solver.assert(f)
            asserted += f
          case Command.CheckSat if !checked =>
            checked = true // the first check of these scripts is their sat question
            assertEquals(solver.solve(), solver.Result.Sat, file)
            val model = solver.model().getOrElse(fail(s"no model for $file"))
            // Only what was asserted before this check: the script may assert more after it.
            val failing = asserted.filter(f => !model.holds(f))
            assert(failing.isEmpty, s"$file: ${failing.length} assertions fail under the model")
          case _ => ()

  test("a datatype constant's value is a constructor term"):
    val responses = Session.run(Parser.parse("""
      (set-logic ALL)
      (declare-datatypes ((Pair 0)) (((pair (first Int) (second Int)))))
      (declare-const q Pair)
      (assert (= (first q) 3))
      (check-sat)
      (get-value (q (first q)))"""))
    assertEquals(responses.head, "sat")
    assert(responses(1).contains("(q (pair 3 "), responses(1))
    assert(responses(1).contains("((first q) 3)"), responses(1))

  test("a constant the simplifier defined away is still valued"):
    val responses = Session.run(Parser.parse("""
      (set-logic ALL)
      (declare-sort U 0)
      (declare-const p Bool)
      (declare-fun a () U)
      (declare-fun b () U)
      (assert (and (= a b) (not p)))
      (check-sat)
      (get-value ((= a b) b p))"""))
    assertEquals(responses.head, "sat")
    assert(responses(1).contains("((= a b) true)"), responses(1))
    assert(responses(1).contains("(p false)"), responses(1))
