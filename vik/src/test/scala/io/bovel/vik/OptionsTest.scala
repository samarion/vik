package io.bovel.vik

import io.bovel.smtlib.{Parser, Printer}

/** `:rlimit` (the fuel), `:timeout`, `:check-models`, and `:reason-unknown`. */
class OptionsTest extends munit.FunSuite:
  test("check-models: each sat's model makes the assertions true, as written"):
    val script = Parser.parse("""
      (set-option :check-models true)
      (declare-const x Int)
      (declare-const p Bool)
      (declare-const b (_ BitVec 8))
      (define-fun big ((v (_ BitVec 8))) Bool (bvugt v #x80))
      (assert (< 3 x 10))
      (assert (big (bvadd b #x01)))
      (assert (=> p (= x 7)))
      (check-sat)
      (push 1)
      (assert (let ((y (+ x 1))) (= y 5)))
      (check-sat)
      (pop 1)
      (check-sat-assuming (p))""")
    assertEquals(Session.run(script), List("sat", "sat", "sat"))
    val s = Session(checkModels = true)
    s.run("(declare-const x Int)")
    s.assert("(< x 0)")
    assertEquals(s.checkSat(), Some(true))

  test("check-models: lowered commands played directly are checked as lowered"):
    val lowered = Lowering(Parser.parse("""
      (declare-const b (_ BitVec 8))
      (declare-const a (Array Int Int))
      (assert (bvugt (bvmul b #x03) #x80))
      (assert (= (select a 1) (ite (= b #x2b) 4 5)))
      (check-sat)
      (check-sat-assuming ((= (select a 2) 6)))""")).commands
    assertEquals(Session(checkModels = true).play(lowered), List("sat", "sat"))

  test("check-models: a model that fails its check answers unknown, with the error and the reason"):
    // No model the solver makes is known to fail its check: the check is given a formula the search never
    // sees, `x < 0` against `x > 0`.
    def session(check: Boolean) =
      val solver = Solver()
      solver.alsoChecked = List(Formula.Less(Term.Const("x"), Term.Num(0)))
      Session(solver, checkModels = check)
    val script = "(declare-const x Int) (assert (> x 0)) (check-sat) (get-info :reason-unknown) (get-model)"
    val responses = session(check = true).run(script)
    assertEquals(responses.head, "unknown")
    assert(responses(1).startsWith("(error \"model check: "), responses(1))
    assert(responses(2).startsWith("((:reason-unknown \"model check: "), responses(2))
    assertEquals(responses(3), "(error \"no model\")")
    assertEquals(session(check = false).run(script).head, "sat")
    // `:check-models` in the script turns the check on as the option does.
    assertEquals(session(check = false).run("(set-option :check-models true) " + script).head, "unknown")

  test("check-models: the solver checks its own model"):
    val s = Solver()
    s.checkModels = true
    s.declare("x", Nil, Sort.Int)
    s.assert(Formula.Less(Term.Const("x"), Term.Num(3)))
    assertEquals(s.solve(), s.Result.Sat)
    assert(s.model().exists(_.holds(Formula.Less(Term.Const("x"), Term.Num(3)))))

  test("rlimit and reason-unknown"):
    val script = Parser.parse("""
      (set-option :rlimit 1)
      (declare-const x Int)
      (declare-const y Int)
      (declare-fun f (Int) Int)
      (assert (or (= (f x) 1) (= (f y) 2)))
      (assert (< x y))
      (check-sat)
      (get-info :reason-unknown)
      (set-option :rlimit 1000000)
      (check-sat)
      (get-info :reason-unknown)""")
    assertEquals(
      Session.run(script),
      List("unknown", "((:reason-unknown resourceout))", "sat", "((:reason-unknown incomplete))")
    )
    assertEquals(Session.answers(script), List(None, Some(true)))
    assertEquals(Parser.parse(Printer.print(script)), script)
