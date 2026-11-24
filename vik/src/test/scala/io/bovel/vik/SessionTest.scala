package io.bovel.vik

import io.bovel.smtlib.Term.Const
import io.bovel.smtlib as s2

class SessionTest extends munit.FunSuite:
  test("commands arrive piece by piece, each in the scope of the earlier ones") {
    val s = Session()
    s.run("(declare-const x Int) (declare-const y Int) (define-fun big ((z Int)) Bool (> z 100))")
    s.assert("(< x y)")
    assertEquals(s.checkSat(), Some(true))
    s.push()
    s.assert("(big x)") // the macro of the first piece
    s.assert(s2.Formula.Cmp(s2.CmpOp.Lt, List(Const("y"), Const("x")))) // a tree, in the same scope
    assertEquals(s.checkSat(), Some(false))
    s.pop()
    assertEquals(s.checkSat(), Some(true))
  }

  test("checkSatAssuming: the assumptions hold for that check alone") {
    val s = Session()
    s.run("(declare-const a Bool)")
    s.assert("a")
    assertEquals(s.checkSatAssuming(List(s2.Formula.Not(s2.Formula.Pred(Const("a"))))), Some(false))
    assertEquals(s.checkSat(), Some(true))
  }

  test("a lowered convenience keeps its definitions across the pieces") {
    val s = Session()
    s.run("(set-option :produce-models true) (declare-const x Int) (declare-const y Int)")
    s.assert("(= y (ite (< x 0) 0 x))") // the ite becomes a defined constant, declared before the assertion
    s.assert("(< x (- 3))")
    assertEquals(s.checkSat(), Some(true))
    assertEquals(s.model().map(_.value(Term.Const("y"))), Some(Term.Num(0)))
    assertEquals(s.run("(get-value (y))"), List("((y 0))"))
  }

  test("the responses of each piece, and the state of the whole") {
    val s = Session()
    assertEquals(s.run("(declare-const p Bool) (assert (! p :named a)) (check-sat)"), List("sat"))
    assertEquals(s.run("(assert (! (not p) :named b)) (check-sat) (get-unsat-core)"), List("unsat", "(a b)"))
    assertEquals(s.unsatCore, List("a", "b"))
    assertEquals(s.run("(reset) (declare-const p Int) (assert (> p 0)) (check-sat)"), List("sat"))
  }

  test("an unsat among the top-level assertions holds for every later check") {
    // A conflict found at decision level 0 (issue 37): plain, under an assumption, under a push, with
    // one more assertion, on Booleans and on the bounds of one integer.
    val s = Session()
    s.run("(declare-const u Bool) (declare-const f Bool) (declare-const q Bool)")
    s.run("(assert (or (not u) (not f))) (assert f) (assert u)")
    assertEquals(s.checkSat(), Some(false))
    assertEquals(s.checkSat(), Some(false))
    assertEquals(s.run("(check-sat-assuming (q))"), List("unsat"))
    s.push()
    s.assert("q")
    assertEquals(s.checkSat(), Some(false))
    s.pop()
    s.assert("(or u q)")
    assertEquals(s.checkSat(), Some(false))
    val t = Session()
    t.run("(declare-const x Int) (assert (<= x 5)) (assert (not (<= x 7)))")
    assertEquals(t.run("(check-sat) (check-sat) (check-sat-assuming ((<= x 100)))"), List("unsat", "unsat", "unsat"))
  }

  test("a budget spent before the lemmas answers unknown") {
    // The array lemmas take rounds of the lemma loop, which the budget stops (issue 38).
    val text = """
      (declare-sort E 0)
      (declare-const a (Array Int E)) (declare-const b (Array Int E)) (declare-const x E) (declare-const y E)
      (assert (= a (store b 0 x))) (assert (= (select a 0) y)) (assert (not (= x y)))
      (check-sat)"""
    assertEquals(Session(fuel = 0).run(text), List("unknown"))
    assertEquals(Session().run(text), List("unsat"))
  }

  test("a declaration leaves with its level") {
    // Popped, the name is free for another sort (issue 40); with `:global-declarations` it stays.
    val s = Session()
    s.run("(declare-const a Int) (push 1) (declare-const x Int) (assert (> x 0))")
    assertEquals(s.checkSat(), Some(true))
    s.run("(pop 1) (declare-const x Bool) (declare-fun f (Bool) Int)")
    s.run("(assert (and (not x) (distinct (f x) (f false))))")
    assertEquals(s.checkSat(), Some(false))
    s.run(
      "(reset-assertions) (push 1) (define-fun p () Bool true) (assert p) (pop 1) (declare-const p Bool) (assert (not p))"
    )
    assertEquals(s.checkSat(), Some(true))
    intercept[s2.Smt2Error](s.run("(push 1) (declare-const q Int) (pop 1) (assert (= q 1))"))
    val g = Session()
    g.run("(set-option :global-declarations true) (push 1) (declare-const q Int) (pop 1) (assert (= q 1))")
    assertEquals(g.checkSat(), Some(true))
  }

  test("a datatype leaves with its level") {
    val s = Session()
    s.run("(push 1) (declare-datatype D ((a) (b))) (declare-const d D) (assert (= d a))")
    assertEquals(s.checkSat(), Some(true))
    s.run("(pop 1) (declare-datatype D ((c))) (declare-const e D) (assert (= e c))")
    assertEquals(s.checkSat(), Some(true))
    s.run("(reset-assertions) (push 1) (declare-datatype E ((m) (n))) (pop 1) (declare-const m Int) (assert (= m 5))")
    assertEquals(s.checkSat(), Some(true))
  }

  test("a popped datatype does not constrain a sort of its name (issue 144)") {
    // The encoder of the first check knew `D` as a datatype of two values, and kept it past the pop.
    val s = Session()
    s.run("(push 1) (declare-datatype D ((A) (B))) (declare-const w D)")
    assertEquals(s.checkSat(), Some(true))
    s.run("(pop 1) (declare-sort D 0) (declare-const x D) (declare-const y D) (declare-const z D)")
    s.run("(assert (distinct x y z))")
    assertEquals(s.checkSat(), Some(true))
    // The constructors' names too, declared again as constants of that sort: no longer distinct values.
    s.run("(declare-const A D) (declare-const B D) (assert (= A B))")
    assertEquals(s.checkSat(), Some(true))
  }

  test("a pop of more levels than are open is an error, and changes nothing (issue 178)") {
    def run(script: String) = Session.run(s2.Parser.parse(script))
    assertEquals(
      run("(declare-const x Int) (pop 1) (assert (> x 0)) (check-sat)"),
      List(
        "(error \"pop 1: the stack depth is 0\")",
        "sat"
      )
    )
    // `reset-assertions` drops the levels: there is none left to pop.
    assertEquals(
      run("(declare-const x Int) (push 1) (assert (> x 0)) (reset-assertions) (pop 1) (check-sat)"),
      List(
        "(error \"pop 1: the stack depth is 0\")",
        "sat"
      )
    )
    // Refused whole: the level stays open, with its declaration and its assertion.
    assertEquals(
      run("(declare-const x Int) (push 1) (declare-const y Int) (assert (< y 0)) (pop 2) (assert (> y 0)) (check-sat)"),
      List("(error \"pop 2: the stack depth is 1\")", "unsat")
    )
    // Through the API too.
    val s = Session()
    assertEquals(s.run("(pop 1)"), List("(error \"pop 1: the stack depth is 0\")"))
    s.pop()
    s.run("(declare-const z Int)")
    assertEquals(s.checkSat(), Some(true))
  }

  test("exit ends the script") {
    // What follows is not read, not even parsed (issue 52).
    val s = Session()
    assertEquals(
      s.run("(declare-const p Bool) (assert p) (check-sat) (exit) (assert (not p)) (check-sat) (not a command)"),
      List("sat")
    )
    assertEquals(s.run("(check-sat)"), Nil)
  }

  test("an unknown symbol is an error of the text, not of the solver") {
    val s = Session()
    intercept[s2.Smt2Error](s.assert("(< x 1)"))
    s.run("(declare-const x Int)")
    s.assert("(< x 1)")
    assertEquals(s.checkSat(), Some(true))
  }

  test("pop through the API clears the lowering caches (issue 22)"):
    val s = Session()
    s.run("(set-logic QF_LRA)(declare-const x Real)")
    s.push()
    s.assert("(< x 0.5)")
    assertEquals(s.checkSat(), Some(true))
    s.pop()
    s.assert("(> x 0.5)")
    s.assert("(< x 0.25)")
    assertEquals(s.checkSat(), Some(false), "x > 1/2 and x < 1/4: the constant for 1/2 must keep its definition")
