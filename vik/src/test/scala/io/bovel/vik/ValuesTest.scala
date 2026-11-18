package io.bovel.vik

import io.bovel.smtlib.Parser

/** `get-value` and `get-model`: values computed from the model at the script's
 *  sorts, whatever the lowering minted on the way.
 */
class ValuesTest extends munit.FunSuite:
  private def run(text: String): List[String] = Session.run(Parser.parse("(set-option :produce-models true)\n" + text))

  test("is_int and to_int of terms that are not literals"):
    // Read through the lowered term, `floor!N` had no value: false, and the constant's name (issue 45).
    assertEquals(
      run(
        "(declare-const r Real) (assert (= r 3.0)) (check-sat) (get-value ((is_int r) (is_int (+ r 0.5)) (to_int (+ r 0.5)) (to_int (- r 0.5))))"
      ),
      List("sat", "(((is_int r) true) ((is_int (+ r 0.5)) false) ((to_int (+ r 0.5)) 3) ((to_int (- r 0.5)) 2))")
    )

  test("a define-fun named like a minted constant keeps its own value"):
    // `ite!1` the macro, `ite!N` the lowering's constant for the term-level ite (issue 46).
    assertEquals(
      run(
        "(define-fun ite!1 () Int 5) (declare-const b Bool) (declare-const x Int) (assert b) (assert (= x (ite b 1 2))) (check-sat) (get-value (ite!1 x))"
      ),
      List("sat", "((ite!1 5) (x 1))")
    )

  test("bit-vectors inside datatypes and arrays are written as bit-vectors"):
    // At their fields' sorts, and over a constant array of the script's sort (issue 47).
    assertEquals(
      run("""(declare-datatype P ((mk (fst (_ BitVec 4)) (snd Int)))) (declare-const p P)
             (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
             (assert (= p (mk #xA 7))) (assert (= (select a #x01) #x05)) (check-sat)
             (get-value (p (fst p) (select a #x01) (mk (bvadd (fst p) #x1) 2))) (get-model)"""),
      List(
        "sat",
        "((p (mk #b1010 7)) ((fst p) #b1010) ((select a #x01) #b00000101) ((mk (bvadd (fst p) #x1) 2) (mk #b1011 2)))",
        "((define-fun a () (Array (_ BitVec 8) (_ BitVec 8)) (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) #b00000000) #b00000001 #b00000101)) (define-fun p () P (mk #b1010 7)))"
      )
    )

  test("an array indexed by bit-vectors is read at its indices"):
    // The indices were abstract elements, `|@(_ BitVec 4)!0|`: a read at `x` missed its row (issue 138).
    assertEquals(
      run(
        """(declare-const a (Array (_ BitVec 4) (_ BitVec 4))) (declare-const x (_ BitVec 4))
             (declare-const y (_ BitVec 4)) (declare-const arr (Array (_ BitVec 4) Int))
             (declare-const rest (Array (_ BitVec 4) Int)) (assert (= (select a x) #x5)) (assert (= (select a y) #x6))
             (assert (= arr (store rest y 1))) (check-sat) (get-value (x y (select a x) (select a y) (select arr y) a))"""
      ),
      List(
        "sat",
        "((x #b0000) (y #b0001) ((select a x) #b0101) ((select a y) #b0110) ((select arr y) 1) (a (store (store ((as const (Array (_ BitVec 4) (_ BitVec 4))) #b0000) #b0000 #b0101) #b0001 #b0110)))"
      )
    )

  test("operations under a select, an ite, a macro: literals of their sort"):
    // Where the lowering mints constants, the value is computed instead (issue 48).
    assertEquals(
      run("""(declare-const x (_ BitVec 4)) (declare-const by (_ BitVec 4)) (declare-const p Bool)
             (declare-const a (Array (_ BitVec 4) (_ BitVec 4))) (declare-const arr (Array (_ BitVec 4) (_ BitVec 4)))
             (define-fun g ((y (_ BitVec 4))) (_ BitVec 4) (bvadd y #b0001))
             (assert (= x #b0011)) (assert (= by #b0111)) (assert p) (assert (= (select a #b0100) #b0111)) (check-sat)
             (get-value ((select a (bvadd x #b0001)) (g x) (select arr x) (bvudiv (ite (bvsle by #b0110) by by) #b0011)
                         ((_ extract 2 1) (ite (bvult by #b1000) by #b0111)) (ite (=> p (bvule x #b0000)) #b0101 by)
                         (bvsmod #b0111 #b1101) (bvudiv by #b0000) (bvashr #b1000 #b0110) ((_ rotate_left 5) by)))"""),
      List(
        "sat",
        "(((select a (bvadd x #b0001)) #b0111) ((g x) #b0100) ((select arr x) #b0000) ((bvudiv (ite (bvsle by #b0110) by by) #b0011) #b0010) (((_ extract 2 1) (ite (bvult by #b1000) by #b0111)) #b11) ((ite (=> p (bvule x #b0000)) #b0101 by) #b0111) ((bvsmod #b0111 #b1101) #b1110) ((bvudiv by #b0000) #b1111) ((bvashr #b1000 #b0110) #b1111) (((_ rotate_left 5) by) #b1110))"
      )
    )

  test("a function on a store finds its row"):
    // Array arguments compared as arrays, not as terms (issue 49).
    assertEquals(
      run(
        "(declare-const a (Array Int Int)) (declare-fun f ((Array Int Int)) Int) (assert (= (f (store a 0 1)) 7)) (assert (= (f a) 3)) (check-sat) (get-value ((f (store a 0 1)) (f (store (store a 0 1) 0 1))))"
      ),
      List("sat", "(((f (store a 0 1)) 7) ((f (store (store a 0 1) 0 1)) 7))")
    )

  test("an array field of a datatype value is an array"):
    // It was an abstract element, `|@(-> Int Int)!0|`: `x` was not `(C a)` in the model, and arithmetic
    // on a read of the field threw `not a number` (issue 139).
    assertEquals(
      run(
        """(declare-datatype D ((C (arr (Array Int Int))))) (declare-const x D) (declare-const y D)
           (declare-const a (Array Int Int)) (assert (= x (C a))) (assert (= (select a 3) 7)) (assert ((_ is C) y))
           (check-sat) (get-value (x (select (arr x) 3) (+ (select (arr y) 0) 1)))"""
      ),
      List(
        "sat",
        "((x (C (store ((as const (Array Int Int)) 0) 3 7))) ((select (arr x) 3) 7) ((+ (select (arr y) 0) 1) 1))"
      )
    )

  test("a function symbol is answered as a lambda over its graph"):
    // It was echoed as its own value, `((f f))` (issue 50).
    assertEquals(
      run(
        "(declare-sort U 0) (declare-fun f (U) U) (declare-const a U) (assert (= (f a) a)) (check-sat) (get-value (f a))"
      ),
      List("sat", "((f (lambda ((x!0 U)) (ite (= x!0 @U!0) @U!0 @U!0))) (a @U!0))")
    )
