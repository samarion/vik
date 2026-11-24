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

  test("a constructor's linear argument is computed from its terms"):
    // Its class, alone and without a variable of the simplex, got a fresh number: `x = (mk 1)` (issue 137).
    assertEquals(
      run("""(declare-datatype P ((mk (f Int)))) (declare-const a Int) (declare-const x P)
             (assert (= x (mk (+ a 1)))) (assert (= a 5)) (check-sat) (get-value (x (f x) (= x (mk (+ a 1)))))"""),
      List("sat", "((x (mk 6)) ((f x) 6) ((= x (mk (+ a 1))) true))")
    )
    // A lowered bit-vector operation is such a term.
    assertEquals(
      run("""(declare-datatype P ((mk (f (_ BitVec 2))))) (declare-const a (_ BitVec 2)) (declare-const x P)
             (assert (= x (mk (bvnot a)))) (assert (= a #b01)) (check-sat) (get-value (x))"""),
      List("sat", "((x (mk #b10)))")
    )
    // A number invented for another value's field is past it: `y`'s field is not the 6 of `x`'s.
    assertEquals(
      run("""(declare-datatype P ((mk (f Int)))) (declare-const a Int) (declare-const x P) (declare-const y P)
             (assert (= x (mk (+ a 1)))) (assert (= a 5)) (assert (distinct x y)) (check-sat) (get-value (x y))"""),
      List("sat", "((x (mk 6)) (y (mk 7)))")
    )
    // A selector application met only inside a linear argument is a term of the e-graph: `u`'s head is not
    // one more than itself (issue 136).
    assertEquals(
      run("""(declare-datatypes ((Lst 0)) (((nil) (cons (hd Int) (tl Lst))))) (declare-const u Lst)
             (assert (= u (cons (+ (hd u) 1) nil))) (check-sat)"""),
      List("unsat")
    )

  test("a constructor's argument mixing an integer and a real keeps its exact value"):
    // Valued by the final check's evaluator, at the model's one δ (from #208).
    assertEquals(
      run("""
        (set-option :check-models true)
        (declare-datatype P ((mk (f Real))))
        (declare-const i Int)
        (declare-const r Real)
        (declare-const x P)
        (assert (= i 2))
        (assert (= r 0.5))
        (assert (= x (mk (- r (to_real i)))))
        (check-sat)
        (get-value ((= (f x) (- 1.5))))
      """),
      List("sat", "(((= (f x) (- 1.5)) true))")
    )

  test("an array inside a datatype value is compared by its elements (issue 141)"):
    // By structure, `(C a)` and `(C (store a 0 1))` were apart where `a` and the store are equal.
    assertEquals(
      run("""(declare-datatype D ((C (arr (Array Int Int))))) (declare-const a (Array Int Int))
             (assert (= (select a 0) 1)) (check-sat)
             (get-value ((= a (store a 0 1)) (= (C a) (C (store a 0 1))) (= (C a) (C (store a 0 2)))))"""),
      List("sat", "(((= a (store a 0 1)) true) ((= (C a) (C (store a 0 1))) true) ((= (C a) (C (store a 0 2))) false))")
    )

  test("arrays written at two equal datatype values are equal (issue 180)"):
    assertEquals(
      run("""(declare-datatype D ((C (arr (Array Int Int))))) (declare-const a (Array Int Int))
             (declare-const m (Array D Int)) (assert (= (select a 0) 1)) (check-sat)
             (get-value ((= (store m (C a) 5) (store m (C (store a 0 1)) 5))))"""),
      List("sat", "(((= (store m (C a) 5) (store m (C (store a 0 1)) 5)) true))")
    )

  test("over a finite index sort, an array is the function it is at every index"):
    // "0 with `true` at 1" and "1 with `false` at 0" are one array over `Bool`; over 0..1 likewise.
    def array(index: Sort, default: Int, writes: (Term, Int)*): Term =
      writes.foldLeft(Model.constArray(Sort.Fun(List(index), Sort.Int), Term.Num(default))) { case (a, (i, v)) =>
        Model.store(a, i, Term.Num(v))
      }
    val (f, t) = (Term.Bool(Formula.False), Term.Bool(Formula.True))
    assert(Model.same(array(Sort.Bool, 0, t -> 1), array(Sort.Bool, 1, f -> 0)))
    assert(!Model.same(array(Sort.Bool, 0, t -> 1), array(Sort.Bool, 1, f -> 1)))
    val bit = Sort.IntRange(0, 1)
    assert(Model.same(array(bit, 7, Term.Num(0) -> 3, Term.Num(1) -> 4), array(bit, 3, Term.Num(1) -> 4)))
    // Over the integers an index is always left at the default.
    assert(!Model.same(array(Sort.Int, 0, Term.Num(1) -> 1), array(Sort.Int, 1, Term.Num(0) -> 0)))

  test("distinct values of a datatype can be around a new element of an uninterpreted sort (issue 127)"):
    // `c1_2`'s values to spare are around one of `U`: there was no new element to give, and `k12` and `k14`
    // were both `(c1_2 c0_0)`.
    assertEquals(
      run("""(declare-sort U 0)
             (declare-datatypes ((D0 0) (D1 0)) (((c0_0) (c0_1 (s0_1_0 U))) ((c1_0) (c1_2 (s1_2_0 D0)))))
             (declare-const x D1) (declare-const y D1)
             (assert ((_ is c1_2) x)) (assert ((_ is c1_2) y)) (assert (distinct x y))
             (check-sat) (get-value ((distinct x y)))"""),
      List("sat", "(((distinct x y) true))")
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
        "((x #b0001) (y #b0000) ((select a x) #b0101) ((select a y) #b0110) ((select arr y) 1) (a (store (store ((as const (Array (_ BitVec 4) (_ BitVec 4))) #b0000) #b0000 #b0110) #b0001 #b0101)))"
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

  test("a default datatype value is ground"):
    // The first constructor leads back to its sort, where the default ended in an abstract element:
    // `y` was `(rec (rec @D!2))` (issue 140). The classes of `y` and of its fields take distinct values (issue
    // 127), and the default ends each of them.
    assertEquals(
      run("""(declare-datatype D ((rec (next D)) (base (n Bool)))) (declare-const y D)
             (check-sat) (get-model) (get-value ((next y) (next (next y))))"""),
      List(
        "sat",
        "((define-fun y () D (rec (rec (rec (base false))))))",
        "(((next y) (rec (rec (base false)))) ((next (next y)) (rec (base false))))"
      )
    )
    // Two sorts that recur through each other: `u` was `(a1 (b1 (a1 @B!1)))`.
    assertEquals(
      run("""(declare-datatypes ((A 0) (B 0)) (((a1 (ab B))) ((b1 (ba A)) (b2 (bz Bool))))) (declare-const u A)
             (check-sat) (get-model)"""),
      List("sat", "((define-fun u () A (a1 (b1 (a1 (b1 (a1 (b2 false))))))))")
    )

  test("a function symbol is answered as a lambda over its graph"):
    // It was echoed as its own value, `((f f))` (issue 50).
    assertEquals(
      run(
        "(declare-sort U 0) (declare-fun f (U) U) (declare-const a U) (assert (= (f a) a)) (check-sat) (get-value (f a))"
      ),
      List("sat", "((f (lambda ((x!0 U)) (ite (= x!0 @U!0) @U!0 @U!0))) (a @U!0))")
    )
