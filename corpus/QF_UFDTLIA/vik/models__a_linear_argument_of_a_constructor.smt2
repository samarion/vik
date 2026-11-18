; Hand-written for VIK (this repository's license): a constructor applied to `a + 1`. The argument's class,
; alone and without a variable of the simplex, got a fresh number in the model: `x = (mk 1)` with `a = 5`,
; against the first assertion (issue 137, 2026-11-18). The number invented for the field of `y`, a value
; apart from `x`, is past the argument's.
; EXPECT: sat
; EXPECT: ((define-fun a () Int 5) (define-fun x () P (mk 6)) (define-fun y () P (mk 7)))
; EXPECT: ((x (mk 6)) ((f x) 6) ((= x (mk (+ a 1))) true))
; EXPECT: sat
; EXPECT: ((x (mk 6)) (y (mk 7)) ((= x y) false))
(set-logic QF_UFDTLIA)
(set-option :produce-models true)
(declare-datatype P ((mk (f Int))))
(declare-const a Int)
(declare-const x P)
(declare-const y P)
(assert (= x (mk (+ a 1))))
(assert (= a 5))
(set-info :status sat)
(check-sat)
(get-model)
(get-value (x (f x) (= x (mk (+ a 1)))))
(assert (distinct x y))
(set-info :status sat)
(check-sat)
(get-value (x y (= x y)))
