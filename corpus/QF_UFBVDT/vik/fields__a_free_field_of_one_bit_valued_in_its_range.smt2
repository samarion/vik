; Hand-written for VIK (this repository's license): `y` differs from `x`, whose field of one bit is 1, so
; the field of `y` is 0. It is a term the solver makes, which had no range: the model valued it 2, past the
; value known, printed `#b0` in the model and `2` under `ubv_to_int` (issue 126, 2026-11-17).
; EXPECT: sat
; EXPECT: ((define-fun x () P (mk #b1)) (define-fun y () P (mk #b0)))
; EXPECT: (((ubv_to_int (f y)) 0))
(set-logic ALL)
(set-option :produce-models true)
(declare-datatype P ((mk (f (_ BitVec 1)))))
(declare-const x P)
(declare-const y P)
(assert (= (f x) #b1))
(assert (distinct x y))
(set-info :status sat)
(check-sat)
(get-model)
(get-value ((ubv_to_int (f y))))
