; Hand-written for VIK (this repository's license): two datatype values whose array fields are equal as
; arrays and written differently, `a` and `(store a 0 1)` where `a` holds 1 at 0. `get-value` compared the
; values by structure below a constructor and answered `false` for their equality, `true` for the arrays'
; own (issue 141, 2026-11-18).
; EXPECT: sat
; EXPECT: (((= a (store a 0 1)) true) ((= (C a) (C (store a 0 1))) true) ((distinct (C a) (C (store a 0 1))) false))
; EXPECT: (((= (C a) (C (store a 0 2))) false) ((= (mk (C a) 3) (mk (C (store a 0 1)) 3)) true) ((= (mk (C a) 3) (mk (C (store a 0 1)) 4)) false))
(set-logic ALL)
(set-option :produce-models true)
(declare-datatype D ((C (arr (Array Int Int)))))
(declare-datatype P ((mk (fst D) (snd Int))))
(declare-const a (Array Int Int))
(assert (= (select a 0) 1))
(set-info :status sat)
(check-sat)
(get-value ((= a (store a 0 1)) (= (C a) (C (store a 0 1))) (distinct (C a) (C (store a 0 1)))))
(get-value ((= (C a) (C (store a 0 2))) (= (mk (C a) 3) (mk (C (store a 0 1)) 3)) (= (mk (C a) 3) (mk (C (store a 0 1)) 4))))
