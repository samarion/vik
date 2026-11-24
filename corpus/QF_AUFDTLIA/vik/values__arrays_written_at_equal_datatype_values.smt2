; Hand-written for VIK (this repository's license): two arrays written at the datatype values `(C a)` and
; `(C (store a 0 1))`, which are one value when `a` holds 1 at 0. `get-value` keyed the writes by the way the
; indices are written and answered `false` for the arrays' equality (issue 180, 2026-11-18).
; EXPECT: sat
; EXPECT: (((= (store m (C a) 5) (store m (C (store a 0 1)) 5)) true))
(set-logic ALL)
(set-option :produce-models true)
(declare-datatype D ((C (arr (Array Int Int)))))
(declare-const a (Array Int Int))
(declare-const m (Array D Int))
(assert (= (select a 0) 1))
(set-info :status sat)
(check-sat)
(get-value ((= (store m (C a) 5) (store m (C (store a 0 1)) 5))))
