; Hand-written for VIK (this repository's license): an array of arrays — a
; matrix of integers — read and written at both levels, with the model of
; the whole and `get-value` through both.
; EXPECT: sat
; EXPECT: (((select (select n 1) 2) 7) ((select (select n 1) 3) 4) ((select (select m 1) 2) 3) ((= n m) false) ((= (select n 1) row) true) ((select (select n 0) 0) 0))
; EXPECT: ((define-fun m () (Array Int (Array Int Int)) (store ((as const (Array Int (Array Int Int))) ((as const (Array Int Int)) 0)) 1 (store (store ((as const (Array Int Int)) 0) 2 3) 3 4))) (define-fun n () (Array Int (Array Int Int)) (store (store (store ((as const (Array Int (Array Int Int))) ((as const (Array Int Int)) 0)) 1 (store (store ((as const (Array Int Int)) 0) 2 3) 3 4)) 1 (store (store (store (store (store ((as const (Array Int Int)) 0) 2 3) 3 4) 2 7) 2 7) 3 4)) 1 (store (store (store (store (store ((as const (Array Int Int)) 0) 2 3) 3 4) 2 7) 2 7) 3 4))) (define-fun row () (Array Int Int) (store (store (store (store (store ((as const (Array Int Int)) 0) 2 3) 3 4) 2 7) 2 7) 3 4)))
; EXPECT: unsat
; EXPECT: sat
; EXPECT: (((select (select m 0) 5) 9))
(set-logic QF_ALIA)
(set-option :produce-models true)
(declare-const m (Array Int (Array Int Int)))
(declare-const row (Array Int Int))
(declare-const n (Array Int (Array Int Int)))
(assert (= row (store (select m 1) 2 7)))
(assert (= n (store m 1 row)))
(assert (= (select (select m 1) 2) 3))
(assert (= (select (select m 1) 3) 4))
(set-info :status sat)
(check-sat)
(get-value ((select (select n 1) 2) (select (select n 1) 3) (select (select m 1) 2) (= n m) (= (select n 1) row) (select (select n 0) 0)))
(get-model)
(push 1)
(assert (= (select (select n 1) 2) 3))
(set-info :status unsat)
(check-sat)
(pop 1)
(push 1)
(assert (= (select (select n 0) 5) (select (select m 0) 5)))
(assert (= (select (select n 0) 5) 9))
(set-info :status sat)
(check-sat)
(get-value ((select (select m 0) 5)))
(pop 1)
