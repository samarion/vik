; From z3test: array.smt2 (MIT, LICENSES/z3test.txt)
; logic: QF_AUFLIA, the smallest the script fits, which set none (prune logic)
(set-logic QF_AUFLIA)

; Copyright (c) 2015 Microsoft Corporation



(define-fun a () (Array Int Int) ((as const (Array Int Int)) 0))
(assert (= (store (store a 0 1) 0 0) (store a 0 1)))
(set-info :status unsat)
(check-sat)

(reset)
(define-fun a () (Array Int Int) ((as const (Array Int Int)) 0))
(assert (= (store (store (store a 0 1) 1 2) 0 0) (store (store a 0 1) 1 2)))
(set-info :status unsat)
(check-sat)

(reset)
(define-fun a () (Array Int Int) ((as const (Array Int Int)) 0))
(assert (= (store (store (store (store a 0 1) 1 2) 2 3) 0 0) (store (store (store a 0 1) 1 2) 2 3)))
(set-info :status unsat)
(check-sat)

(reset)
(set-option :auto-config true)
(define-fun a () (Array Int Int) ((as const (Array Int Int)) 0))
(assert (= (store (store a 0 1) 0 0) (store a 0 1)))
(set-info :status unsat)
(check-sat)

(reset)
(set-option :auto-config true)
(define-fun a () (Array Int Int) ((as const (Array Int Int)) 0))
(assert (= (store (store (store a 0 1) 1 2) 0 0) (store (store a 0 1) 1 2)))
(set-info :status unsat)
(check-sat)

(reset)
(set-option :auto-config true)
(define-fun a () (Array Int Int) ((as const (Array Int Int)) 0))
(assert (= (store (store (store (store a 0 1) 1 2) 2 3) 0 0) (store (store (store a 0 1) 1 2) 2 3)))
(set-info :status unsat)
(check-sat)
