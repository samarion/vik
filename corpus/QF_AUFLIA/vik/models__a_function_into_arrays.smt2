; Hand-written for VIK (this repository's license): a declared function whose result is an array. The model
; left it out entirely and a value query returned the application unevaluated (issue 27, 2026-09-05).
; EXPECT: sat
; EXPECT: (((select (g 0) 1) 5) ((select (g 3) 2) 7) ((g 0) (store (store ((as const (Array Int Int)) 0) 1 5) 2 7)))
; EXPECT: ((define-fun k () Int 3) (define-fun g ((x!0 Int)) (Array Int Int) (ite (= x!0 0) (store (store ((as const (Array Int Int)) 0) 1 5) 2 7) (ite (= x!0 3) (store (store ((as const (Array Int Int)) 0) 1 5) 2 7) ((as const (Array Int Int)) 0)))))
(set-logic QF_AUFLIA)
(set-option :produce-models true)
(declare-fun g (Int) (Array Int Int))
(declare-const k Int)
(assert (= (select (g 0) 1) 5))
(assert (= (select (g k) 2) 7))
(assert (= k 3))
(set-info :status sat)
(check-sat)
(get-value ((select (g 0) 1) (select (g 3) 2) (g 0)))
(get-model)
