; Hand-written for VIK (this repository's license): datatype values with an array field, `x` built from
; an array the script reads and `y` known by its tester only. The model gave the field an abstract
; element, `|@(-> Int Int)!0|`, in place of the array: `(= x (C a 4))` was false in the model of the
; script that asserts it, z3 refused the model's text for the unknown constant, and `get-value` threw
; `not a number` on arithmetic over a read of the field (issue 139, 2026-11-18).
; EXPECT: sat
; EXPECT: ((x (C (store ((as const (Array Int Int)) 0) 3 7) 4)) ((arr x) (store ((as const (Array Int Int)) 0) 3 7)) ((select (arr x) 3) 7) ((+ (select (arr y) 1) 1) 6) ((= (arr x) a) true))
; EXPECT: ((define-fun a () (Array Int Int) (store ((as const (Array Int Int)) 0) 3 7)) (define-fun x () D (C (store ((as const (Array Int Int)) 0) 3 7) 4)) (define-fun y () D (C (store ((as const (Array Int Int)) 0) 1 5) 8)))
(set-logic ALL)
(set-option :produce-models true)
(declare-datatype D ((C (arr (Array Int Int)) (len Int))))
(declare-const x D)
(declare-const y D)
(declare-const a (Array Int Int))
(assert (= x (C a 4)))
(assert (= (select a 3) 7))
(assert ((_ is C) y))
(assert (= (select (arr y) 1) 5))
(set-info :status sat)
(check-sat)
(get-value (x (arr x) (select (arr x) 3) (+ (select (arr y) 1) 1) (= (arr x) a)))
(get-model)
