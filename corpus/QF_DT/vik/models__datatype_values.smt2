; Hand-written for VIK (this repository's license): datatype values in a model. A class without a
; constructor node was an abstract element, which is no datatype value, and a constructor's field invented
; by a tester's expansion was valued 0 even where `(not (= x (mk 0)))` forbids it (issue 26, 2026-09-05).
; EXPECT: sat
; EXPECT: ((define-fun q () Q (mk 1)) (define-fun x () Lst (cons 3 (cons 2 nil))) (define-fun y () Lst (cons 5 (cons 4 nil))))
; EXPECT: ((x (cons 3 (cons 2 nil))) (y (cons 5 (cons 4 nil))) (q (mk 1)) (((_ is cons) x) true) ((n q) 1))
(set-logic ALL)
(set-option :produce-models true)
(declare-datatypes ((Lst 0)) (((nil) (cons (hd Int) (tl Lst)))))
(declare-datatypes ((Q 0)) (((mk (n Int)))))
(declare-const x Lst)
(declare-const y Lst)
(declare-const q Q)
(assert ((_ is cons) x))
(assert (not (= x y)))
(assert (not (= q (mk 0))))
(set-info :status sat)
(check-sat)
(get-model)
(get-value (x y q ((_ is cons) x) (n q)))
