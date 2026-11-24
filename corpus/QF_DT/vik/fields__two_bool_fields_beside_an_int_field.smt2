; Hand-written for VIK (this repository's license): two `of-Bool` values apart, which `Bool` allows. The model
; gave both `(of-Bool false)` before the fields were bounded (issue 125, 2026-11-17).
; EXPECT: sat
; EXPECT: ((define-fun x () Val (of-Bool false)) (define-fun y () Val (of-Bool true)))
(set-logic ALL)
(set-option :produce-models true)
(declare-datatypes ((Val 0)) (((of-Int (to-Int Int)) (of-Bool (to-Bool Bool)))))
(declare-const x Val)
(declare-const y Val)
(assert ((_ is of-Bool) x))
(assert ((_ is of-Bool) y))
(assert (distinct x y))
(set-info :status sat)
(check-sat)
(get-model)
