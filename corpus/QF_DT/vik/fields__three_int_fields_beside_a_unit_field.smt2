; Hand-written for VIK (this repository's license): three `of-Int` values pairwise apart: an infinite field
; next to a finite one, which the bounds leave alone (issue 125, 2026-11-17).
; EXPECT: sat
; EXPECT: ((define-fun x () Val (of-Int 1)) (define-fun y () Val (of-Int 2)) (define-fun z () Val (of-Int 3)))
(set-logic ALL)
(set-option :produce-models true)
(declare-datatypes ((Unit 0) (Val 0)) (((unit)) ((of-Int (to-Int Int)) (of-Unit (to-Unit Unit)))))
(declare-const x Val)
(declare-const y Val)
(declare-const z Val)
(assert ((_ is of-Int) x))
(assert ((_ is of-Int) y))
(assert ((_ is of-Int) z))
(assert (distinct x y z))
(set-info :status sat)
(check-sat)
(get-model)
