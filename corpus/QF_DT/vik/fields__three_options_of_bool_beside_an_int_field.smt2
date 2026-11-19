; Hand-written for VIK (this repository's license): three `of-Opt` values pairwise apart, as many as `(Opt
; Bool)` has. The model gave all three `(of-Opt none)` before the fields were bounded (issue 125, 2026-11-17).
; EXPECT: sat
; EXPECT: ((define-fun x () Val (of-Opt none)) (define-fun y () Val (of-Opt (some false))) (define-fun z () Val (of-Opt (some true))))
(set-logic ALL)
(set-option :produce-models true)
(declare-datatypes ((Opt 0) (Val 0)) (((none) (some (get Bool))) ((of-Int (to-Int Int)) (of-Opt (to-Opt Opt)))))
(declare-const x Val)
(declare-const y Val)
(declare-const z Val)
(assert ((_ is of-Opt) x))
(assert ((_ is of-Opt) y))
(assert ((_ is of-Opt) z))
(assert (distinct x y z))
(set-info :status sat)
(check-sat)
(get-model)
