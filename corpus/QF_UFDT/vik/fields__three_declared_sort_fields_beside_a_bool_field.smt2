; Hand-written for VIK (this repository's license): three `of-U` values pairwise apart, `U` a declared sort:
; as many values as needed (issue 125, 2026-11-17).
; EXPECT: sat
; EXPECT: ((define-fun x () Val (of-U @U!0)) (define-fun y () Val (of-U @U!1)) (define-fun z () Val (of-U @U!2)))
(set-logic QF_UFDT)
(set-option :produce-models true)
(declare-sort U 0)
(declare-datatypes ((Val 0)) (((of-U (to-U U)) (of-Bool (to-Bool Bool)))))
(declare-const x Val)
(declare-const y Val)
(declare-const z Val)
(assert ((_ is of-U) x))
(assert ((_ is of-U) y))
(assert ((_ is of-U) z))
(assert (distinct x y z))
(set-info :status sat)
(check-sat)
(get-model)
