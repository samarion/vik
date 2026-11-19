; Hand-written for VIK (this repository's license): three `of-Bool` values pairwise apart, with `Val` finite:
; its fields were expanded, but only those of a datatype sort, so the `Bool` ones were never decided (issue 125,
; 2026-11-17).
(set-logic QF_DT)
(declare-datatypes ((Unit 0) (Val 0)) (((unit)) ((of-Unit (to-Unit Unit)) (of-Bool (to-Bool Bool)))))
(declare-const x Val)
(declare-const y Val)
(declare-const z Val)
(assert ((_ is of-Bool) x))
(assert ((_ is of-Bool) y))
(assert ((_ is of-Bool) z))
(assert (distinct x y z))
(set-info :status unsat)
(check-sat)
