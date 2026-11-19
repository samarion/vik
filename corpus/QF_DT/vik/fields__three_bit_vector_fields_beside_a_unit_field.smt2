; Hand-written for VIK (this repository's license): three `of-BV` values pairwise apart, with `Val` finite: to
; the solver, its field is an `Int`, so `Val` is infinite (issue 126, 2026-11-17).
(set-logic ALL)
(declare-datatypes ((Unit 0) (Val 0)) (((unit)) ((of-Unit (to-Unit Unit)) (of-BV (to-BV (_ BitVec 1))))))
(declare-const x Val)
(declare-const y Val)
(declare-const z Val)
(assert ((_ is of-BV) x))
(assert ((_ is of-BV) y))
(assert ((_ is of-BV) z))
(assert (distinct x y z))
(set-info :status unsat)
(check-sat)
