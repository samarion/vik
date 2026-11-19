; Hand-written for VIK (this repository's license): three `of-Opt` values pairwise apart, an option of `Unit`
; having two values (issue 125, 2026-11-17).
(set-logic ALL)
(declare-datatypes ((Unit 0) (Opt 0) (Val 0)) (((unit)) ((none) (some (get Unit))) ((of-Int (to-Int Int)) (of-Opt (to-Opt Opt)))))
(declare-const x Val)
(declare-const y Val)
(declare-const z Val)
(assert ((_ is of-Opt) x))
(assert ((_ is of-Opt) y))
(assert ((_ is of-Opt) z))
(assert (distinct x y z))
(set-info :status unsat)
(check-sat)
