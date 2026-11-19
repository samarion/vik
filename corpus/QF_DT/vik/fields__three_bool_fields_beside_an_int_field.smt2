; Hand-written for VIK (this repository's license): three `of-Bool` values pairwise apart, `Bool` having two
; values; the fields the testers' expansion invents were never decided true or false (issue 125, 2026-11-17).
(set-logic ALL)
(declare-datatypes ((Val 0)) (((of-Int (to-Int Int)) (of-Bool (to-Bool Bool)))))
(declare-const x Val)
(declare-const y Val)
(declare-const z Val)
(assert ((_ is of-Bool) x))
(assert ((_ is of-Bool) y))
(assert ((_ is of-Bool) z))
(assert (distinct x y z))
(set-info :status unsat)
(check-sat)
