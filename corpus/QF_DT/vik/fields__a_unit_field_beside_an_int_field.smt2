; Hand-written for VIK (this repository's license): the script of issue 125. `Val` is infinite through `of-
; Int`, and its `of-Unit` values are one, `Unit` having one value; no term of the script names their fields,
; which the testers' expansion invents. Those had no tester disjunction under an infinite datatype, so the two
; values stayed apart, and the answer was sat (issue 125, 2026-11-17).
(set-logic ALL)
(declare-datatypes ((Unit 0) (Val 0)) (((unit)) ((of-Int (to-Int Int)) (of-Unit (to-Unit Unit)))))
(declare-const x Val)
(declare-const y Val)
(assert ((_ is of-Unit) x))
(assert ((_ is of-Unit) y))
(assert (not (= x y)))
(set-info :status unsat)
(check-sat)
