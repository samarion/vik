; Hand-written for VIK (this repository's license): an array of the integers to one bit that differs from
; itself with a zero stored at 0 and with a one stored at 0 has no value left at 0. The reads at the
; witnesses of the two differences are the solver's own terms, and had no range (issue 154, 2026-11-17).
(set-logic QF_AUFBVLIA)
(declare-const a (Array Int (_ BitVec 1)))
(assert (not (= a (store a 0 #b0))))
(set-info :status sat)
(check-sat)
(assert (not (= a (store a 0 #b1))))
(set-info :status unsat)
(check-sat)
