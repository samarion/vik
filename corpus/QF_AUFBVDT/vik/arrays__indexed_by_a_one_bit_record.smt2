; Hand-written for VIK (this repository's license): two arrays indexed by a record of one bit, equal at both
; its values and apart. The extensionality witness is a third index, whose field had no range (issue 126,
; 2026-11-19).
(set-logic QF_AUFBVDT)
(declare-datatypes ((R 0)) (((mk (fld (_ BitVec 1))))))
(declare-const a (Array R Int))
(declare-const b (Array R Int))
(assert (= (select a (mk #b0)) (select b (mk #b0))))
(push 1)
(assert (= (select a (mk #b1)) (select b (mk #b1))))
(assert (distinct a b))
(set-info :status unsat)
(check-sat)
(pop 1)
(assert (distinct a b))
(set-info :status sat)
(check-sat)
