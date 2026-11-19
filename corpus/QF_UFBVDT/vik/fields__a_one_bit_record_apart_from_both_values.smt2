; Hand-written for VIK (this repository's license): a record of one bit apart from both its values, then from
; one. The model of the `sat` gave `r` the other value only by chance: its field was an integer of any size,
; and `(mk #b0)` was the value 2 written modulo 2 (issue 126, 2026-11-19).
(set-logic QF_UFBVDT)
(set-option :produce-models true)
(declare-datatypes ((R 0)) (((mk (fld (_ BitVec 1))))))
(declare-const r R)
(assert (distinct r (mk #b0)))
(push 1)
(assert (distinct r (mk #b1)))
(set-info :status unsat)
(check-sat)
(pop 1)
(set-info :status sat)
(check-sat)
(get-model)
