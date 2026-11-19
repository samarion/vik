; Hand-written for VIK (this repository's license): the script of issue 125 with a field of a declared sort in
; place of `Int`: answered sat since datatypes came in (6782b292), where an `Int` field was refused (issue 125,
; 2026-11-17).
(set-logic QF_UFDT)
(declare-sort U 0)
(declare-datatypes ((Unit 0) (Val 0)) (((unit)) ((of-Opaque (to-Opaque U)) (of-Unit (to-Unit Unit)))))
(declare-const x Val)
(declare-const y Val)
(assert ((_ is of-Unit) x))
(assert ((_ is of-Unit) y))
(assert (not (= x y)))
(set-info :status unsat)
(check-sat)
