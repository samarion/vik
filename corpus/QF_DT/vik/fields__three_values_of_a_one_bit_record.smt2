; Hand-written for VIK (this repository's license): the minimal script of issue 126: three values of a record
; of one bit, pairwise apart (issue 126, 2026-11-17).
(set-logic ALL)
(declare-datatype P ((mk (f (_ BitVec 1)))))
(declare-const x P)
(declare-const y P)
(declare-const z P)
(assert (distinct x y z))
(set-info :status unsat)
(check-sat)
