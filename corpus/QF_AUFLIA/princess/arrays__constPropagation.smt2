; From princess: arrays/constPropagation.smt2 (BSD, LICENSES/princess.txt)
; logic: QF_AUFLIA, the smallest the script fits, which set none (prune logic)
(set-logic QF_AUFLIA)


(declare-const y Int)
(declare-const z Int)
(declare-const y2 Int)
(declare-const z2 Int)

(assert (= (store ((as const (Array Int Int)) y) 2 y2)
           (store ((as const (Array Int Int)) z) 2 z2)))
(assert (not (= y z)))
(set-info :status unsat)
(check-sat)
