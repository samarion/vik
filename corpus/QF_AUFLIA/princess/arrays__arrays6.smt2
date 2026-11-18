; From princess: arrays/arrays6.smt2 (BSD, LICENSES/princess.txt)
; logic: QF_AUFLIA, the smallest the script fits, for AUFLIA (prune logic)
(set-logic QF_AUFLIA)

(declare-fun arr () (Array Int Int))
(declare-const x Int)
(declare-const y Int)

(assert (= (store ((as const (Array Int Int)) 0) x 10) arr))
(assert (not (>= (select arr y) 0)))

(set-info :status unsat)
(check-sat)

