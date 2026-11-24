; From cvc5: regress0/arrays/dd_ios_t1_norm_op.smt2 (modified BSD, LICENSES/cvc5.txt)
; EXPECT: unsat
; logic: QF_AUFLIA, the smallest the script fits, for ALL (prune logic)
(set-logic QF_AUFLIA)
(declare-fun a () (Array Int Int))
(declare-fun i () Int)
(assert (= (store a (+ i 2) 0) (store (store (store (store (store (store a (+ i 3) 0) (+ i 2) 1) (+ i 1) 0) i 0) (+ i 5) 0) i 0)))
(set-info :status unsat)
(check-sat)
