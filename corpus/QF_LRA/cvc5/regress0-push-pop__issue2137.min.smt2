; From cvc5: regress0/push-pop/issue2137.min.smt2 (modified BSD, LICENSES/cvc5.txt)
; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: unsat
; logic: QF_LRA, the smallest the script fits, for ALL (prune logic)
(set-logic QF_LRA)
(declare-fun a () Real)
(declare-fun b () Bool)
(assert (< 0 a))
(assert (xor b (< 0 a 0) false))
(set-info :status sat)
(check-sat)
(assert (not b))
(set-info :status unsat)
(check-sat)
