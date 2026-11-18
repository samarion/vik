; From cvc5: regress0/push-pop/issue6535-inc-solve.smt2 (modified BSD, LICENSES/cvc5.txt)
; COMMAND-LINE: -i
; EXPECT: sat
; logic: QF_UFLRA, the smallest the script fits, for ALL (prune logic)
(set-logic QF_UFLRA)
(declare-fun f0_2 (Real Real) Real)
(declare-fun x8 () Real)
(assert (= 0.0 (f0_2 x8 1.0)))
(push)
(assert (= x8 1.0))
(set-info :status sat)
(check-sat)
