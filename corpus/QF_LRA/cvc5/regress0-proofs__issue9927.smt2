; From cvc5: regress0/proofs/issue9927.smt2 (modified BSD, LICENSES/cvc5.txt)
; EXPECT: unsat
(set-logic QF_LRA)
(declare-fun b () Bool)
(assert (= 0.0 (ite b 2.0 1.0)))
(set-info :status unsat)
(check-sat)