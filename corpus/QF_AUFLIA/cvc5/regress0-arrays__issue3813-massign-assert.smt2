; From cvc5: regress0/arrays/issue3813-massign-assert.smt2 (modified BSD, LICENSES/cvc5.txt)
; EXPECT: sat
; COMMAND-LINE: --produce-unsat-cores
; logic: QF_AUFLIA, the smallest the script fits, for ALL (prune logic)
(set-logic QF_AUFLIA)
(set-info :status sat)
(declare-fun a () (Array Int Bool))
(declare-fun b () (Array Int Bool))
(assert (= a (store b 0 true)))
(set-info :status sat)
(check-sat)
