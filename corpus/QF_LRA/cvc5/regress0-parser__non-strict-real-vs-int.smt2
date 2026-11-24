; From cvc5: regress0/parser/non-strict-real-vs-int.smt2 (modified BSD, LICENSES/cvc5.txt)
; COMMAND-LINE: --no-strict-parsing
; EXPECT: sat
; logic: QF_LRA, the smallest the script fits, for ALL (prune logic)
(set-logic QF_LRA)
(set-info :status sat)
(declare-fun x () Real)
(assert (= x 10))
(assert (<= (+ x 1) 20))
(set-info :status sat)
(check-sat)
