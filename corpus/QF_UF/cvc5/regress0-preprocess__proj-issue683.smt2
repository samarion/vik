; From cvc5: regress0/preprocess/proj-issue683.smt2 (modified BSD, LICENSES/cvc5.txt)
; EXPECT: unsat
; logic: QF_UF, the smallest the script fits, for ALL (prune logic)
(set-logic QF_UF)
(set-info :status unsat)
(check-sat-assuming (false (= (- 0.0) 0.0)))
