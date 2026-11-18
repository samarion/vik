; From cvc5: regress0/cores/issue3455.smt2 (modified BSD, LICENSES/cvc5.txt)
; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: sat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
; logic: QF_LRA, the smallest the script fits, for ALL (prune logic)
(set-logic QF_LRA)
(declare-fun x0 () Real)
(set-info :status sat)
(check-sat)
(assert (<= (* x0 (- 1.0)) 0.0))
(assert (or (>= 0.0 x0) (> (+ 1.0 x0) (- 12.0))))
(set-info :status sat)
(check-sat)
(push)
(assert (<= x0 (- 13.0)))
(set-info :status unsat)
(check-sat)
(set-info :status unsat)
(check-sat)
(set-info :status unsat)
(check-sat)
