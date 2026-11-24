; From cvc5: regress0/push-pop/issue7479-global-decls.smt2 (modified BSD, LICENSES/cvc5.txt)
; COMMAND-LINE: -i
; EXPECT: unsat
; logic: QF_LIA, the smallest the script fits, for ALL (prune logic)
(set-logic QF_LIA)
(set-option :global-declarations true)
(define-fun y () Bool (> 0 0))
(assert y)
(push)
(set-info :status unsat)
(check-sat)
