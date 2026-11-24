; From cvc5: regress0/smtlib/issue4077.smt2 (modified BSD, LICENSES/cvc5.txt)
; COMMAND-LINE: --incremental
; EXPECT: sat
; logic: QF_BV, the smallest the script fits, for BV (prune logic)

; Use a quantified logic to make sure that TheoryEngine creates a master
; equality engine
(set-option :global-declarations true)
(set-logic QF_BV)
(declare-const x (_ BitVec 4))
(push)
(reset-assertions)
(assert (bvslt (bvsrem (_ bv1 4) x) (_ bv1 4)))
(set-info :status sat)
(check-sat)
