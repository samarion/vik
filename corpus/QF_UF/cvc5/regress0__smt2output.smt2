; From cvc5: regress0/smt2output.smt2 (modified BSD, LICENSES/cvc5.txt)
; This test checks the correct output behavior of SMT-LIBv2 symbols
; (sometimes they have to be |quoted| with pipes).
;
; COMMAND-LINE: -qm
; logic: QF_UF, the smallest the script fits, which set none (prune logic)
; EXPECT: sat
; EXPECT: ((define-fun |to to| () Bool true) (define-fun toto () Bool true))
(set-logic QF_UF)
(declare-fun |toto| () Bool)
(declare-fun |to to| () Bool)
(assert (and toto |to to|))
(set-info :status sat)
(check-sat)
(get-model)
