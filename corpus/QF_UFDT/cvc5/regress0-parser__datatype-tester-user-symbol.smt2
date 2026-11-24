; From cvc5: regress0/parser/datatype-tester-user-symbol.smt2 (modified BSD, LICENSES/cvc5.txt)
; COMMAND-LINE:
; COMMAND-LINE: --strict-parsing
; EXPECT: sat
(set-logic QF_UFDT)
(declare-datatypes ((T 0)) (((C) (D))))
(declare-fun is-C (T) Bool)
(assert (is-C D))
(assert (not ((_ is C) D)))
(assert ((_ is D) D))
(set-info :status sat)
(check-sat)
