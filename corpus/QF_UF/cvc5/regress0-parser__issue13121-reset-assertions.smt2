; From cvc5: regress0/parser/issue13121-reset-assertions.smt2 (modified BSD, LICENSES/cvc5.txt)
; COMMAND-LINE: --incremental
; EXPECT: sat
(set-logic QF_UF)
(declare-const q Bool)
(reset)
(set-logic QF_UF)
(declare-const p Bool)
(reset-assertions)
; p is no longer declared after the reset-assertions
(declare-const p Bool)
(assert p)
(set-info :status sat)
(check-sat)
