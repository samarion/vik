; From cvc5: regress0/parser/strict-numeral.smt2 (modified BSD, LICENSES/cvc5.txt)
; COMMAND-LINE: --strict-parsing
; EXPECT: sat
(set-logic QF_LIRA)
(declare-fun x () Int)
(declare-fun -2 () Int)
(assert (= x 3))
(assert (= x -2))
(set-info :status sat)
(check-sat)
