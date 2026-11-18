; From cvc5: regress0/parser/keyword-one-char.smt2 (modified BSD, LICENSES/cvc5.txt)
; EXPECT: sat
(set-logic ALL)
(set-info :a)
(set-info :ab)
(declare-const a Bool)
(assert (! a :named b))
(set-info :status sat)
(check-sat)
