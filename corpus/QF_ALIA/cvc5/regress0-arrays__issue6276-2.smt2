; From cvc5: regress0/arrays/issue6276-2.smt2 (modified BSD, LICENSES/cvc5.txt)
; COMMAND-LINE: -i
; EXPECT: sat
(set-logic QF_ALIA)
(set-info :status sat)
(declare-fun i2 () Int)
(declare-fun arr0 () (Array Int Bool))
(declare-fun i10 () Int)
(assert (select (store (store arr0 1 true) i10 false) i2))
(push)
(assert (= i10 0))
(set-info :status sat)
(check-sat)
