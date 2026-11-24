; From cvc5: regress0/arrays/issue6276.smt2 (modified BSD, LICENSES/cvc5.txt)
; COMMAND-LINE: -i
; EXPECT: sat
; EXPECT: sat
(set-logic QF_ALIA)
(declare-fun v0 () Bool)
(declare-fun i1 () Int)
(declare-fun arr0 () (Array Int Bool))
(assert (select (store arr0 0 v0) i1))
(push)
(assert (= 1 i1))
(set-info :status sat)
(check-sat)
(set-info :status sat)
(check-sat)
