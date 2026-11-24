; From cvc5: regress0/arrays/proj-issue391-minisat-elim.smt2 (modified BSD, LICENSES/cvc5.txt)
; EXPECT: sat
(set-logic QF_AX)
(declare-const x (Array Bool Bool))
(declare-const _x (Array Bool (Array Bool Bool)))
(declare-const x4 Bool)
(assert (and (select (select (store _x x4 x) true) false)))
(set-info :status sat)
(check-sat)
