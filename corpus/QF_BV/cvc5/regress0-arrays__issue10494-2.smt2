; From cvc5: regress0/arrays/issue10494-2.smt2 (modified BSD, LICENSES/cvc5.txt)
; EXPECT: sat
(set-logic ALL)
(declare-const a (Array Int (_ BitVec 1)))
(assert (= a (store a 0 (bvadd #b1 (select a 1)))))
(set-info :status sat)
(check-sat)
