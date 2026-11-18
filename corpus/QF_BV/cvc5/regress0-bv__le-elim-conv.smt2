; From cvc5: regress0/bv/le-elim-conv.smt2 (modified BSD, LICENSES/cvc5.txt)
(set-logic ALL)
(set-info :status sat)
(declare-fun a () (_ BitVec 32))

(assert (>= (ubv_to_int a) 50000))
(assert (<= (ubv_to_int a) 60000))

(check-sat)
