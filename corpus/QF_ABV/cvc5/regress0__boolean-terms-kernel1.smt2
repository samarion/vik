; From cvc5: regress0/boolean-terms-kernel1.smt2 (modified BSD, LICENSES/cvc5.txt)
; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: sat
(set-logic QF_ABV)
(declare-fun b () (_ BitVec 32))
(declare-fun hk () (Array Bool (_ BitVec 32)))
(push 1)
(assert (not (= b (select hk true))))
(set-info :status sat)
(check-sat)
(pop 1)
(assert (not (= b (_ bv0 32))))
(assert (= b (select hk true)))
(set-info :status sat)
(check-sat)
