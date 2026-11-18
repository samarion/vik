; From cvc5: regress0/bv/bvmul-pow2-only.smt2 (modified BSD, LICENSES/cvc5.txt)
(set-logic QF_BV)
(set-info :status sat)
(declare-fun x () (_ BitVec 4))

(assert (= x #b1000))

(assert (= (bvmul (bvneg x) x) #b0000))
(assert (= (bvmul (bvneg #b0100) #b0100) #b0000))
(check-sat)
