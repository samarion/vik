; From cvc5: regress0/bv/holes/commutative-xor.smt2 (modified BSD, LICENSES/cvc5.txt)
; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)

(declare-const x (_ BitVec 3))
(declare-const y (_ BitVec 3))
(assert (not (= (bvxor x y) (bvxor y x))))
(set-info :status unsat)
(check-sat)
(exit)
