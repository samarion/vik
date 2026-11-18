; From cvc5: regress0/bv/holes/and-flatten.smt2 (modified BSD, LICENSES/cvc5.txt)
; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)

(declare-const x1 (_ BitVec 3))
(declare-const x2 (_ BitVec 3))
(declare-const x3 (_ BitVec 3))
(declare-const x4 (_ BitVec 3))
(assert (not (= (bvand (bvand x1 x2) (bvand x3 x4)) (bvand x1 x2 x3 x4))))
(set-info :status unsat)
(check-sat)
(exit)
