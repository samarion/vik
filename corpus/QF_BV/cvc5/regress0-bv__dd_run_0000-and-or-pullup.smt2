; From cvc5: regress0/bv/dd_run_0000-and-or-pullup.smt2 (modified BSD, LICENSES/cvc5.txt)
; EXPECT: unsat
; logic: QF_BV, the smallest the script fits, for ALL (prune logic)
(set-logic QF_BV)
(declare-const __ (_ BitVec 2))
(assert (= (_ bv1 1) ((_ extract 0 0) (bvand (_ bv1 32) (bvor (_ bv0 32) (bvand (_ bv131070 32) ((_ sign_extend 24) ((_ zero_extend 1) ((_ zero_extend 5) __)))))))))
(set-info :status unsat)
(check-sat)
