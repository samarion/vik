; From cvc5: regress0/bv/dd_run_0000-and-or-pullup-2.smt2 (modified BSD, LICENSES/cvc5.txt)
; EXPECT: unsat
; logic: QF_BV, the smallest the script fits, for ALL (prune logic)
(set-logic QF_BV)
(declare-fun I () (_ BitVec 8))
(assert (= (_ bv1 1) ((_ extract 0 0) (ite (= (_ bv0 32) ((_ zero_extend 24) ((_ extract 7 0) (bvor (_ bv1 32) (bvand (_ bv33553921 32) ((_ sign_extend 24) I)))))) (_ bv1 32) (_ bv0 32)))))
(set-info :status unsat)
(check-sat)
