; From cvc5: regress0/bv/dd.try_small_difret.smt2 (modified BSD, LICENSES/cvc5.txt)
; EXPECT: unsat
; logic: QF_BV, the smallest the script fits, for ALL (prune logic)
(set-logic QF_BV)
(declare-const x Bool)
(assert (= (_ bv1 1) (bvand (_ bv1 1) (bvnot ((_ extract 0 0) (ite x (_ bv1 1) (_ bv0 1)))) ((_ extract 0 0) (ite x (_ bv1 1) (_ bv0 1))))))
(set-info :status unsat)
(check-sat)
