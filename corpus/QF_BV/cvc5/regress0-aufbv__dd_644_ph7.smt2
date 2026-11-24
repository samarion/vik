; From cvc5: regress0/aufbv/dd_644_ph7.smt2 (modified BSD, LICENSES/cvc5.txt)
; EXPECT: unsat
; logic: QF_BV, the smallest the script fits, for ALL (prune logic)
(set-logic QF_BV)
(declare-const x (_ BitVec 1))
(assert (= (_ bv1 1) ((_ extract 0 0) (bvlshr (concat (bvor (_ bv1 10) ((_ zero_extend 9) x) (ite false (_ bv0 10) (_ bv0 10))) (_ bv0 1)) (_ bv0 11)))))
(set-info :status unsat)
(check-sat)
