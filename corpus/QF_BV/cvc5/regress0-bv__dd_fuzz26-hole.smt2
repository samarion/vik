; From cvc5: regress0/bv/dd_fuzz26-hole.smt2 (modified BSD, LICENSES/cvc5.txt)
; EXPECT: unsat
; logic: QF_BV, the smallest the script fits, for ALL (prune logic)
(set-logic QF_BV)
(declare-const v (_ BitVec 1))
(set-info :status unsat)
(check-sat-assuming ((not (bvuge (bvnor (bvor (_ bv2 4) (_ bv1 4)) (bvlshr ((_ zero_extend 3) v) (_ bv0 4))) (_ bv1 4)))))
