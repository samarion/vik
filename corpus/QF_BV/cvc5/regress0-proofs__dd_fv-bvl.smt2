; From cvc5: regress0/proofs/dd_fv-bvl.smt2 (modified BSD, LICENSES/cvc5.txt)
; EXPECT: unsat
; logic: QF_BV, the smallest the script fits, for ALL (prune logic)
(set-logic QF_BV)
(define-fun b ((bv (_ BitVec 4))) (_ BitVec 4) bv)
(define-fun i ((index (_ BitVec 4)) (bv (_ BitVec 4))) (_ BitVec 4) (b bv))
(assert (= (_ bv0 8) (bvxor (_ bv1 8) ((_ zero_extend 4) (i (_ bv0 4) (_ bv0 4))))))
(set-info :status unsat)
(check-sat)
