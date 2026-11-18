; From cvc5: regress0/bv/dd_fuzz21.smt2 (modified BSD, LICENSES/cvc5.txt)
; EXPECT: unsat
; logic: QF_BV, the smallest the script fits, for ALL (prune logic)
(set-logic QF_BV)
(declare-const x (_ BitVec 1))
(set-info :status unsat)
(check-sat-assuming ((bvult (_ bv1 3) (bvmul ((_ sign_extend 2) x) ((_ repeat 3) (_ bv1 1))))))
