; From cvc5: regress0/proofs/project-issue317-inc-sat-conflictlit.smt2 (modified BSD, LICENSES/cvc5.txt)
; EXPECT: unsat
; EXPECT: unsat
; logic: QF_BV, the smallest the script fits, for ALL (prune logic)
(set-logic QF_BV)
(declare-const __ (_ BitVec 1))
(set-option :incremental true)
(set-info :status unsat)
(check-sat-assuming ((bvsgt ((_ sign_extend 42) (bvcomp ((_ zero_extend 10) __) ((_ zero_extend 10) __))) (_ bv0 43))))
(set-info :status unsat)
(check-sat-assuming ((bvsgt ((_ sign_extend 42) (bvcomp ((_ zero_extend 10) __) ((_ zero_extend 10) __))) (_ bv0 43))))
