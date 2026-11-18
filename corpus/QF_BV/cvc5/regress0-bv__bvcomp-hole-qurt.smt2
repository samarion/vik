; From cvc5: regress0/bv/holes/bvcomp-hole-qurt.smt2 (modified BSD, LICENSES/cvc5.txt)
; EXPECT: unsat
; logic: QF_BV, the smallest the script fits, for ALL (prune logic)
(set-logic QF_BV)
(declare-fun fp.f1 () (_ BitVec 64))
(assert (not
(= (bvcomp ((_ extract 63 63) fp.f1) #b0) (bvnot ((_ extract 63 63) fp.f1)))
))
(set-info :status unsat)
(check-sat)
