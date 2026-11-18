; From cvc5: regress0/bv/holes/bv-ite-width-one.smt2 (modified BSD, LICENSES/cvc5.txt)
; EXPECT: unsat
; logic: QF_BV, the smallest the script fits, for ALL (prune logic)
(set-logic QF_BV)
(declare-const b (_ BitVec 1))
(assert (not
(= (bvcomp #b1 b) b)
))
(set-info :status unsat)
(check-sat)
