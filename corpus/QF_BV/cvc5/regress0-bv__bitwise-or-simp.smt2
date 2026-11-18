; From cvc5: regress0/bv/bitwise-or-simp.smt2 (modified BSD, LICENSES/cvc5.txt)
; EXPECT: unsat
; logic: QF_BV, the smallest the script fits, for ALL (prune logic)
(set-logic QF_BV)
(declare-fun x () (_ BitVec 4))
(assert (not (=
(bvor #b0100 x #b0001) (bvor #b0101 x))))
(set-info :status unsat)
(check-sat)
