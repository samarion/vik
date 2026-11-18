; From cvc5: regress0/bv/bitwise-and-simp.smt2 (modified BSD, LICENSES/cvc5.txt)
; EXPECT: unsat
; logic: QF_BV, the smallest the script fits, for ALL (prune logic)
(set-logic QF_BV)
(declare-fun x () (_ BitVec 4))
(assert (not (=
(bvand #b1011 x #b1110) (bvand #b1010 x))))
(set-info :status unsat)
(check-sat)
