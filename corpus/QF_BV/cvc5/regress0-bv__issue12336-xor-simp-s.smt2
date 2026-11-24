; From cvc5: regress0/bv/issue12336-xor-simp-s.smt2 (modified BSD, LICENSES/cvc5.txt)
; EXPECT: unsat
(set-logic QF_BV)
(declare-const r (_ BitVec 4))
(assert (= #b0001 (bvxor r (bvnot r))))
(set-info :status unsat)
(check-sat)
