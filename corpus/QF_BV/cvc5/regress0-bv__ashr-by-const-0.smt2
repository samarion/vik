; From cvc5: regress0/bv/holes/ashr-by-const-0.smt2 (modified BSD, LICENSES/cvc5.txt)
; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)

(declare-const x (_ BitVec 5))
(assert (not (=
  (bvashr x #b00000)
  x
	)))
(set-info :status unsat)
(check-sat)
(exit)
