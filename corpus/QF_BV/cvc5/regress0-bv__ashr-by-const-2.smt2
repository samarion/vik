; From cvc5: regress0/bv/holes/ashr-by-const-2.smt2 (modified BSD, LICENSES/cvc5.txt)
; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)

(declare-const x (_ BitVec 5))
(assert (not (=
  (bvashr x #b00110)
  ((_ repeat 5) ((_ extract 4 4) x))
	)))
(set-info :status unsat)
(check-sat)
(exit)
