; From cvc5: regress0/bv/holes/repeat-eliminate-1.smt2 (modified BSD, LICENSES/cvc5.txt)
; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)

(declare-const x (_ BitVec 10))
(assert (not (=
	((_ repeat 5) x)
	(concat x ((_ repeat 4) x))
	)))
(set-info :status unsat)
(check-sat)
(exit)
