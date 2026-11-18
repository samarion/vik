; From cvc5: regress0/bv/holes/neg-add.smt2 (modified BSD, LICENSES/cvc5.txt)
; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)

(declare-const x (_ BitVec 5))
(declare-const y (_ BitVec 5))
(declare-const z (_ BitVec 5))
(assert (not (=
	(bvneg (bvadd x y z))
	(bvadd (bvneg x) (bvneg y) (bvneg z)))))
(set-info :status unsat)
(check-sat)
(exit)
