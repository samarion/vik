; From cvc5: regress0/bv/holes/not-xor.smt2 (modified BSD, LICENSES/cvc5.txt)
; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)

(declare-const x (_ BitVec 4))
(declare-const y (_ BitVec 4))
(declare-const z (_ BitVec 4))
(assert (not (=
  (bvnot (bvxor x y z))
  (bvxor (bvnot x) y z)
	)))
(set-info :status unsat)
(check-sat)
(exit)
