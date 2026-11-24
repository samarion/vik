; From cvc5: regress0/bv/holes/srem-eliminate-fewer-bitwise-ops.smt2 (modified BSD, LICENSES/cvc5.txt)
; Logos proof checking exceeds the 600-second timeout.
; DISABLE-TESTER: cpc-logos
; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)

(declare-const x (_ BitVec 5))
(declare-const y (_ BitVec 5))
(assert (and (bvsgt x #b00000) (bvsgt y #b00000) (not (=
	(bvsrem x y)
  (ite (bvuge x #b10000) (bvneg (bvurem x y)) (bvurem x y))))))
(set-info :status unsat)
(check-sat)
(exit)
