; From cvc5: regress0/bv/holes/comp-eliminate.smt2 (modified BSD, LICENSES/cvc5.txt)
; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)

(declare-const x (_ BitVec 4))
(declare-const y (_ BitVec 4))
;(assert (= (bvcomp x y) (bvnot (bvcomp (bvnot x) (bvnot y)))))
;(assert (= (ite (= x y) #b1 #b0) (bvnot (ite (= (bvnot x) (bvnot y)) #b1 #b0))))
(assert (not (= (bvcomp x y) (ite (= x y) #b1 #b0))))
(set-info :status unsat)
(check-sat)
(exit)
