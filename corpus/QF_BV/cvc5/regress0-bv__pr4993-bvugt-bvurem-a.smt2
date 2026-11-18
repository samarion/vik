; From cvc5: regress0/bv/pr4993-bvugt-bvurem-a.smt2 (modified BSD, LICENSES/cvc5.txt)
; COMMAND-LINE:
(set-logic QF_BV)
(set-info :status unsat)
(declare-const x (_ BitVec 4))
(declare-const y (_ BitVec 4))
(assert (not (= (bvugt (bvurem y x) x) (ite (= x #x0) (bvugt y #x0) false))))
(check-sat)
