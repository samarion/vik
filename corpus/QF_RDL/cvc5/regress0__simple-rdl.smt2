; From cvc5: regress0/simple-rdl.smt2 (modified BSD, LICENSES/cvc5.txt)
(set-logic QF_RDL)
(set-info :status unsat)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (not (=> (< (- x y) 0) (< x y))))
(check-sat)

