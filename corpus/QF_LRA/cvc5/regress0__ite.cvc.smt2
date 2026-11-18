; From cvc5: regress0/ite.cvc.smt2 (modified BSD, LICENSES/cvc5.txt)
; EXPECT: unsat
; logic: QF_LRA, the smallest the script fits, for ALL (prune logic)
(set-logic QF_LRA)
(set-option :incremental true)
(declare-fun x () Real)
(declare-fun y () Real)
(push 1)

(assert (not (= x (ite true x y))))

(set-info :status unsat)
(check-sat)

(pop 1)

