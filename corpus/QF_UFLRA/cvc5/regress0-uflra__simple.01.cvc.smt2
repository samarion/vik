; From cvc5: regress0/uflra/simple.01.cvc.smt2 (modified BSD, LICENSES/cvc5.txt)
; EXPECT: sat
; logic: QF_UFLRA, the smallest the script fits, for ALL (prune logic)
(set-logic QF_UFLRA)
(set-option :incremental true)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun f (Real) Real)
(push 1)

(assert (not (= (f x) (f y))))

(set-info :status sat)
(check-sat)

(pop 1)

