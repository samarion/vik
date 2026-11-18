; From cvc5: regress0/arrays/bool-array.smt2 (modified BSD, LICENSES/cvc5.txt)
; EXPECT: unsat
(set-logic QF_AX)
(set-info :status unsat)

(declare-fun a () (Array Bool Bool))
(declare-fun b () (Array Bool Bool))

(assert (not (= (select a (= a b)) (select a (not (= a b))))))
(assert (= (select a true) (select a false)))

(set-info :status unsat)
(check-sat)
