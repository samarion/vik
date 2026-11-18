; From cvc5: regress1/sym/qf-function.smt2 (modified BSD, LICENSES/cvc5.txt)
(set-logic QF_UFLIA)
(set-info :status sat)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun P (Int) Int)
(declare-fun Q (Int) Int)

(assert (or (= (f a) 0) (= (g a) 0)))

(check-sat)
