; From cvc5: regress1/push-pop/bug216.smt2 (modified BSD, LICENSES/cvc5.txt)
; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: unsat

(set-logic QF_UF)
(declare-fun x () Bool)
(declare-fun y () Bool)
(assert (=> x y))
(set-info :status sat)
(check-sat) ; returns sat
(assert (=> y x))
(assert (and x (not y)))
(set-info :status unsat)
(check-sat) ; returns sat --> ERROR
