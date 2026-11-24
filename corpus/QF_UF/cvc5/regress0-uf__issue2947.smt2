; From cvc5: regress0/uf/issue2947.smt2 (modified BSD, LICENSES/cvc5.txt)
(set-logic QF_UF)
(set-info :status unsat)
(declare-fun f (Bool) Bool)
(assert
  (not (f true))
)
(assert
  (f (ite (f true) true (f false)))
)
(check-sat)
(exit)
