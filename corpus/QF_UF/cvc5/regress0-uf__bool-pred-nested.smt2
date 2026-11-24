; From cvc5: regress0/uf/bool-pred-nested.smt2 (modified BSD, LICENSES/cvc5.txt)
(set-logic QF_UF)
(set-info :status sat)
(declare-fun P (Bool Bool) Bool)

(assert (P (P true (P false false)) (P false true)))

(check-sat)
