; From cvc5: regress0/smtlib/reset-set-logic.smt2 (modified BSD, LICENSES/cvc5.txt)
; EXPECT: sat
; EXPECT: sat
(set-logic QF_LRA)
(declare-const x Real)
(assert (= x (- 2.5)))
(set-info :status sat)
(check-sat)

(reset)

(set-logic QF_LIA)
(declare-const x Int)
(assert (= x 2))
(set-info :status sat)
(check-sat)
