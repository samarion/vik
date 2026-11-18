; From cvc5: regress0/arith/arith-strict-relaxed.smt2 (modified BSD, LICENSES/cvc5.txt)
; COMMAND-LINE:
; EXPECT: unsat
(set-logic QF_LRA)

(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)

; Both strict and non-strict inequalities.
(assert (< y 0))
(assert (>= y x))
(assert (>= y (- x)))

(set-info :status unsat)
(check-sat)
