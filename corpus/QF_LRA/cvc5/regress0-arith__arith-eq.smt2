; From cvc5: regress0/arith/arith-eq.smt2 (modified BSD, LICENSES/cvc5.txt)
; COMMAND-LINE:
; EXPECT: unsat
(set-logic QF_LRA)

(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)

(assert (= z 0))
(assert (= (* 3 x) y))
(assert (= (+ 1 (* 5 x)) y))
(assert (= (+ 7 (* 4 x)) y))

(set-info :status unsat)
(check-sat)
