; From cvc5: regress0/cores/issue4925.smt2 (modified BSD, LICENSES/cvc5.txt)
; EXPECT: sat
; EXPECT: unsat
; EXPECT: unsat
(set-logic QF_LRA)
(set-option :incremental true)
(declare-fun a () Real)
(declare-fun b () Real)
(declare-fun c () Real)
(assert (< c 0))
(assert (> (+ a b) 0))
(assert (or (< a 1) (> c 1)))
(set-info :status sat)
(check-sat)
(assert (= b (- 1)))
(set-info :status unsat)
(check-sat-assuming (true))
(set-info :status unsat)
(check-sat)
