; From cvc5: regress0/printer/learned-lit-output.smt2 (modified BSD, LICENSES/cvc5.txt)
; COMMAND-LINE: -o learned-lits
; SCRUBBER: sed -e 's/(learned-lit.*/learned-lit/'
; EXPECT: learned-lit
; EXPECT: learned-lit
; EXPECT: learned-lit
; EXPECT: sat
; logic: QF_LIA, the smallest the script fits, for ALL (prune logic)
(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (> x 10))
(assert (or (< x 5) (> y 0)))
(set-info :status sat)
(check-sat)
