; From cvc5: regress0/parser/real-numerals.smt2 (modified BSD, LICENSES/cvc5.txt)
; logic: QF_LRA, the smallest the script fits, for QF_NRA (prune logic)
(set-logic QF_LRA)
(set-info :status sat)
; note according to SMT-LIB, a NUMERAL specifies a Real when the logic contains reals but not ints
(define-fun x () Real 0)
(assert (<= (- 1) x 3))
(check-sat)
