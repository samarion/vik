; From cvc5: regress0/parser/strict-parsing-mixed-arith-3b.smt2 (modified BSD, LICENSES/cvc5.txt)
; COMMAND-LINE: --strict-parsing
; EXPECT: sat
(set-logic QF_LRA)
; ok since 0 is treated as 0.0 in this logic
(assert (= 0 0.0))
(set-info :status sat)
(check-sat)
