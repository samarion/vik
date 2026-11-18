; From cvc5: regress0/printer/print_options_auto.smt2 (modified BSD, LICENSES/cvc5.txt)
; COMMAND-LINE: -o options-auto
; SCRUBBER: sed -e 's/(options-auto.*//'
; EXPECT: sat
(set-logic QF_LRA)
(assert true)
(set-info :status sat)
(check-sat)
