; From cvc5: regress0/printer/print_subs.smt2 (modified BSD, LICENSES/cvc5.txt)
; COMMAND-LINE: -o subs
; EXPECT: (substitution (= a 3))
; EXPECT: sat
; logic: QF_LIA, the smallest the script fits, for ALL (prune logic)
(set-logic QF_LIA)
(declare-fun a () Int)
(declare-fun b () Int)
(assert (= (* 2 a) 6))
(assert (> b a))
(set-info :status sat)
(check-sat)
