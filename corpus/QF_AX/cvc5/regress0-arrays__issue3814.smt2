; From cvc5: regress0/arrays/issue3814.smt2 (modified BSD, LICENSES/cvc5.txt)
; COMMAND-LINE: --produce-unsat-cores
; EXPECT: sat
(set-logic QF_AX)
(declare-fun a () (Array Bool Bool))
(declare-fun b () (Array Bool Bool))
(declare-fun c () Bool)
(declare-fun d () Bool)
(declare-fun e () Bool)
(assert (= a (store b c d)))
(assert (= e (select a (select b d))))
(set-info :status sat)
(check-sat)
