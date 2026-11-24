; From cvc5: regress0/arrays/issue4927-unsat-cores.smt2 (modified BSD, LICENSES/cvc5.txt)
; COMMAND-LINE: --produce-models
; EXPECT: unsat
(set-logic QF_AX)
(declare-const a (Array Bool Bool))
(declare-const b (Array Bool Bool))
(declare-const c Bool)
(declare-const d Bool)
(declare-const e Bool)
(assert (= a (store b c d)))
(assert (distinct e d (ite e c d)))
(assert (= e c (select b d)))
(set-info :status unsat)
(check-sat)
