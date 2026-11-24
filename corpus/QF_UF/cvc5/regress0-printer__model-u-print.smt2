; From cvc5: regress0/printer/model-u-print.smt2 (modified BSD, LICENSES/cvc5.txt)
; COMMAND-LINE: --produce-models --model-u-print=dt
; EXPECT: sat
; EXPECT: ((define-fun a () U @U!0) (define-fun b () U @U!1) (define-fun c () U @U!2))
(set-logic QF_UF)
(declare-sort U 0)
(declare-const a U)
(declare-const b U)
(declare-const c U)
(assert (distinct a b c))
(set-info :status sat)
(check-sat)
(get-model)
