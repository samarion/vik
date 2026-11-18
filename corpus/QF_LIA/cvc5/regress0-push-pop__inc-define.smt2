; From cvc5: regress0/push-pop/inc-define.smt2 (modified BSD, LICENSES/cvc5.txt)
; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: sat
(set-logic QF_LIA)
(declare-fun x () Int)
(set-info :status sat)
(check-sat)
(define-const t Bool (not (= x 0)))
(assert t)
(set-info :status sat)
(check-sat)
