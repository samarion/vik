; From cvc5: regress0/proofs/issue9200-lfsc-inst-sorts.smt2 (modified BSD, LICENSES/cvc5.txt)
; logic: QF_UFLIA, the smallest the script fits, for UFLIA (prune logic)
(set-logic QF_UFLIA)
(set-info :status unsat)
(declare-sort F 2)
(define-fun g ((C.usr.2.A@0 (F Int Int))) Bool false)
(assert false)
(check-sat)

