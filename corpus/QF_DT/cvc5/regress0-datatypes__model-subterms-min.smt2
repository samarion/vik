; From cvc5: regress0/datatypes/model-subterms-min.smt2 (modified BSD, LICENSES/cvc5.txt)
; logic: QF_DT, the smallest the script fits, for ALL (prune logic)
(set-logic QF_DT)
(set-info :status sat)
(declare-datatypes ((A 0) (B 0)) (
((a (sa B)))
((e1) (e2 (se2 A)))
))

(declare-const x1 A)
(declare-const x2 B)

(assert (distinct x1 (a x2)))

(declare-const x3 A)

(assert (distinct x2 (e2 x3)))

(check-sat)

