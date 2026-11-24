; Hand-written for VIK (this repository's license): `u` differs from `y` and from `z`, whose fields of two
; bits are 3 and 0. The field of `u` is a term the solver makes, which had no range: the model gave it a
; number past every value known and printed it modulo 4, as the `#b00` of `z`, against the `distinct`
; (issue 126, 2026-11-17).
(set-logic ALL)
(set-option :produce-models true)
(declare-datatype P ((mk (f (_ BitVec 2)))))
(declare-const y P)
(declare-const z P)
(declare-const u P)
(assert (= (f y) #b11))
(assert (= (f z) #b00))
(assert (distinct y z u))
(set-info :status sat)
(check-sat)
(get-model)
