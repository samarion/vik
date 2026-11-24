; Hand-written for VIK (this repository's license): there are four arrays of one bit to the Booleans, so five
; records of one are not pairwise distinct. An array over finite sorts has finitely many values, but the
; solver counted `Bool` and the datatypes alone as finite, and the fields, which no term of the script
; names, were never compared (issue 153, 2026-11-17).
(set-logic ALL)
(declare-datatype P ((mk (arr (Array (_ BitVec 1) Bool)))))
(declare-const a1 P)
(declare-const a2 P)
(declare-const a3 P)
(declare-const a4 P)
(declare-const a5 P)
(push 1)
(assert (distinct a1 a2 a3 a4))
(set-info :status sat)
(check-sat)
(pop 1)
(assert (distinct a1 a2 a3 a4 a5))
(set-info :status unsat)
(check-sat)
