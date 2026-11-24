; Hand-written for VIK (this repository's license): an array whose elements have one value has one value,
; whatever its index, so two records of one are equal. The solver counted `Bool` and the datatypes alone
; as finite, and the two fields, which no term of the script names, were never compared (issue 153,
; 2026-11-17).
(set-logic ALL)
(declare-datatype Un ((unit)))
(declare-datatype W ((w (f (Array Int Un)))))
(declare-const x W)
(declare-const y W)
(assert (distinct x y))
(set-info :status unsat)
(check-sat)
