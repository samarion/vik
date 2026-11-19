; Hand-written for VIK (this repository's license): two `cons` lists of `Unit` apart, which their tails allow.
; Without `get-model`, as for three (issue 127) (issue 125, 2026-11-17).
(set-logic QF_DT)
(declare-datatypes ((Unit 0) (L 0)) (((unit)) ((nil) (cons (hd Unit) (tl L)))))
(declare-const x L)
(declare-const y L)
(assert ((_ is cons) x))
(assert ((_ is cons) y))
(assert (distinct x y))
(set-info :status sat)
(check-sat)
