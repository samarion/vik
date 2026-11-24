; Hand-written for VIK (this repository's license): three `cons` lists of `Unit` pairwise apart, which their
; tails allow. Without `get-model`: the model gives the three tails `nil`, the same value (issue 127) (issue
; 125, 2026-11-17).
(set-logic QF_DT)
(declare-datatypes ((Unit 0) (L 0)) (((unit)) ((nil) (cons (hd Unit) (tl L)))))
(declare-const x L)
(declare-const y L)
(declare-const z L)
(assert ((_ is cons) x))
(assert ((_ is cons) y))
(assert ((_ is cons) z))
(assert (distinct x y z))
(set-info :status sat)
(check-sat)
