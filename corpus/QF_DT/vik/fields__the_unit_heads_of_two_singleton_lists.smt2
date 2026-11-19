; Hand-written for VIK (this repository's license): two lists of `Unit`, both a `cons` onto `nil`, apart: a
; recursive datatype is infinite, and the heads its testers invent were unbounded (issue 125, 2026-11-17).
(set-logic QF_DT)
(declare-datatypes ((Unit 0) (L 0)) (((unit)) ((nil) (cons (hd Unit) (tl L)))))
(declare-const x L)
(declare-const y L)
(assert (= (tl x) nil))
(assert (= (tl y) nil))
(assert ((_ is cons) x))
(assert ((_ is cons) y))
(assert (distinct x y))
(set-info :status unsat)
(check-sat)
