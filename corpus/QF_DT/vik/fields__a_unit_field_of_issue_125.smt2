; Hand-written for VIK (this repository's license): the minimal script of issue 125. `V` is infinite through
; `b`, and its `a` values are one, `U` having one value; the fields of `x` and `y` are terms the testers'
; expansion makes, which had no value of their sort, so the two stayed apart (issue 125, 2026-11-17).
(set-logic ALL)
(declare-datatypes ((U 0) (V 0)) (((u)) ((a (f U)) (b (g Int)))))
(declare-const x V)
(declare-const y V)
(assert ((_ is a) x))
(assert ((_ is a) y))
(assert (distinct x y))
(set-info :status unsat)
(check-sat)
