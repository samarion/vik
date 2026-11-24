; Hand-written for VIK (this repository's license): the head of `u` is one more than itself. The selector
; application `(hd u)` occurred only inside the linear argument `(+ (hd u) 1)`, which the e-graph keeps as a
; leaf: it got no class and no variable of the simplex, the selector rule never equated it with the field,
; and the answer was sat (issue 136, 2026-11-17).
(set-logic QF_UFDTLIA)
(declare-datatypes ((Lst 0)) (((nil) (cons (hd Int) (tl Lst)))))
(declare-const u Lst)
(assert (= u (cons (+ (hd u) 1) nil)))
(set-info :status unsat)
(check-sat)
