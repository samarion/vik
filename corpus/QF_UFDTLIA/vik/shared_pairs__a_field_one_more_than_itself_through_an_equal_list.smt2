; Hand-written for VIK (this repository's license): issue 136's first script, the selector applied to a list
; equal to `u`.
(set-logic QF_UFDTLIA)
(declare-datatypes ((Lst 0)) (((nil) (cons (hd Int) (tl Lst)))))
(declare-const u Lst)
(declare-const v Lst)
(assert (= u v))
(assert (= u (cons (+ (hd v) 1) nil)))
(set-info :status unsat)
(check-sat)
