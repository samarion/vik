; Hand-written for VIK (this repository's license): issue 136's first script, the equality under a
; disjunction that the other assertion decides.
(set-logic QF_UFDTLIA)
(declare-datatypes ((Lst 0)) (((nil) (cons (hd Int) (tl Lst)))))
(declare-const u Lst)
(declare-const p Bool)
(assert (or p (= u (cons (+ (hd u) 1) nil))))
(assert (not p))
(set-info :status unsat)
(check-sat)
