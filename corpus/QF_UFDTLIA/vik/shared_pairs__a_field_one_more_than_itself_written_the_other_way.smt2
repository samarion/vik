; Hand-written for VIK (this repository's license): issue 136's first script, the equality's sides swapped.
(set-logic QF_UFDTLIA)
(declare-datatypes ((Lst 0)) (((nil) (cons (hd Int) (tl Lst)))))
(declare-const u Lst)
(assert (= (cons (+ (hd u) 1) nil) u))
(set-info :status unsat)
(check-sat)
