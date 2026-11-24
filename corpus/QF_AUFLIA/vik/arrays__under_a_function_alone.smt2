; Hand-written for VIK (this repository's license): arrays met only as the arguments of a function, in a
; script with no integer, no real and no store. Two arrays that agree at both Boolean indices are equal,
; so the function's applications are; and there are four arrays from Bool to Bool, so five applications
; cannot be distinct. Before the fix the pass that pairs such arrays ran only beside an arithmetic term
; or a store, and the pairs it made got their witnesses only when the same round emitted a clause: each
; unsat check answered sat (issue 133).
(set-logic QF_AUFLIA)
(declare-sort U 0)
(declare-fun p ((Array Bool Bool)) Bool)
(declare-fun f ((Array Bool Bool)) U)
(declare-const a1 (Array Bool Bool))
(declare-const a2 (Array Bool Bool))
(declare-const a3 (Array Bool Bool))
(declare-const a4 (Array Bool Bool))
(declare-const a5 (Array Bool Bool))
(push 1)
(assert (distinct (p a1) (p a2)))
(assert (= (select a1 true) (select a2 true)))
(set-info :status sat)
(check-sat)
(assert (= (select a1 false) (select a2 false)))
(set-info :status unsat)
(check-sat)
(pop 1)
(push 1)
(assert (distinct (f a1) (f a2) (f a3) (f a4)))
(set-info :status sat)
(check-sat)
(assert (distinct (f a1) (f a2) (f a3) (f a4) (f a5)))
(set-info :status unsat)
(check-sat)
(pop 1)
