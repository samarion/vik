; Hand-written for VIK (this repository's license): two `of-Pair` values apart, a pair of `Unit`s having one
; value: the expansion of a field of a finite datatype invents its fields in turn (issue 125, 2026-11-17).
(set-logic ALL)
(declare-datatypes ((Unit 0) (Pair 0) (Val 0)) (((unit)) ((mk (fst Unit) (snd Unit))) ((of-Int (to-Int Int)) (of-Pair (to-Pair Pair)))))
(declare-const x Val)
(declare-const y Val)
(assert ((_ is of-Pair) x))
(assert ((_ is of-Pair) y))
(assert (distinct x y))
(set-info :status unsat)
(check-sat)
