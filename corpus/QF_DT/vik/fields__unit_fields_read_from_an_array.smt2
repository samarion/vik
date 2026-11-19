; Hand-written for VIK (this repository's license): two reads of an array of `Val`, both `of-Unit`, apart:
; terms the array passes make get the bounds too (issue 125, 2026-11-17).
(set-logic ALL)
(declare-datatypes ((Unit 0) (Val 0)) (((unit)) ((of-Int (to-Int Int)) (of-Unit (to-Unit Unit)))))
(declare-const a (Array Int Val))
(assert ((_ is of-Unit) (select a 0)))
(assert ((_ is of-Unit) (select a 1)))
(assert (not (= (select a 0) (select a 1))))
(set-info :status unsat)
(check-sat)
