; Hand-written for VIK (this repository's license): the third reproducer in issue 135.
(set-logic ALL)
(declare-datatype D ((C (arr (Array Int Int)))))
(declare-const a (Array Int Int))
(declare-const v Int)
(assert (= v (select a 1)))
(assert (not (= (C a) (C (store a 1 v)))))
(set-info :status unsat)
(check-sat)
