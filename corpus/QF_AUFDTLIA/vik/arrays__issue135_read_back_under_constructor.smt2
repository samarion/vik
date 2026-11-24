; Hand-written for VIK (this repository's license): the first reproducer in issue 135.
(set-logic ALL)
(declare-datatype D ((C (arr (Array Int Int)))))
(declare-const a (Array Int Int))
(assert (not (= (C a) (C (store a 0 (select a 0))))))
(set-info :status unsat)
(check-sat)
