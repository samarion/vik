; Hand-written for VIK (this repository's license): the second reproducer in issue 135.
(set-logic QF_AUFLIA)
(declare-sort U 0)
(declare-fun f ((Array Int Int)) U)
(declare-const a (Array Int Int))
(declare-const i Int)
(assert (not (= (f a) (f (store a i (select a i))))))
(set-info :status unsat)
(check-sat)
