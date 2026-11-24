; Hand-written for VIK (this repository's license): a constructor named `store!9`, which the solver took for
; the store symbol of an array sort by its name, and threw (issue 143, 2026-11-17). VIK's own names start
; with `.` now, which no script declares (issue 194).
(set-logic ALL)
(declare-datatype T ((store!9 (fa Int) (fi Int) (fv Int))))
(declare-const t T)
(declare-const u T)
(declare-const m (Array Int Int))
(assert (= (select (store m 0 1) 0) 1))
(assert (= t (store!9 1 2 3)))
(assert (= u (store!9 1 2 4)))
(set-info :status sat)
(check-sat)
