; Hand-written for VIK (this repository's license): arrays met only as the fields of a constructor, in a
; script with no integer, no real and no store. Two arrays that agree at both Boolean indices are equal,
; so the constructor's applications are; and there are four arrays from Bool to Bool, so five
; applications cannot be distinct. Before the fix the pass that pairs such arrays ran only beside an
; arithmetic term or a store, and each unsat check answered sat (issue 133).
(set-logic ALL)
(declare-datatype P ((mk (arr (Array Bool Bool)))))
(declare-const a1 (Array Bool Bool))
(declare-const a2 (Array Bool Bool))
(declare-const a3 (Array Bool Bool))
(declare-const a4 (Array Bool Bool))
(declare-const a5 (Array Bool Bool))
(push 1)
(assert (distinct (mk a1) (mk a2)))
(assert (= (select a1 true) (select a2 true)))
(set-info :status sat)
(check-sat)
(assert (= (select a1 false) (select a2 false)))
(set-info :status unsat)
(check-sat)
(pop 1)
(push 1)
(assert (distinct (mk a1) (mk a2) (mk a3) (mk a4)))
(set-info :status sat)
(check-sat)
(assert (distinct (mk a1) (mk a2) (mk a3) (mk a4) (mk a5)))
(set-info :status unsat)
(check-sat)
(pop 1)
