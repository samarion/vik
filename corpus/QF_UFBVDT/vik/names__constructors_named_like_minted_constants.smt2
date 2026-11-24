; Hand-written for VIK (this repository's license): the lowering names the quotient and the remainder of a
; `bvudiv` `q!1` and `r!2`, and a datatype declared after took the two names for its constructors: the
; constants became constructors, two distinct values, and the answer was unsat (issue 143, 2026-11-17).
; VIK's own names start with `.` now, which no script declares (issue 194).
(set-logic ALL)
(declare-const a (_ BitVec 4))
(assert (= a #x4))
(assert (= (bvudiv a #x3) #x1))
(declare-datatype P ((q!1) (r!2)))
(set-info :status sat)
(check-sat)
