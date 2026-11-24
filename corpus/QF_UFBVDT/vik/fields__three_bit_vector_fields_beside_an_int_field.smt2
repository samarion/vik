; Hand-written for VIK (this repository's license): three `of-BV` values pairwise apart, `(_ BitVec 1)` having
; two values. The lowering made the field an `Int` and bounded a selector application only where the script
; wrote one; the field the testers' expansion makes had no range (issue 126, 2026-11-17).
(set-logic ALL)
(declare-datatypes ((Val 0)) (((of-Int (to-Int Int)) (of-BV (to-BV (_ BitVec 1))))))
(declare-const x Val)
(declare-const y Val)
(declare-const z Val)
(assert ((_ is of-BV) x))
(assert ((_ is of-BV) y))
(assert ((_ is of-BV) z))
(assert (distinct x y z))
(set-info :status unsat)
(check-sat)
