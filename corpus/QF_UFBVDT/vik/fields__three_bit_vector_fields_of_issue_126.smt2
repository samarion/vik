; Hand-written for VIK (this repository's license): the script of issue 126. A field of one bit has two
; values, so three `of-BV` values are not pairwise distinct. The lowering made the field an `Int` and
; bounded a selector application only where the script wrote one; the fields the testers' expansion makes
; had no range, and the answer was sat (issue 126, 2026-11-17).
(set-logic ALL)
(set-option :produce-models true)
(declare-datatypes ((Val 0)) (((of-Int (to-Int Int)) (of-BV (to-BV (_ BitVec 1))))))
(declare-const x1 Val)
(assert ((_ is of-BV) x1))
(declare-const x2 Val)
(assert ((_ is of-BV) x2))
(declare-const x3 Val)
(assert ((_ is of-BV) x3))
(assert (distinct x1 x2 x3))
(set-info :status unsat)
(check-sat)
