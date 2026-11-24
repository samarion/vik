; Hand-written for VIK (this repository's license): an array differs from itself with a zero stored at an
; index and from itself with a one stored there, which leaves no value for its element of one bit at that
; index. The element is read at the witnesses of the two differences, reads that the solver makes itself and
; that had no range (issue 154, 2026-11-17). Here for an inner array of an array of arrays.
(set-logic QF_ABV)
(declare-const a (Array (_ BitVec 2) (Array (_ BitVec 2) (_ BitVec 1))))
(declare-const i (_ BitVec 2))
(declare-const j (_ BitVec 2))
(assert (not (= (select a i) (store (select a i) j #b0))))
(set-info :status sat)
(check-sat)
(assert (not (= (select a i) (store (select a i) j #b1))))
(set-info :status unsat)
(check-sat)
