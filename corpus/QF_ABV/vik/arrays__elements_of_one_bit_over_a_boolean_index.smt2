; Hand-written for VIK (this repository's license): there are four arrays of the Booleans to one bit, so five
; of them are not pairwise distinct. They are told apart by the reads at witness indices, which the solver
; makes itself: those had no range, and were integers of any size (issue 154, 2026-11-17).
(set-logic ALL)
(declare-const a (Array Bool (_ BitVec 1)))
(declare-const b (Array Bool (_ BitVec 1)))
(declare-const c (Array Bool (_ BitVec 1)))
(declare-const d (Array Bool (_ BitVec 1)))
(declare-const e (Array Bool (_ BitVec 1)))
(push 1)
(assert (distinct a b c d))
(set-info :status sat)
(check-sat)
(pop 1)
(assert (distinct a b c d e))
(set-info :status unsat)
(check-sat)
