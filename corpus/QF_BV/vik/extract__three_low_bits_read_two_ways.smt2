; Hand-written for VIK (this repository's license): the three low bits of a bit-vector, as the concat of two
; extracts and as one extract. The extracts lower to quotients of `x` by 2, 4 and 8, bounded by the width,
; and branch and bound walked them: 3 s at width 16 and no answer at width 32 (issue 159, 2026-11-18,
; reduced from cvc5's `regress0/bv/core/concat-merge-0`). The integer equations leave the difference of
; the two readings a multiple of 8, which its bounds exclude at any width.
(set-logic QF_BV)
(declare-fun x () (_ BitVec 32))
(declare-fun y () (_ BitVec 64))
(push 1)
(assert (not (= (concat ((_ extract 2 1) x) ((_ extract 0 0) x)) ((_ extract 2 0) x))))
(set-info :status unsat)
(check-sat)
(pop 1)
(assert (not (= (concat ((_ extract 2 1) y) ((_ extract 0 0) y)) ((_ extract 2 0) y))))
(set-info :status unsat)
(check-sat)
