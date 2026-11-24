; From smtinterpol: array/trivdiseq001.smt2 (LGPL-3.0, LICENSES/smtinterpol.txt)
; statuses: the `unknown` ones answered by Z3 version 4.14.0 (statusstamp, 2026-11-17; its `set-option` and `get-` commands left out, z3 refusing SMTInterpol's options)
(set-option :produce-proofs true)
(set-option :proof-check-mode true)

(set-logic QF_ALIA)
(declare-fun a () (Array Int Int))
(declare-fun b () (Array Int Int))
(declare-fun v0 () Int)
(declare-fun v2 () Int)
; The read-over-weakeq lemma needs the trivial index disequalities 0 != 1 and
; 2 != 1.  Both express the same affine fact up to a shift and to the sign, so
; the clause contains only one literal for them and the proof for the other one
; must multiply it by -1.
(assert (= b (store (store a 2 v2) 0 v0)))
(assert (not (= (select b 1) (select a 1))))
(set-info :status unsat)
(check-sat)
(get-proof)
(exit)
