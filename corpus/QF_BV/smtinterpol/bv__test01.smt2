; From smtinterpol: bv/test01.smt2 (LGPL-3.0, LICENSES/smtinterpol.txt)
;(set-option :produce-proofs true)
;(set-option :proof-check-mode true)
; logic: QF_BV, the smallest the script fits, for QF_UFBV (prune logic)

(set-info :status unsat)

(set-logic QF_BV)

(define-fun f ((a (_ BitVec 8))) (_ BitVec 8) (bvadd a a))
(define-fun g () (_ BitVec 8) (_ bv27 8))
(declare-const b (_ BitVec 8))

(assert (or (not (= g (_ bv27 8))) (not (= (f (f b)) (_ bv108 8)))))
(assert (= b (_ bv27 8)))
(check-sat)

(exit)
