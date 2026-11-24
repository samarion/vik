; From smtinterpol: bv/bvmul01.smt2 (LGPL-3.0, LICENSES/smtinterpol.txt)
; statuses: the `unknown` ones answered by Z3 version 4.14.0 (statusstamp, 2026-11-17)
(set-option :produce-proofs true)
(set-option :produce-models true)
(set-logic QF_BV)

(declare-const a (_ BitVec 32))
(declare-const b (_ BitVec 32))

(assert (not (= (bvmul a b) (bvmul b a))))
(set-info :status unsat)
(check-sat)
(get-proof)
