; From smtinterpol: bv/bvnot01.smt2 (LGPL-3.0, LICENSES/smtinterpol.txt)
; statuses: the `unknown` ones answered by cvc5 version 1.3.3 (by hand, 2026-11-17: z3 4.14 refuses the file)
(set-option :produce-proofs true)
(set-option :produce-models true)
(set-logic QF_BVLIA)

(declare-const a (_ BitVec 32))
(declare-const b (_ BitVec 32))

(assert (not (= (bvnot a) (bvsub ((_ int_to_bv 32) (- 1)) a))))
(set-info :status unsat)
(check-sat)
(get-proof)
