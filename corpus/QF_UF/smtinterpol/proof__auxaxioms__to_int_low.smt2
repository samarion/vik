; From smtinterpol: proof/auxaxioms/to_int_low.smt2 (LGPL-3.0, LICENSES/smtinterpol.txt)
; statuses: the `unknown` ones answered by Z3 version 4.14.0 (statusstamp, 2026-11-17; its `set-option` and `get-` commands left out, z3 refusing SMTInterpol's options)
(set-option :produce-proofs true)
(set-option :proof-check-mode true)
(set-option :model-check-mode true)
(set-option :print-terms-cse false)

(set-logic QF_UFLIRA)
(declare-fun x () Real)
(declare-fun y () Real)

(push 1)
(assert (< x (to_int x)))
(set-info :status unsat)
(check-sat)
(get-proof)
(pop 1)

(push 1)
(assert (< (- y (to_int x)) (to_int (- y (to_int x)))))
(set-info :status unsat)
(check-sat)
(get-proof)
(pop 1)


