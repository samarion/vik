; From smtinterpol: proof/auxaxioms/true_not_false.smt2 (LGPL-3.0, LICENSES/smtinterpol.txt)
; statuses: the `unknown` ones answered by Z3 version 4.15.1 (statusstamp, 2026-11-18; its `set-option` and `get-` commands left out, z3 refusing SMTInterpol's options)
(set-option :produce-proofs true)
(set-option :proof-check-mode true)


(set-logic QF_ALIA)
; using array theory is possibly the only way to trigger this axiom
(push 1)
(assert (= ((as const (Array Int Bool)) true) ((as const (Array Int Bool)) false)))
(set-info :status unsat)
(check-sat)
(set-option :print-terms-cse false)
(get-proof)
(pop 1)
