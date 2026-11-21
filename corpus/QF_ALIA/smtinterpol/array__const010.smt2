; From smtinterpol: array/const010.smt2 (LGPL-3.0, LICENSES/smtinterpol.txt)
; statuses: the `unknown` ones answered by Z3 version 4.15.1 (statusstamp, 2026-11-18; its `set-option` and `get-` commands left out, z3 refusing SMTInterpol's options)
(set-option :produce-proofs true)
(set-option :proof-check-mode true)

(set-logic QF_ALIA)
(declare-sort U 0)
(declare-fun v1 () U)
(declare-fun v2 () U)
(define-fun constU ((v U)) (Array Int U) ((as const (Array Int U)) v))

(assert (= (constU v1) (constU v2)))
(set-info :status sat)
(check-sat)
(get-model)
(get-value ((@diff (constU v1) (constU v2))))
(exit)

