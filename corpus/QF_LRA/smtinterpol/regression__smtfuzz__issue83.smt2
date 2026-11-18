; From smtinterpol: regression/smtfuzz/issue83.smt2 (LGPL-3.0, LICENSES/smtinterpol.txt)
; statuses: the `unknown` ones answered by Z3 version 4.14.0 (statusstamp, 2026-11-17)
(set-info :expect-errors 1)
(set-logic QF_LRA)
(declare-const v0 Bool)
(assert (or v0))
(set-info :status sat)
(check-sat)

