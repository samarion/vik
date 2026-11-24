; From smtinterpol: model/array001.smt2 (LGPL-3.0, LICENSES/smtinterpol.txt)
; statuses: the `unknown` ones answered by Z3 version 4.14.0 (statusstamp, 2026-11-17; its `set-option` and `get-` commands left out, z3 refusing SMTInterpol's options)
(set-option :model-check-mode true)
(set-logic QF_ALIA)

(declare-const i Int)
(declare-const a (Array Int Int))

(assert (distinct (store a i 0) a))
(set-info :status sat)
(check-sat)
(get-model)
