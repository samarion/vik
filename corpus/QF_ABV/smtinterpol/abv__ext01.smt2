; From smtinterpol: abv/ext01.smt2 (LGPL-3.0, LICENSES/smtinterpol.txt)
; statuses: the `unknown` ones answered by Z3 version 4.14.0 (statusstamp, 2026-11-17)
(set-logic QF_ABV)

(declare-const a (Array (_ BitVec 1) (_ BitVec 1)))
(declare-const b (Array (_ BitVec 1) (_ BitVec 1)))
(declare-const c (Array (_ BitVec 1) (_ BitVec 1)))
(declare-const d (Array (_ BitVec 1) (_ BitVec 1)))
(declare-const e (Array (_ BitVec 1) (_ BitVec 1)))

(assert (distinct a b c d e))
(set-info :status unsat)
(check-sat)
