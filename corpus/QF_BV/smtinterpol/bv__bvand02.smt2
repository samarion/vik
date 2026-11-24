; From smtinterpol: bv/bvand02.smt2 (LGPL-3.0, LICENSES/smtinterpol.txt)
; statuses: the `unknown` ones answered by Z3 version 4.14.0 (statusstamp, 2026-11-17; its `set-option` and `get-` commands left out, z3 refusing SMTInterpol's options)
(set-option :produce-proofs true)
(set-option :produce-models true)
(set-logic QF_BV)

(declare-const a (_ BitVec 32))

(assert (= (bvand a #x0f0f99cc) #x06081004))
(assert (= (bvand #xf0f06633 a) #x50700230))
(set-info :status sat)
(check-sat)
(get-model)

(assert (not (= a #x56781234)))
(set-info :status unsat)
(check-sat)
(get-proof)
