; From smtinterpol: proof/rewrite/bool_eq_rewrite.smt2 (LGPL-3.0, LICENSES/smtinterpol.txt)
; statuses: the `unknown` ones answered by Z3 version 4.14.0 (statusstamp, 2026-11-17; its `set-option` and `get-` commands left out, z3 refusing SMTInterpol's options)
(set-option :produce-proofs true)
(set-option :proof-check-mode true)
(set-option :model-check-mode true)
(set-option :print-terms-cse false)

(set-logic QF_UF)
(declare-fun p () Bool)
(declare-fun q () Bool)
(declare-fun r () Bool)

; check non-binary xor rewrite
(push 1)
(assert (= p (not q) r))
(assert (xor p r))
(set-info :status unsat)
(check-sat)
(get-proof)
(pop 1)

; check non-binary with two negated arguments
(push 1)
(assert (= p (not q) (not r)))
(assert (xor p (not r)))
(set-info :status unsat)
(check-sat)
(get-proof)
(pop 1)

; check non-binary with no negated argument
(push 1)
(assert (= p q r))
(assert (xor p r))
(set-info :status unsat)
(check-sat)
(get-proof)
(pop 1)

; check true rewrite
(push 1)
(assert (= p (not q) true r))
(assert (not p))
(set-info :status unsat)
(check-sat)
(get-proof)
(pop 1)

; check false rewrite
(push 1)
(assert (= p (not q) false r))
(assert p)
(set-info :status unsat)
(check-sat)
(get-proof)
(pop 1)
