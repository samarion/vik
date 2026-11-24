; From smtinterpol: proof/rewrite/bool_distinct_rewrite.smt2 (LGPL-3.0, LICENSES/smtinterpol.txt)
; statuses: the `unknown` ones answered by Z3 version 4.14.0 (statusstamp, 2026-11-17; its `set-option` and `get-` commands left out, z3 refusing SMTInterpol's options)
(set-option :produce-proofs true)
(set-option :proof-check-mode true)
(set-option :model-check-mode true)
(set-option :print-terms-cse false)

(set-logic QF_UF)
(declare-fun p () Bool)
(declare-fun q () Bool)
(declare-fun r () Bool)

; check distinct with more than two parameters
(push 1)
(assert (distinct p q r))
(set-info :status unsat)
(check-sat)
(get-proof)
(pop 1)

; check binary distinct 
(push 1)
(assert (distinct p q))
(assert p)
(assert q)
(set-info :status unsat)
(check-sat)
(get-proof)
(pop 1)

; check binary distinct with negated arguments
(push 1)
(assert (distinct p (not q)))
(assert (distinct (not q) r))
(assert p)
(assert (not r))
(set-info :status unsat)
(check-sat)
(get-proof)
(pop 1)

; check non-binary with two negated argument
(push 1)
(assert (distinct (not p) (not q)))
(assert p)
(assert q)
(set-info :status unsat)
(check-sat)
(get-proof)
(pop 1)

; check true and false rewrites
(push 1)
(assert (distinct p true))
(assert (distinct p false))
(set-info :status unsat)
(check-sat)
(get-proof)
(pop 1)

(push 1)
(assert (distinct true p))
(assert (distinct false p))
(set-info :status unsat)
(check-sat)
(get-proof)
(pop 1)

; check distinct same
(push 1)
(assert (distinct p p))
(set-info :status unsat)
(check-sat)
(get-proof)
(pop 1)

; check distinct opposite
(push 1)
(assert (not (distinct p (not p))))
(set-info :status unsat)
(check-sat)
(get-proof)
(pop 1)
