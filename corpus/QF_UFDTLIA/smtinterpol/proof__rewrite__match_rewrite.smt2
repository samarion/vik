; From smtinterpol: proof/rewrite/match_rewrite.smt2 (LGPL-3.0, LICENSES/smtinterpol.txt)
; statuses: the `unknown` ones answered by Z3 version 4.14.0 (statusstamp, 2026-11-17; its `set-option` and `get-` commands left out, z3 refusing SMTInterpol's options)
(set-option :produce-proofs true)
(set-option :proof-check-mode true)
(set-logic QF_UFDTLIA)
(declare-datatypes ( (List 1) (Tree 1) ) (
 (par (X) ( (nil) (cons (car X) (cdr (List X)) )))
 (par (X) ( (leaf (data X)) (node (left (Tree X)) (right (Tree X))) ))
))

(declare-const t (Tree Int))

(assert (not (= (match (ite true t (leaf 1))
                          (((leaf x) (+ x x))
                          ((node x y) (+ 1 1))
                          ((leaf x) (+ 1 x 1))
			  (x (+ 2 (data x)))))
                (ite ((_ is leaf) t) (* 2 (data t)) 2))))

(set-info :status unsat)
(check-sat)
(get-proof)
