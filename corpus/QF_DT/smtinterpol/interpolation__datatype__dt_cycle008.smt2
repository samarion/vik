; From smtinterpol: interpolation/datatype/dt_cycle008.smt2 (LGPL-3.0, LICENSES/smtinterpol.txt)
; logic: QF_DT, the smallest the script fits, for QF_UFDT (prune logic)
; statuses: the `unknown` ones answered by Z3 version 4.14.0 (statusstamp, 2026-11-17; its `set-option` and `get-` commands left out, z3 refusing SMTInterpol's options)
(set-option :produce-interpolants true)
(set-option :interpolant-check-mode true)
(set-logic QF_DT)


(declare-datatypes ( (List 0) (Nat 0) ) (
 ( (nil) (cons (car Nat) (cdr List) ))
 ( (zero) (succ (pred Nat)) )
))

(declare-const u List)
(declare-const v List)

;; simple cycle

(assert (! (= u (cons zero (cons zero v))) :named A))
(assert (! (= v (cons (succ zero) u)) :named B))


(set-info :status unsat)
(check-sat)
(get-interpolants A B)
(get-interpolants B A)
(exit)
