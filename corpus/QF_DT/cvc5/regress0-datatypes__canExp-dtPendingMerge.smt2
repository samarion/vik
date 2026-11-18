; From cvc5: regress0/datatypes/canExp-dtPendingMerge.smt2 (modified BSD, LICENSES/cvc5.txt)
; COMMAND-LINE: --ee-mode=distributed
; COMMAND-LINE: --ee-mode=central
; EXPECT: unsat
; logic: QF_DT, the smallest the script fits, for ALL (prune logic)
(set-logic QF_DT)
(set-info :status unsat)
(declare-datatypes ((T 0)) (((A) (B (proj0B T) (proj1B T)) (C (proj0C T)) (D (proj0D T) ))))
(declare-fun w () T)
(declare-fun u () T)
(assert (= w (B (D u) (B (D u) (C w)))))
(set-info :status unsat)
(check-sat)
