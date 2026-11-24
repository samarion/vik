; From z3test: z3name_bug.smt2 (MIT, LICENSES/z3test.txt)
; EXPECT: sat
; EXPECT: ((define-fun p ((x!0 Int)) Bool (ite (= x!0 10) true (ite (= x!0 1) true true))))
; logic: QF_UFLIA, the smallest the script fits, which set none (prune logic)
(set-logic QF_UFLIA)

; Copyright (c) 2015 Microsoft Corporation

(set-option :model.compact true)
(declare-fun p (Int) Bool)
;(declare-fun f (Int Real) Bool)

(assert (p (ite (p 1) 10 20)))
(assert (p 1))
(set-info :status sat)
(check-sat-using (then nnf smt))
(get-model)

