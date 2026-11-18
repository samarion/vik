; From cvc5: regress0/arrays/issue3065-write-chain.smt2 (modified BSD, LICENSES/cvc5.txt)
; EXPECT: sat
; EXPECT: sat
; logic: QF_AUFLIA, the smallest the script fits, for ALL (prune logic)
(set-logic QF_AUFLIA)
(set-option :incremental true)
(declare-fun x () (Array Int (Array Int Int)))
(assert (= (select (select x 0) 0) (select (select x 1) 1)))
(set-info :status sat)
(check-sat)
(assert (= x (store x 0 (select x 1))))
(set-info :status sat)
(check-sat)
