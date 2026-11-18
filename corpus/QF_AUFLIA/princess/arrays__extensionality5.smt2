; From princess: arrays/extensionality5.smt2 (BSD, LICENSES/princess.txt)
; Example that previously led to non-termination in
; ExtArray.ArraySort.augmentModelTermSet
; logic: QF_AUFLIA, the smallest the script fits, which set none (prune logic)
(set-logic QF_AUFLIA)

(declare-const a (Array Int Int))
(declare-const b (Array Int Int))

(assert (= a ((as const (Array Int Int)) 1)))
(assert (= b (store a 1 1)))

(set-info :status sat)
(check-sat)
(get-model)

