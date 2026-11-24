; From cvc5: regress0/datatypes/tenum-bug.smt2 (modified BSD, LICENSES/cvc5.txt)
; logic: QF_DT, the smallest the script fits, for QF_ALL (prune logic)
(set-logic QF_DT)
(set-info :status sat)

(declare-datatypes ((DNat 0) (Nat 0)) (((dnat (data Nat)))
                                       ((succ (pred DNat)) (zero))))

(declare-fun x () Nat)

(assert (not (= x zero)))

(check-sat)
