; From cvc5: regress0/datatypes/dt-param-card4-bool-sat.smt2 (modified BSD, LICENSES/cvc5.txt)
; EXPECT: sat
; logic: QF_DT, the smallest the script fits, for QF_ALL (prune logic)
(set-logic QF_DT)
(set-info :status sat)
(declare-datatypes ((Pair 2)) ((par (T S) ((pair (first T) (second S))))))

(declare-fun p1 () (Pair Bool Bool))
(declare-fun p2 () (Pair Bool Bool))
(declare-fun p3 () (Pair Bool Bool))
(declare-fun p4 () (Pair Bool Bool))

(assert (distinct p1 p2 p3 p4))
(set-info :status sat)
(check-sat)
