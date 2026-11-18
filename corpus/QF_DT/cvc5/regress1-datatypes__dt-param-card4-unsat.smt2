; From cvc5: regress1/datatypes/dt-param-card4-unsat.smt2 (modified BSD, LICENSES/cvc5.txt)
; Logos does not support parametric datatype declarations.
; DISABLE-TESTER: cpc-logos
; EXPECT: unsat
; logic: QF_DT, the smallest the script fits, for QF_ALL (prune logic)
(set-logic QF_DT)
(set-info :status unsat)
(declare-datatypes ((Pair 2)) ((par (T S) ((pair (first T) (second S))))))

(declare-datatypes ((Color 0)) (((red) (blue))))

(declare-fun p1 () (Pair Color Color))
(declare-fun p2 () (Pair Color Color))
(declare-fun p3 () (Pair Color Color))
(declare-fun p4 () (Pair Color Color))
(declare-fun p5 () (Pair Color Color))

(assert (distinct p1 p2 p3 p4 p5))
(set-info :status unsat)
(check-sat)
