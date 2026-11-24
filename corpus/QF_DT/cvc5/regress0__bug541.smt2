; From cvc5: regress0/bug541.smt2 (modified BSD, LICENSES/cvc5.txt)
; Logos does not support parametric datatype declarations.
; DISABLE-TESTER: cpc-logos
; EXPECT: unsat
(set-logic ALL)
(declare-datatypes ((Pair 2)) ((par (T1 T2) ((mk-pair (first T1) (second T2))))))
(assert (= (mk-pair 0.0 0.0) (mk-pair 1.5 2.5)))
(set-info :status unsat)
(check-sat)
(exit)
