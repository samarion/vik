; From cvc5: regress0/datatypes/dt-param-simple-unsat.smt2 (modified BSD, LICENSES/cvc5.txt)
; Logos does not support parametric datatype declarations.
; DISABLE-TESTER: cpc-logos
; EXPECT: unsat
(set-logic ALL)
(declare-datatypes ( (List 1) ) (
(par ( X ) ( (nil) (cons (head X) (tail (List X)))))
))
(declare-fun x () (List Int))
(assert (= (cons 0 x) (as nil (List Int))))
(set-info :status unsat)
(check-sat)
