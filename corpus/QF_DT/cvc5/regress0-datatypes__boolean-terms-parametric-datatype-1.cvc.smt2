; From cvc5: regress0/datatypes/boolean-terms-parametric-datatype-1.cvc.smt2 (modified BSD, LICENSES/cvc5.txt)
; EXPECT: sat
(set-logic ALL)
(set-option :incremental false)
(declare-datatypes ((RightistTree 1)) ((par (T)((node (left Bool) (right (RightistTree T))) (leaf (data T))))))
(declare-fun x () (RightistTree Int))
(assert (not (= x (leaf 0))))
(set-info :status sat)
(check-sat)
