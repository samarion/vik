; From cvc5: regress0/datatypes/issue1433.smt2 (modified BSD, LICENSES/cvc5.txt)
; EXPECT: sat
(set-logic QF_UFDTLIA)
(set-info :status sat)
(declare-datatype MyList (par (T) ((nelem) (cons (hd T) (tl (MyList T))))))

(declare-fun a () (MyList Int))
(assert (> (hd a) 50))
(set-info :status sat)
(check-sat)
