; From cvc5: regress0/datatypes/issue12930-tester-quoted-cons.smt2 (modified BSD, LICENSES/cvc5.txt)
; EXPECT: sat
(set-logic ALL)
(declare-datatypes ((T 1)) ((par (a) ((|C,| (|fst,| a) (|snd,| a)) (|D,|)))))
(declare-const s (T Int))
(assert ((_ is |C,|) s))
(assert (not ((_ is |D,|) s)))
(set-info :status sat)
(check-sat)
