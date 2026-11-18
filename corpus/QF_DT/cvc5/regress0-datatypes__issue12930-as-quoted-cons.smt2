; From cvc5: regress0/datatypes/issue12930-as-quoted-cons.smt2 (modified BSD, LICENSES/cvc5.txt)
; EXPECT: sat
(set-logic ALL)
(declare-datatypes ((T 1)) ((par (a) ((|C,| (|fst| a) (|snd| a))))))
(declare-const s (T Int))
(assert (= s ((as |C,| (T Int)) 1 2)))
(set-info :status sat)
(check-sat)
