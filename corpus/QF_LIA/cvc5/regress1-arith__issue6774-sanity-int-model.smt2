; From cvc5: regress1/arith/issue6774-sanity-int-model.smt2 (modified BSD, LICENSES/cvc5.txt)
; COMMAND-LINE: -i
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
(set-logic ALIRA)
(declare-const x Real)
(declare-fun i () Int)
(declare-fun i1 () Int)
(push)
(assert (< 1 (- i)))
(set-info :status sat)
(check-sat)
(pop)
(push)
(assert (or (>= i1 (* 5 (- i)))))
(set-info :status sat)
(check-sat)
(pop)
(assert (or (> i1 1) (= x (to_real i))))
(set-info :status sat)
(check-sat)
(assert (not (is_int x)))
(set-info :status sat)
(check-sat)
