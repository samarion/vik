; From cvc5: regress0/datatypes/mutual-rec-param-dt.smt2 (modified BSD, LICENSES/cvc5.txt)
; Modified for VIK: the `nil` of `List2` is renamed `nil2`. VIK refuses a name that two datatypes share (issue 230), which cvc5 and z3 accept.


(set-logic ALL)
(set-option :produce-models true)
(set-info :status sat)
(declare-datatypes ( (List 1) (List2 1) ) (
(par ( X ) 
( (cons (head X) (tail (List2 X))) (nil))
)
(par ( Y ) 
( (cons2 (head2 Y) (tail2 (List Y))) (nil2))
)
))
(declare-fun a () (List Int))
(declare-fun b () (List Int))
(assert (= (head a) 5))
(check-sat)
