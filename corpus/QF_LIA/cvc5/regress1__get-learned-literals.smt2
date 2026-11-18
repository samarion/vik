; From cvc5: regress1/get-learned-literals.smt2 (modified BSD, LICENSES/cvc5.txt)
; SCRUBBER: sed -e 's/(>=.*/learned-ineq/'
; EXPECT: sat
; EXPECT: (
; EXPECT: learned-ineq
; EXPECT: learned-ineq
; EXPECT: )
; logic: QF_LIA, the smallest the script fits, for ALL (prune logic)
(set-logic QF_LIA)
(set-option :produce-learned-literals true)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)

(assert (> x 5))
(assert (< y 4))
(assert (or (< x y) (> z 0)))
(set-info :status sat)
(check-sat)
(get-learned-literals)
