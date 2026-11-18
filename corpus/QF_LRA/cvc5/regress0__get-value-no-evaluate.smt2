; From cvc5: regress0/get-value-no-evaluate.smt2 (modified BSD, LICENSES/cvc5.txt)
; COMMAND-LINE: -q
; SCRUBBER: sed 's/(.*//g'
; EXPECT: sat
; logic: QF_LRA, the smallest the script fits, for ALL (prune logic)
(set-logic QF_LRA)
(set-option :global-declarations true)
(set-option :produce-models true)
(declare-const _x29 Real)
(set-info :status sat)
(check-sat)
(get-value ((forall ((_x56 Real)) (=> (>= _x29 _x56 _x29) (>= _x29 _x56 _x29)))))
