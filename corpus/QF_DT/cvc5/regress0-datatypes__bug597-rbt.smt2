; From cvc5: regress0/datatypes/bug597-rbt.smt2 (modified BSD, LICENSES/cvc5.txt)
(set-option :global-declarations true)
(set-logic ALL)
(set-info :status sat)

; Tree type
(declare-datatypes ((Tree 0)) (((node (data Int) (color Bool) (left Tree) (right Tree)) (nil))))

; content function
(declare-fun size (Tree) Int)
(assert (= (size nil) 0))


(check-sat)
