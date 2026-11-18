; From cvc5: regress0/arrays/issue10494.smt2 (modified BSD, LICENSES/cvc5.txt)
; EXPECT: sat
; logic: QF_ABV, the smallest the script fits, for ALL (prune logic)
(set-logic QF_ABV)
(declare-const a (Array (_ BitVec 64) (_ BitVec 64)) ) 
(declare-const b (_ BitVec 64) ) 
(assert ( = a ( store a ( bvneg ( bvneg #x1111111111111111 ) ) 
        ( bvadd #x1111111111111111 ( select a #x0000000000000000 ) ) ) ) ) 
( check-sat )
