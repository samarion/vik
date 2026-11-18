; Hand-written for VIK (this repository's license): arrays indexed by bit-vectors, read and written at
; constants. The model gave each index an abstract element, `|@(_ BitVec 4)!0|`, in place of its number:
; a read at `x` missed its row, so `(= (select a x) #x5)` was false in the model of the script that
; asserts it, and z3 refused the model's text for the unknown constant (issue 138, 2026-11-18).
; EXPECT: sat
; EXPECT: ((x #b0001) (y #b0000) (k #b0001) ((select a x) #b0101) ((select a y) #b0110) ((= (select a x) #x5) true) ((select b k) #b0111) ((select b x) #b0111))
; EXPECT: ((define-fun a () (Array (_ BitVec 4) (_ BitVec 4)) (store (store ((as const (Array (_ BitVec 4) (_ BitVec 4))) #b0000) #b0000 #b0110) #b0001 #b0101)) (define-fun b () (Array (_ BitVec 4) (_ BitVec 4)) (store (store (store (store (store ((as const (Array (_ BitVec 4) (_ BitVec 4))) #b0000) #b0000 #b0110) #b0001 #b0101) #b0001 #b0111) #b0000 #b0110) #b0001 #b0111)) (define-fun k () (_ BitVec 4) #b0001) (define-fun x () (_ BitVec 4) #b0001) (define-fun y () (_ BitVec 4) #b0000))
(set-logic QF_ABV)
(set-option :produce-models true)
(declare-const a (Array (_ BitVec 4) (_ BitVec 4)))
(declare-const b (Array (_ BitVec 4) (_ BitVec 4)))
(declare-const x (_ BitVec 4))
(declare-const y (_ BitVec 4))
(declare-const k (_ BitVec 4))
(assert (= (select a x) #x5))
(assert (= (select a y) #x6))
(assert (= b (store a k #x7)))
(assert (bvugt k y))
(set-info :status sat)
(check-sat)
(get-value (x y k (select a x) (select a y) (= (select a x) #x5) (select b k) (select b x)))
(get-model)
