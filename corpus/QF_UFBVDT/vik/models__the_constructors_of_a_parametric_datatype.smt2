; Hand-written for VIK (this repository's license): the constructors of a parametric datatype in a model.
; An instance's constructors have names of the parser's, and the model printed them: `|cons@(_ BitVec 2)|`
; and `nil@Int`, which no solver reads back (issue 142, 2026-11-17). They are written `(as cons (List τ))`,
; as cvc5 writes them, at one parameter and at two, and inside one another.
; EXPECT: sat
; EXPECT: ((define-fun l () (List (_ BitVec 2)) ((as cons (List (_ BitVec 2))) #b11 (as nil (List (_ BitVec 2))))) (define-fun n () (List (Pair Bool Bool)) ((as cons (List (Pair Bool Bool))) ((as pair (Pair Bool Bool)) true false) (as nil (List (Pair Bool Bool))))) (define-fun p () (Pair (_ BitVec 2) Bool) ((as pair (Pair (_ BitVec 2) Bool)) #b01 true)))
; EXPECT: ((l ((as cons (List (_ BitVec 2))) #b11 (as nil (List (_ BitVec 2))))) ((tail l) (as nil (List (_ BitVec 2)))) (p ((as pair (Pair (_ BitVec 2) Bool)) #b01 true)) ((head n) ((as pair (Pair Bool Bool)) true false)))
(set-logic QF_UFBVDT)
(set-option :produce-models true)
(declare-datatypes ((List 1)) ((par (T) ((nil) (cons (head T) (tail (List T)))))))
(declare-datatype Pair (par (A B) ((pair (fst A) (snd B)))))
(declare-const l (List (_ BitVec 2)))
(declare-const p (Pair (_ BitVec 2) Bool))
(declare-const n (List (Pair Bool Bool)))
(assert (= l (cons #b11 (as nil (List (_ BitVec 2))))))
(assert (= (fst p) #b01))
(assert (snd p))
(assert (= n (cons (pair true false) (as nil (List (Pair Bool Bool))))))
(set-info :status sat)
(check-sat)
(get-model)
(get-value (l (tail l) p (head n)))
