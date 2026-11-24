; From princess: adt/datatype6b.smt2 (BSD, LICENSES/princess.txt)
; EXPECT: sat
; EXPECT: ((define-fun a () List (cons 4 (cons 3 nil))) (define-fun b () List (cons 2 (cons 1 nil))))


(declare-datatype List ( (nil) (cons (head Int) (tail List)) ))

(declare-const a List)
(declare-const b List)

(assert (not (= a b)))
(set-info :status sat)
(check-sat)
(get-model)

