; Hand-written for VIK (this repository's license): four `of-Pair` values pairwise apart, as many as a pair of
; `Bool`s has. The model repeated `(mk false false)` before the fields were bounded (issue 125, 2026-11-17).
; EXPECT: sat
; EXPECT: ((define-fun w () Val (of-Pair (mk false false))) (define-fun x () Val (of-Pair (mk true true))) (define-fun y () Val (of-Pair (mk true false))) (define-fun z () Val (of-Pair (mk false true))))
(set-logic ALL)
(set-option :produce-models true)
(declare-datatypes ((Pair 0) (Val 0)) (((mk (fst Bool) (snd Bool))) ((of-Int (to-Int Int)) (of-Pair (to-Pair Pair)))))
(declare-const x Val)
(declare-const y Val)
(declare-const z Val)
(declare-const w Val)
(assert ((_ is of-Pair) x))
(assert ((_ is of-Pair) y))
(assert ((_ is of-Pair) z))
(assert ((_ is of-Pair) w))
(assert (distinct x y z w))
(set-info :status sat)
(check-sat)
(get-model)
