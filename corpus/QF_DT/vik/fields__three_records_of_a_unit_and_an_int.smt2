; Hand-written for VIK (this repository's license): three `of-W` values pairwise apart, `W` a record of a
; `Unit` and an `Int`: infinite, though one of its fields is finite (issue 125, 2026-11-17).
; EXPECT: sat
; EXPECT: ((define-fun x () Val (of-W (mk unit 1))) (define-fun y () Val (of-W (mk unit 2))) (define-fun z () Val (of-W (mk unit 3))))
(set-logic ALL)
(set-option :produce-models true)
(declare-datatypes ((Unit 0) (W 0) (Val 0)) (((unit)) ((mk (u Unit) (n Int))) ((of-Int (to-Int Int)) (of-W (to-W W)))))
(declare-const x Val)
(declare-const y Val)
(declare-const z Val)
(assert ((_ is of-W) x))
(assert ((_ is of-W) y))
(assert ((_ is of-W) z))
(assert (distinct x y z))
(set-info :status sat)
(check-sat)
(get-model)
