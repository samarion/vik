; Hand-written for VIK (this repository's license), from a script of bench/fuzz.py (seed 20261123): `D0` is
; infinite through the uninterpreted `U`, so `c1_2` has values to spare, around a new element of `U`. The
; model had no new element to give, and gave the distinct `k12` and `k14` one value, `(c1_2 c0_0)`
; (issue 127, 2026-11-23).
; EXPECT: sat
; EXPECT: (((distinct k12 k13 k14 k15) true))
(set-logic ALL)
(set-option :produce-models true)
(declare-sort U 0)
(declare-datatypes ((D0 0) (D1 0)) (((c0_0) (c0_1 (s0_1_0 U))) ((c1_0) (c1_1 (s1_1_0 (_ BitVec 8)) (s1_1_1 (_ BitVec 3))) (c1_2 (s1_2_0 D0)))))
(declare-const k12 D1)
(declare-const k13 D1)
(declare-const k14 D1)
(declare-const k15 D1)
(assert (distinct k12 k13 k14 k15))
(assert ((_ is c1_1) k13))
(assert ((_ is c1_1) k15))
(set-info :status sat)
(check-sat)
(get-value ((distinct k12 k13 k14 k15)))
