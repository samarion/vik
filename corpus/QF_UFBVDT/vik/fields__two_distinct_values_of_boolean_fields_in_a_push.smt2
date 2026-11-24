; Hand-written for VIK (this repository's license), from bench/fuzz.py (seed 20261123, script 6549, minimized): two
; distinct constants of a datatype of Boolean and bit-vector fields, in a push after a tester. The first version of
; step 10 of #192, which compares datatype values in the final check, compared each class with the first class of
; its value only. Two constants the script keeps apart got one value, and the model of check-sat 2 failed its check
; (2026-11-23, before it was pushed).
(set-logic ALL)
(declare-datatypes ((D0 0) (D1 0) (D2 0)) (((c0_0 (s0_0_0 (_ BitVec 4))) (c0_1 (s0_1_0 D0)) (c0_2 (s0_2_0 (_ BitVec 3)) (s0_2_1 (_ BitVec 1)))) ((c1_0 (s1_0_0 Bool)) (c1_1 (s1_1_0 Bool)) (c1_2 (s1_2_0 (_ BitVec 8)))) ((c2_0) (c2_1) (c2_2 (s2_2_0 D1)))))
(declare-const k6 D1)
(declare-const k7 D1)
(declare-const k10 D2)
(assert ((_ is c2_2) k10))
(set-info :status sat)
(check-sat)
(push 1)
(assert (distinct k6 k7))
(set-info :status sat)
(check-sat)
(pop 1)
(set-info :status sat)
(check-sat)
