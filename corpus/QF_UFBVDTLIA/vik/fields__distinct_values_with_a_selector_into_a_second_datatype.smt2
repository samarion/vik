; Hand-written for VIK (this repository's license), from bench/fuzz.py (seed 20261123, script 3728, minimized):
; three distinct values of a datatype, one a selector of a second datatype, one under an `ite`. The first version of
; step 10 of #192, which compares datatype values in the final check, compared each class with the first class of
; its value only. Two constants the script keeps apart got one value, and the model of check-sat 1 failed its check
; (2026-11-23, before it was pushed).
(set-logic ALL)
(declare-datatypes ((D0 0) (D1 0)) (((c0_0 (s0_0_0 (_ BitVec 8)))) ((c1_0) (c1_1 (s1_1_0 Int) (s1_1_1 (_ BitVec 1))) (c1_2 (s1_2_0 D0)))))
(declare-const k0 Bool)
(declare-const k7 D0)
(declare-const k8 D0)
(declare-const k9 D0)
(declare-const k11 D1)
(assert (distinct k9 (s1_2_0 k11) (ite k0 k7 k8)))
(set-info :status sat)
(check-sat)
