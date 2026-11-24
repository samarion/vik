; Hand-written for VIK (this repository's license), from bench/fuzz.py (seed 20261123, script 6994, minimized): two
; distinct constants of a datatype whose one field is another datatype, beside a datatype with an uninterpreted
; field. The first version of step 10 of #192, which compares datatype values in the final check, compared each
; class with the first class of its value only. Two constants the script keeps apart got one value, and the model of
; check-sat 1 failed its check (2026-11-23, before it was pushed).
(set-logic ALL)
(declare-sort U 0)
(declare-datatypes ((D0 0) (D1 0) (D2 0)) (((c0_0 (s0_0_0 (_ BitVec 3)))) ((c1_0 (s1_0_0 D0))) ((c2_0) (c2_1 (s2_1_0 (_ BitVec 1)) (s2_1_1 U)))))
(declare-const k0 Bool)
(declare-const k7 D0)
(declare-const k8 D1)
(declare-const k9 D1)
(assert (ite (not (ite k0 false k0)) k0 ((_ is c1_0) (c1_0 k7))))
(assert (distinct k8 k9))
(set-info :status sat)
(check-sat)
