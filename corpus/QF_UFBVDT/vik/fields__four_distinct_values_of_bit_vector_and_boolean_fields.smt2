; Hand-written for VIK (this repository's license), from bench/fuzz.py (seed 20261123, script 1632, minimized): four
; distinct constants of a datatype with a bit-vector field and a Boolean one, beside a selector applied off its
; constructor. The first version of step 10 of #192, which compares datatype values in the final check, compared
; each class with the first class of its value only. Two constants the script keeps apart got one value, and the
; model of check-sat 1 failed its check (2026-11-23, before it was pushed).
(set-logic ALL)
(declare-datatypes ((D0 0)) (((c0_0 (s0_0_0 (_ BitVec 4))) (c0_1 (s0_1_0 Bool)))))
(declare-const k6 (_ BitVec 4))
(declare-const k7 D0)
(declare-const k8 D0)
(declare-const k9 D0)
(declare-const k10 D0)
(assert (s0_1_0 (c0_0 k6)))
(assert (distinct k7 k8 k9 k10))
(set-info :status sat)
(check-sat)
