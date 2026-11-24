; Hand-written for VIK (this repository's license), from bench/fuzz.py (seed 20261123, script 530, minimized): an
; array indexed by datatype values with a store, then four distinct constants of the datatype in a push. The first
; version of step 10 of #192, which compares datatype values in the final check, compared each class with the first
; class of its value only. Two constants the script keeps apart got one value, and the model of check-sat 2 failed
; its check (2026-11-23, before it was pushed).
(set-logic ALL)
(declare-datatypes ((D0 0)) (((c0_0 (s0_0_0 (_ BitVec 2))))))
(declare-const k1 Bool)
(declare-const k10 D0)
(declare-const k11 D0)
(declare-const k12 D0)
(declare-const k13 D0)
(declare-const a1_0 (Array D0 D0))
(declare-fun issue133 (Int) Int)
(assert (= (ite k1 a1_0 a1_0) (store a1_0 k13 k10)))
(assert (= (issue133 0) 1))
(set-info :status sat)
(check-sat)
(push 1)
(assert (distinct k10 k11 k12 k13))
(set-info :status sat)
(check-sat)
(pop 1)
(set-info :status sat)
(check-sat)
