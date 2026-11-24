; Hand-written for VIK (this repository's license), from bench/fuzz.py (seed 20261123): `(Opt (_ BitVec 1))` has
; three values, and four distinct constants of it are unsat. With the fields of datatype values left to the
; final check, the check compared each class with the first class of its value only: `(some k3)` was first
; with `(some #b0)`, apart from neither `k11` nor `k13`, which shared the value and were never compared, and
; the answer was sat (step 10 of #192, 2026-11-23, before it was pushed).
(set-logic ALL)
(declare-sort U 0)
(declare-datatypes ((D0 0)) (((c0_0 (s0_0_0 U)) (c0_1 (s0_1_0 (_ BitVec 3)) (s0_1_1 (_ BitVec 4))) (c0_2))))
(declare-datatype Opt (par (T) ((none) (some (val T)))))
(declare-datatype Pair (par (A B) ((pair (fst A) (snd B)))))
(declare-const k0 Bool)
(declare-const k1 Bool)
(declare-const k3 (_ BitVec 1))
(declare-const k10 (Opt (_ BitVec 1)))
(declare-const k11 (Opt (_ BitVec 1)))
(declare-const k12 (Opt (_ BitVec 1)))
(declare-const k13 (Opt (_ BitVec 1)))
(assert (ite (not k0) (distinct (some k3) (as none (Opt (_ BitVec 1))) (ite k0 k12 k10)) k1))
(assert (distinct k10 k11 k12 k13))
(set-info :status unsat)
(check-sat)
