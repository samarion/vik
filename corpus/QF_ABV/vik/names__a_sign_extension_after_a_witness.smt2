; Hand-written for VIK (this repository's license): the solver named the witnesses of extensionality `ext!N`,
; and the lowering named the cases of a `sign_extend` `ext!N` too, each avoiding its own names only: the
; second check declared a name the solver had used, and VIK threw (issue 158, found by the fuzzer of #157).
; The two have names of their own now, which no script declares either (issue 194).
(set-logic ALL)
(declare-const k1 Bool)
(declare-const k2 Int)
(declare-const k4 (_ BitVec 3))
(declare-const k6 (_ BitVec 4))
(declare-const a0_0 (Array (_ BitVec 1) Int))
(assert (not (distinct (ite k1 a0_0 a0_0) (store a0_0 #b1 (- 2)) (store a0_0 #b1 k2) (store a0_0 #b1 k2))))
(set-info :status sat)
(check-sat)
(assert (= (bvmul k6 ((_ sign_extend 1) k4)) k6))
(set-info :status sat)
(check-sat)
