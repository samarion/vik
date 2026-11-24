; Hand-written for VIK (this repository's license): a constructor applied to `(bvnot a)`, which the
; lowering makes the linear term `3 - a`. Its class, alone and without a variable of the simplex, got a
; fresh number in the model: `x = (mk #b01)` with `a = #b01`, against the first assertion (issue 137,
; 2026-11-18).
; EXPECT: sat
; EXPECT: ((x (mk #b10)) ((f x) #b10) ((= x (mk (bvnot a))) true))
(set-logic QF_UFBVDT)
(set-option :produce-models true)
(declare-datatype P ((mk (f (_ BitVec 2)))))
(declare-const a (_ BitVec 2))
(declare-const x P)
(assert (= x (mk (bvnot a))))
(assert (= a #b01))
(set-info :status sat)
(check-sat)
(get-value (x (f x) (= x (mk (bvnot a)))))
