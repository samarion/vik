; Hand-written for VIK (this repository's license): twenty stores into a constant array of a 6-bit index
; are not another constant array. Every two stores of the chain were an equality with a witness, read by
; every array of the sort: sixteen stores ran out of a 3 GB heap (2026-11-19).
(set-logic QF_ABV)
(assert (= (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store ((as const (Array (_ BitVec 6) Int)) 0) (_ bv0 6) 1) (_ bv1 6) 1) (_ bv2 6) 1) (_ bv3 6) 1) (_ bv4 6) 1) (_ bv5 6) 1) (_ bv6 6) 1) (_ bv7 6) 1) (_ bv8 6) 1) (_ bv9 6) 1) (_ bv10 6) 1) (_ bv11 6) 1) (_ bv12 6) 1) (_ bv13 6) 1) (_ bv14 6) 1) (_ bv15 6) 1) (_ bv16 6) 1) (_ bv17 6) 1) (_ bv18 6) 1) (_ bv19 6) 1) ((as const (Array (_ BitVec 6) Int)) 1)))
(set-info :status unsat)
(check-sat)
