; Hand-written for VIK (this repository's license): `int_to_bv` of an unbounded integer and of the same
; integer plus the modulus, or plus one against a `bvadd`. Each `int_to_bv` is a residue `r` with
; `n = r + 2^w × k`, the overflow count `k` unbounded, and branch and bound walked the counts: no answer
; in 20 s on the first two checks (issue 150, 2026-11-17). The integer equations leave the difference of
; two residues a multiple of `2^w`, which their bounds exclude.
(set-logic ALL)
(declare-const n Int)
(push 1)
(assert (not (= ((_ int_to_bv 2) n) ((_ int_to_bv 2) (+ n 4)))))
(set-info :status unsat)
(check-sat)
(pop 1)
(push 1)
(assert (not (= ((_ int_to_bv 4) n) ((_ int_to_bv 4) (+ n 16)))))
(set-info :status unsat)
(check-sat)
(pop 1)
(push 1)
(assert (not (= ((_ int_to_bv 2) (+ n 1)) (bvadd ((_ int_to_bv 2) n) #b01))))
(set-info :status unsat)
(check-sat)
(pop 1)
(assert (not (= ((_ int_to_bv 2) (+ n 1)) ((_ int_to_bv 2) n))))
(set-info :status sat)
(check-sat)
