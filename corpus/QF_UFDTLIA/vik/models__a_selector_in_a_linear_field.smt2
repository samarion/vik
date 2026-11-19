; Hand-written for VIK (this repository's license): a constructor applied to sums over the fields of `a`, which
; the e-graph never sees: `a` and its selectors are in no class. The sums' classes were valued with `(c a)` and
; `(s a)` at 0, and `a`, built anew each time it was valued, got fresh fields: `lt = (mk (- 1) 1)` with
; `a = (mk 2 3)` and `x = 1`, against the assertion (Stainless's `Acc` benchmark, `valid-Acc__0`).
; EXPECT: sat
; EXPECT: ((define-fun a () Acc (mk 1 2)) (define-fun lt () Acc (mk 0 3)) (define-fun x () Int 1))
(set-logic QF_UFDTLIA)
(set-option :produce-models true)
(declare-datatype Acc ((mk (c Int) (s Int))))
(declare-const a Acc)
(declare-const lt Acc)
(declare-const x Int)
(assert (= lt (mk (- (c a) x) (+ (s a) x))))
(assert (> x 0))
(set-info :status sat)
(check-sat)
(get-model)
