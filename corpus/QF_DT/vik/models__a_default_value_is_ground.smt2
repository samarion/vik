; Hand-written for VIK (this repository's license): default values of datatypes whose first constructor
; leads back to the sort. The default took that constructor and stopped at the sort's second visit with an
; abstract element, which is no datatype value: `y = (rec (rec @D!3))` (issue 140, 2026-11-18). The sorts
; `A` and `B` recur through each other. The values of distinct classes differ (issue 127), so they are deeper
; than the defaults, which end each of them.
; EXPECT: sat
; EXPECT: ((define-fun u () A (a1 (b1 (a1 (b1 (a1 (b1 (a1 (b2 false))))))))) (define-fun v () D (rec (rec (base false)))) (define-fun y () D (rec (rec (rec (rec (rec (base false))))))))
; EXPECT: (((next y) (rec (rec (rec (rec (base false)))))) ((next (next y)) (rec (rec (rec (base false))))) ((next v) (rec (base false))))
(set-logic QF_DT)
(set-option :produce-models true)
(declare-datatype D ((rec (next D)) (base (n Bool))))
(declare-datatypes ((A 0) (B 0)) (((a1 (ab B))) ((b1 (ba A)) (b2 (bz Bool)))))
(declare-const y D)
(declare-const u A)
(declare-const v D)
(assert ((_ is rec) v))
(set-info :status sat)
(check-sat)
(get-model)
(get-value ((next y) (next (next y)) (next v)))
