; From cvc5: regress0/fmf/proj-issue622-fmf-dt-u.smt2 (modified BSD, LICENSES/cvc5.txt)
; Modified for VIK: the selector and the constructor named alike in two datatypes are renamed in the later one (`s3`, `_c2`). VIK refuses a name that two datatypes share (issue 230), which cvc5 and z3 accept.
; EXPECT: sat
; logic: QF_UFDT, the smallest the script fits, for DT (prune logic)
(set-logic QF_UFDT)
(set-option :finite-model-find true)
(declare-sort u 0)
(declare-datatypes ((d 1) (t 1)) (
(par (p) ((c (s (t p)))))
(par (p) ((g (j p)) (_c (s2 (d p)))))))
(declare-datatypes ((_d 0) (dt 0)) (
((h) (o (s3 dt) (_s dt) (e u) (se (t u)))) 
((_c2 (k u)))))
(declare-const x _d)
(assert ((_ is o) x))
(set-info :status sat)
(check-sat)
