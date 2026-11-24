; From cvc5: regress0/fmf/proj-issue622-fmf-dt-u-orig.smt2 (modified BSD, LICENSES/cvc5.txt)
; Modified for VIK: the constructors and selectors named alike in two datatypes are renamed in the later one (`c2`, `s2`, `c3`, `s3`, `_c2`, `_s2`). VIK refuses a name that two datatypes share (issue 230), which cvc5 and z3 accept.
; EXPECT: sat
(set-logic DT)
(set-option :finite-model-find true)
(declare-sort u 0)
(declare-datatypes ((d 1) (t 2)) ((par (p) ((c (s (t p p))))) (par (p p) ((c2 (d p)) (_c (s2 (d p)))))))
(declare-datatypes ((_d 0) (dt 0)) (((c3) (o (s3 dt) (_s dt) (e u) (se (t u u)))) ((_c2 (_s2 u)))))
(declare-const x _d)
(assert ((_ is o) x))
(set-info :status sat)
(check-sat)
