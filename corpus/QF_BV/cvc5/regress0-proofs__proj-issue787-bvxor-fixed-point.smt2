; From cvc5: regress0/proofs/proj-issue787-bvxor-fixed-point.smt2 (modified BSD, LICENSES/cvc5.txt)
; COMMAND-LINE: --check-proofs
; EXPECT: unsat
; logic: QF_BV, the smallest the script fits, for ALL (prune logic)
(set-logic QF_BV)
(declare-fun x () (_ BitVec 4))
(assert (not (=
  (bvand #b1011
         (bvand x
                (bvor (bvxor (bvxor x (bvnot x) x (_ bv1 4) x)
                             (bvnot x)
                             x
                             x
                             x)
                      x
                      x
                      (bvand (bvadd #x2 x x) x))
                      x
                      x)
                #b1110)
         (bvand #b1010 x))))
(set-info :status unsat)
(check-sat)
