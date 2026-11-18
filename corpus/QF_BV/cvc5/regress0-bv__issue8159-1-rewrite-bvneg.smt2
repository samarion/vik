; From cvc5: regress0/bv/issue8159-1-rewrite-bvneg.smt2 (modified BSD, LICENSES/cvc5.txt)
; COMMAND-LINE: --incremental
(set-logic QF_BV)
(assert (= (_ bv1 1) (bvsmod (_ bv0 1) (bvneg (bvneg (_ bv0 1))))))
(push)
(set-info :status unsat)
(check-sat)
