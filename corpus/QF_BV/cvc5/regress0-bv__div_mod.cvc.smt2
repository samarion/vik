; From cvc5: regress0/bv/div_mod.cvc.smt2 (modified BSD, LICENSES/cvc5.txt)
; The cpc-logos tester takes more than 60 seconds.
; DISABLE-TESTER: cpc-logos
; EXPECT: unsat
; logic: QF_BV, the smallest the script fits, for ALL (prune logic)
(set-logic QF_BV)
(set-option :incremental false)
(declare-fun x () (_ BitVec 4))
(set-info :status unsat)
(check-sat-assuming ( (not (let ((_let_1 (bvsdiv x #b0000))) (and (and (and (and (= (bvudiv x #b0000) #b1111) (= (bvurem x #b0000) x)) (or (= _let_1 #b1111) (= _let_1 #b0001))) (= (bvsrem x #b0000) x)) (= (bvsmod x #b0000) x)))) ))
