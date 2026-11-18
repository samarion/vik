; From cvc5: regress0/aufbv/bug338.smt2 (modified BSD, LICENSES/cvc5.txt)
; logic: QF_ABV, the smallest the script fits, for QF_AUFBV (prune logic)
(set-logic QF_ABV)
(declare-sort U 0)
(declare-sort Index 0)
(declare-sort Element 0)
(declare-fun memory_0 () (Array (_ BitVec 32) (_ BitVec 8)))
(set-info :status sat)

(set-info :notes "RewriteRule <ExtractBitwise>; expect unsat")

(assert (not (= ((_ extract 7 0) (bvor (_ bv65536 32) (concat (_ bv0 25) ((_ extract 7 1) (select memory_0 (_ bv1 32)))) (concat (_ bv0 24) (select memory_0 (_ bv1 32))))) (bvor ((_ extract 7 0) (_ bv65536 32)) ((_ extract 7 0) (concat (_ bv0 25) ((_ extract 7 1) (select memory_0 (_ bv1 32)))))))))
(check-sat)


(exit)
