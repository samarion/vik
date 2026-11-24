; From cvc5: regress0/proofs/trust-subs-eq-open.smt2 (modified BSD, LICENSES/cvc5.txt)
; logic: QF_BV, the smallest the script fits, for ALL (prune logic)
(set-logic QF_BV)
(set-info :status unsat)
(declare-fun c () (_ BitVec 3))
(check-sat-assuming (
(and 
(= (_ bv0 1) ((_ extract 1 1) c)) 
(= (_ bv1 1) ((_ extract 0 0) c)) 
(not (= (_ bv1 2) ((_ extract 1 0) c))))))
