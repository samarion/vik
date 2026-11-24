; From cvc5: regress0/aufbv/cee-small-shared-eq.smt2 (modified BSD, LICENSES/cvc5.txt)
; COMMAND-LINE: --ee-mode=distributed
; COMMAND-LINE: --ee-mode=central
; EXPECT: sat
; logic: QF_ABV, the smallest the script fits, for ALL (prune logic)
(set-logic QF_ABV)
(set-info :status sat)
(declare-fun a () (Array (_ BitVec 1) (_ BitVec 16)))
(assert (not (= (_ bv0 16) (select a ((_ extract 14 14) (select a (_ bv0 1)))))))
(set-info :status sat)
(check-sat)
