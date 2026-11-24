; From cvc5: regress0/aufbv/issue3687-check-models-small.smt2 (modified BSD, LICENSES/cvc5.txt)
; EXPECT: sat
; logic: QF_ABV, the smallest the script fits, for QF_AUFBV (prune logic)
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun b () (_ BitVec 2))
(assert (distinct #b01 (select (store (store a #b01 (bvor #b01 (select a
  #b00))) #b10 #b00) b)))
(set-info :status sat)
(check-sat)
