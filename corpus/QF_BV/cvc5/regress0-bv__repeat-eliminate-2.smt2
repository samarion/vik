; From cvc5: regress0/bv/holes/repeat-eliminate-2.smt2 (modified BSD, LICENSES/cvc5.txt)
; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)

(declare-const x (_ BitVec 4))
(assert (not (= x ((_ repeat 1) x))))
(set-info :status unsat)
(check-sat)
(exit)
