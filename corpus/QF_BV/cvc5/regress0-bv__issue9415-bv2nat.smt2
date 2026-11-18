; From cvc5: regress0/bv/issue9415-bv2nat.smt2 (modified BSD, LICENSES/cvc5.txt)
(set-logic AUFBVFPDTNIRA)
(set-info :smt-lib-version 2.6)
(set-info :status unsat)

(declare-const bv (_ BitVec 32))
(assert (not (<= 0 (ubv_to_int bv))))

(check-sat)
