; From cvc5: regress0/bv/ubv-to-int-range.smt2 (modified BSD, LICENSES/cvc5.txt)
; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)
(declare-fun t () Int)
(declare-fun x () (_ BitVec 32))
(declare-fun y () (_ BitVec 32))
; this is solved based on the range constraints for the ubv_to_int terms,
; without having to reduce them
(assert (or (= t (ubv_to_int x)) (= t (ubv_to_int y))))
(assert (< t 0))
(set-info :status unsat)
(check-sat)
