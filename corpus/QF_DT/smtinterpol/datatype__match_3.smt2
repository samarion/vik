; From smtinterpol: datatype/match_3.smt2 (LGPL-3.0, LICENSES/smtinterpol.txt)
(set-info :smt-lib-version 2.6)
(set-logic QF_DT)

(set-info :category "crafted")
(set-info :status sat)


(declare-datatypes ( (List 0) (Nat 0) ) (
 ( (nil) (cons (car Nat) (cdr List) ))
 ( (zero) (succ (pred Nat)) )
))

(declare-const u List)

(assert (match u ((nil false) ((cons x y) true))))
(assert (= (car u) zero))

(check-sat)
