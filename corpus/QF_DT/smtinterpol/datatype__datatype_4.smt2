; From smtinterpol: datatype/datatype_4.smt2 (LGPL-3.0, LICENSES/smtinterpol.txt)
(set-info :smt-lib-version 2.6)
(set-logic QF_DT)

(set-info :category "crafted")
(set-info :status unsat)


(declare-datatypes ( (List 0) (Nat 0) ) (
 ( (nil) (cons (car Nat) (cdr List) ))
 ( (zero) (succ (pred Nat)) )
))

(declare-const u List)

(assert (and (not ((_ is nil) u)) (not ((_ is cons) u))))

(check-sat)
(exit)
