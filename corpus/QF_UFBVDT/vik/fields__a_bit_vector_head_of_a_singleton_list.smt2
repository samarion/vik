; Hand-written for VIK (this repository's license): a list of one bit-vector of one bit, apart from both such
; lists. The list is infinite, and its head, which the tester's expansion invents, had no range (issue 126,
; 2026-11-19).
(set-logic QF_UFBVDT)
(declare-datatypes ((L 0)) (((nil) (cons (hd (_ BitVec 1)) (tl L)))))
(declare-const l L)
(assert ((_ is cons) l))
(assert ((_ is nil) (tl l)))
(assert (distinct l (cons #b0 nil)))
(assert (distinct l (cons #b1 nil)))
(set-info :status unsat)
(check-sat)
