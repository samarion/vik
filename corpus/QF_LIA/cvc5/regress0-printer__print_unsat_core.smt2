; From cvc5: regress0/printer/print_unsat_core.smt2 (modified BSD, LICENSES/cvc5.txt)
; COMMAND-LINE: --produce-unsat-cores -o unsat-core-benchmark
; logic: QF_LIA, the smallest the script fits, for ALL (prune logic)
; EXPECT: unsat
; EXPECT: (x20)
(set-logic QF_LIA)
(set-option :produce-unsat-cores true)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (! (and (> x 2) (< x 0)) :named x20))
(assert (! (< y 0) :named y0))
(set-info :status unsat)
(check-sat)
(get-unsat-core)
