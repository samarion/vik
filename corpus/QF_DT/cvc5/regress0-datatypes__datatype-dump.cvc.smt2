; From cvc5: regress0/datatypes/datatype-dump.cvc.smt2 (modified BSD, LICENSES/cvc5.txt)
; COMMAND-LINE: -o raw-benchmark
; EXPECT: (set-logic ALL)
; EXPECT: (declare-datatypes ((nat 0)) (((succ (pred nat)) (zero))))
; EXPECT: (declare-fun x () nat)
; EXPECT: (check-sat-assuming ( (not (and (not ((_ is succ) x)) (not ((_ is zero) x)))) ))
; EXPECT: sat
; logic: QF_DT, the smallest the script fits, for ALL (prune logic)
(set-logic QF_DT)
(declare-datatypes ((nat 0)) (((succ (pred nat)) (zero))))
(declare-fun x () nat)
(set-info :status sat)
(check-sat-assuming ( (not (and (not ((_ is succ) x)) (not ((_ is zero) x)))) ))
