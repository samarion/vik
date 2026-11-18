; From cvc5: regress0/cvc3.userdoc.01.cvc.smt2 (modified BSD, LICENSES/cvc5.txt)
; COMMAND-LINE: --incremental
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
; logic: QF_UF, the smallest the script fits, for ALL (prune logic)
(set-logic QF_UF)
(set-info :status unsat)
(check-sat-assuming ( (not (= #b0000111101010000 #b0000111101010000)) ))
(set-info :status unsat)
(check-sat-assuming ( (not (= (concat #b01 #b0) #b010)) ))
(set-info :status unsat)
(check-sat-assuming ( (not (= ((_ extract 3 1) #b0011) #b001)) ))
(set-info :status unsat)
(check-sat-assuming ( (not (= (concat #b0011 #b000) #b0011000)) ))
(set-info :status unsat)
(check-sat-assuming ( (not (= (concat #b000 ((_ extract 3 3) #b1000)) #b0001)) ))
(set-info :status unsat)
(check-sat-assuming ( (not (= ((_ sign_extend 2) #b100) #b11100)) ))
(set-info :status unsat)
(check-sat-assuming ( (not (= ((_ zero_extend 3) #b1) #b0001)) ))
(set-info :status unsat)
(check-sat-assuming ( (not (= ((_ repeat 3) #b10) #b101010)) ))
(set-info :status unsat)
(check-sat-assuming ( (not (= ((_ rotate_left 1) #b101) #b011)) ))
(set-info :status unsat)
(check-sat-assuming ( (not (= ((_ rotate_right 1) #b101) #b110)) ))
