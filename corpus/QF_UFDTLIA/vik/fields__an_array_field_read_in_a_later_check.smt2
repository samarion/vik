; Hand-written for VIK (this repository's license): an array field read through its selector in a later
; check-sat than the one that met the constructor (issues 133 and 134 together). The pair of the field
; and the constructor's array is made in a round of the passes that emits nothing else: the loop of the
; passes has to go on for the two reads to meet, and VIK answered sat to the second check.
(set-logic ALL)
(declare-datatype D ((C (arr (Array Int Int)))))
(declare-const a (Array Int Int))
(declare-const x D)
(assert (= x (C a)))
(set-info :status sat)
(check-sat)
(assert (< (select (arr x) 0) (select a 0)))
(set-info :status unsat)
(check-sat)
