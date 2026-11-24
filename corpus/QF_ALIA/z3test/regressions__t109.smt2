; From z3test: t109.smt2 (MIT, LICENSES/z3test.txt)

; Copyright (c) 2015 Microsoft Corporation

(set-option :produce-models true)

(declare-const mySet (Array Int Bool))

(assert (let ((empty ((as const (Array Int Bool)) false)))
        (let ((fortytwo (store empty 42 true)))
        (let ((fortythree (store fortytwo 43 true)))
          (= mySet ((_ map or) fortytwo fortythree))))))
(set-info :status sat)
(check-sat)
(eval (select mySet 43))
(eval (select mySet 42))
(eval (select mySet 44))