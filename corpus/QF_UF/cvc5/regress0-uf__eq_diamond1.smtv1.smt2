; From cvc5: regress0/uf/eq_diamond1.smtv1.smt2 (modified BSD, LICENSES/cvc5.txt)
(set-option :incremental false)
(set-info :source "Generating minimum transitivity constraints in P-time for deciding Equality Logic,
Ofer Strichman and Mirron Rozanov,
SMT Workshop 2005.

Translator: Leonardo de Moura.")
(set-info :status unsat)
(set-info :category "crafted")
(set-info :difficulty "0")
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun x0 () U)
(declare-fun y0 () U)
(declare-fun z0 () U)
(check-sat-assuming ( (not (= x0 x0)) ))
