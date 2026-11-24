; Hand-written for VIK (this repository's license), issue 189's script: two store chains over `A` and over
; `B`, which the problem equates. Each array took a default of its own, and the two sides were apart at every
; index other than `I` and `J`: the model failed its check (2026-11-23). Arrays that stores connect take one
; default now.
; EXPECT: sat
; EXPECT: (((let ((?v_0 (store B I (select A I))) (?v_1 (store A I (select B I)))) (= (store ?v_1 I (select ?v_0 J)) (store ?v_0 J (select ?v_1 J)))) true))
(set-logic QF_AX)
(set-option :produce-models true)
(declare-sort Index 0)
(declare-sort Element 0)
(declare-fun A () (Array Index Element))
(declare-fun B () (Array Index Element))
(declare-fun I () Index)
(declare-fun J () Index)
(assert (let ((?v_0 (store B I (select A I))) (?v_1 (store A I (select B I)))) (= (store ?v_1 I (select ?v_0 J)) (store ?v_0 J (select ?v_1 J)))))
(assert (not (= A B)))
(set-info :status sat)
(check-sat)
(get-value ((let ((?v_0 (store B I (select A I))) (?v_1 (store A I (select B I)))) (= (store ?v_1 I (select ?v_0 J)) (store ?v_0 J (select ?v_1 J))))))
