import Vik.Lower.Ops

/-!
# Lowered nodes take the values of their surface nodes

`expect_sound`: the shape `expect` gives a surface node describes, in the
lowered model, the value of the node; so with `fits_sound`, each lowered node
of the trace takes the value of its surface node (`corr`).
-/

set_option linter.unusedSectionVars false

namespace Vik.Lower

open Lean.Grind Vik.Real Vik.Low Vik.Surf

variable {R U : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R]
  [OrderedRing R] [IsCharP R 0]

attribute [local instance low] Lean.Grind.Ring.intCast

section
variable {SP : SProblem} {P : Problem} {tr : Trace} {Ms : Surf.Model R U}
  (hM : Ms.Sound SP.sig) (hw : Surf.wellFormed SP.nodes = true) (ht : Surf.typed SP.sig SP.nodes SP.sortOf = true)

set_option quotPrecheck false in
local notation "ρ" => Low.val (lowModel SP P tr Ms).toInterp P.nodes
local notation "vs" => Surf.val Ms.toInterp SP.nodes
set_option quotPrecheck false in
local notation "MI" => (lowModel SP P tr Ms).toInterp

include hM hw ht

theorem expect_sound (hwP : Low.wellFormed P.nodes = true) {i : Nat} {n : SNode} {s : Shape}
    (hn : SP.nodes[i]? = some n) (h : expect SP P tr i = some s)
    (ih : ∀ c < i, ρ (tr.at c) = enc (vs c)) :
    s.ev MI ρ = enc (vs i) := by
  have hi := lt_of_get hn
  have hc := children_lt hw hn
  have hv := Surf.val_node (I := Ms.toInterp) hw hn
  have hty := typed_at hM hw ht hn
  have ihc : ∀ c ∈ n.children, ρ (tr.at c) = enc (vs c) := fun c m => ih c (hc c m)
  have lenc : ∀ c ∈ n.children, c < SP.nodes.length := fun c m => by have := hc c m; omega
  have leafs : ∀ as : List Nat, (∀ a ∈ as, a ∈ n.children) →
      as.map (fun a => (leaf SP tr a).ev MI ρ) = as.map (fun a => enc (vs a)) :=
    fun as hs => List.map_congr_left (fun a m => leaf_ev hM hw ht (lenc a (hs a m)) (ihc a (hs a m)))
  have forms : ∀ as : List Nat, (∀ a ∈ as, a ∈ n.children) →
      as.map (fun a => (form tr a).ev MI ρ) = as.map (fun a => Val.bool (vs a).truth) :=
    fun as hs => List.map_congr_left (fun a m => form_ev (ihc a (hs a m)))
  cases n with
  | const k =>
    simp only [Tab.at_eq, expect, hn] at h
    split at h
    · rename_i hk; cases h
      rw [hv]; simp only [Surf.evalNode, Shape.ev]
      exact const_base SP P tr Ms hk
    · cases h
  | app f args =>
    simp only [Tab.at_eq, expect, hn, Option.some.injEq] at h; subst h
    rw [hv]; simp only [Surf.evalNode, surf_get_values, Shape.ev, Shape.evs_eq, List.map_map]
    rw [ihc f (by simp [SNode.children])]
    have := leafs args (fun a m => by simp [SNode.children, m])
    simp only [Function.comp_def]
    rw [this, show args.map (fun a => enc (vs a)) = (args.map (Low.get (Surf.values Ms.toInterp SP.nodes))).map enc
      from by rw [List.map_map]; rfl]
    exact app_enc_enc SP P tr Ms _ _
  | num v =>
    simp only [Tab.at_eq, expect, hn, Option.some.injEq] at h; subst h
    rw [hv]; simp only [Surf.evalNode, Shape.ev, Lia.eval, enc_num]
    congr 1; grind
  | tt =>
    simp only [Tab.at_eq, expect, hn, Option.some.injEq] at h; subst h
    rw [hv]; rfl
  | ff =>
    simp only [Tab.at_eq, expect, hn, Option.some.injEq] at h; subst h
    rw [hv]; rfl
  | not a =>
    simp only [Tab.at_eq, expect, hn, Option.some.injEq] at h; subst h
    rw [hv]; simp only [Surf.evalNode, surf_get_values, Shape.ev, form_ev (ihc a (by simp [SNode.children])),
      truth_bool, enc_bool]
  | and as =>
    simp only [Tab.at_eq, expect, hn, Option.some.injEq] at h; subst h
    rw [hv]; simp only [Surf.evalNode, surf_get_values, Shape.ev, Shape.allTrue_eq, enc_bool]
    congr 1
    rw [all_as_map, List.map_map, all_as_map as]
    have := forms as (fun a m => by simp [SNode.children, m])
    have := congrArg (List.map Val.truth) this
    simp only [List.map_map, Function.comp_def, truth_bool] at this
    simp only [Function.comp_def]
    rw [this]
  | or as =>
    simp only [Tab.at_eq, expect, hn, Option.some.injEq] at h; subst h
    rw [hv]; simp only [Surf.evalNode, surf_get_values, Shape.ev, Shape.anyTrue_eq, enc_bool]
    congr 1
    rw [any_as_map, List.map_map, any_as_map as]
    have := forms as (fun a m => by simp [SNode.children, m])
    have := congrArg (List.map Val.truth) this
    simp only [List.map_map, Function.comp_def, truth_bool] at this
    simp only [Function.comp_def]
    rw [this]
  | select a x =>
    simp only [Tab.at_eq, expect, hn, Option.some.injEq] at h; subst h
    rw [hv]; simp only [Surf.evalNode, surf_get_values, Shape.ev, Shape.evs]
    rw [ihc a (by simp [SNode.children]), leaf_ev hM hw ht (lenc x (by simp [SNode.children]))
      (ihc x (by simp [SNode.children])), ← List.map_singleton (f := enc)]
    exact app_enc_enc SP P tr Ms _ _
  | store a x v =>
    simp only [Tab.at_eq, expect, hn] at h
    split at h
    · rename_i g _ _
      split at h
      · rename_i k _
        split at h
        · rename_i hst
          cases h
          simp only [Tab.at_eq, Trace.storeOf, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hst
          rw [hv]; simp only [Surf.evalNode, surf_get_values, Shape.ev, Shape.evs]
          rw [const_store SP P tr Ms hst.1 hst.2,
            leaf_ev hM hw ht (lenc a (by simp [SNode.children])) (ihc a (by simp [SNode.children])),
            leaf_ev hM hw ht (lenc x (by simp [SNode.children])) (ihc x (by simp [SNode.children])),
            leaf_ev hM hw ht (lenc v (by simp [SNode.children])) (ihc v (by simp [SNode.children])),
            app_store]
        · cases h
      · cases h
    · cases h
  | implies as =>
    simp only [Tab.at_eq, expect, hn] at h
    rw [hv]; simp only [Surf.evalNode, surf_get_values, enc_bool]
    apply impliesS_ev _ _ _ (as.map fun a => (vs a).truth) _ h
    rw [List.map_map, List.map_map]
    exact forms as (fun a m => by simp [SNode.children, m])
  | xor as =>
    simp only [Tab.at_eq, expect, hn] at h
    rw [hv]; simp only [Surf.evalNode, surf_get_values, enc_bool]
    apply xorS_ev _ _ _ (as.map fun a => (vs a).truth) _ h
    rw [List.map_map, List.map_map]
    exact forms as (fun a m => by simp [SNode.children, m])
  | iff as =>
    simp only [Tab.at_eq, expect, hn, Option.some.injEq] at h; subst h
    obtain ⟨b, hb, hr⟩ := chain_ev MI ρ as (fun x y => .iff (form tr x) (form tr y))
      (fun x y => (vs x).truth = (vs y).truth) (fun x mx y my => by
        refine ⟨_, rfl, ?_⟩
        simp only [form_ev (ihc x (by simp [SNode.children, mx])),
          form_ev (ihc y (by simp [SNode.children, my])), truth_bool, beq_iff_eq])
    rw [hb, hv]; simp only [Surf.evalNode, surf_get_values, enc_bool]
    congr 1
    apply bool_eq_decide
    rw [hr, chainP_map]
  | ite c a b =>
    simp only [Tab.at_eq, expect, hn] at h
    split at h
    · rename_i hb
      simp only [Option.some.injEq] at h; subst h
      simp only [Tab.at_eq, Tab.at_eq, Surf.nodeTyped, Bool.and_eq_true, beq_iff_eq] at hty
      obtain ⟨⟨_, hsa⟩, hsb⟩ := hty
      have ba : SP.isBool a = true := by simp only [SProblem.isBool, SProblem.sort_eq] at hb ⊢; rw [hsa]; exact hb
      have bb : SP.isBool b = true := by simp only [SProblem.isBool, SProblem.sort_eq] at hb ⊢; rw [hsb]; exact hb
      obtain ⟨xa, hxa⟩ := v_bool hM hw ht (lenc a (by simp [SNode.children])) ba
      obtain ⟨xb, hxb⟩ := v_bool hM hw ht (lenc b (by simp [SNode.children])) bb
      rw [hv]; simp only [Surf.evalNode, surf_get_values, Shape.ev]
      rw [form_ev (ihc c (by simp [SNode.children])), form_ev (ihc a (by simp [SNode.children])),
        form_ev (ihc b (by simp [SNode.children])), hxa, hxb, truth_bool]
      split <;> simp [truth_bool]
    · split at h
      · rename_i k hk
        split at h
        · rename_i hite
          simp only [Option.some.injEq] at h; subst h
          simp only [Tab.at_eq, Trace.iteOf, Bool.and_eq_true, decide_eq_true_eq] at hite
          obtain ⟨hk', hm⟩ := hite
          split at hm
          · rename_i i' c0 a0 b0 hmi hni
            simp only [hn, Option.some.injEq, SNode.ite.injEq] at hni
            obtain ⟨rfl, rfl, rfl⟩ := hni
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
            obtain ⟨hle, hm⟩ := hm
            split at hm
            · rename_i c' a' b' hni'
              simp only [Bool.and_eq_true, beq_iff_eq] at hm
              obtain ⟨⟨e1, e2⟩, e3⟩ := hm
              have hc' := children_lt hw hni'
              have same : ∀ x y, x ∈ (SNode.ite c' a' b').children → y ∈ (SNode.ite c a b).children →
                  tr.at x = tr.at y → vs x = vs y := by
                intro x y mx my e
                apply enc_inj
                rw [← ih x (by have := hc' x mx; omega), ← ihc y my, e]
              have ec := same c' c (by simp [SNode.children]) (by simp [SNode.children]) e1
              have ea := same a' a (by simp [SNode.children]) (by simp [SNode.children]) e2
              have eb := same b' b (by simp [SNode.children]) (by simp [SNode.children]) e3
              simp only [Shape.ev]
              rw [const_ite SP P tr Ms hk' hmi, Surf.val_node hw hni', hv]
              simp only [Surf.evalNode, surf_get_values, ec, ea, eb]
            · cases hm
          · cases hm
        · cases h
      · cases h
  | add as =>
    simp only [Tab.at_eq, expect, hn, Option.some.injEq] at h; subst h
    rw [hv]; simp only [Surf.evalNode, Shape.ev, enc_num]
    congr 1
    rw [sumForms_eval _ (linOf P tr) (fun a => (vs a).toR) as
      (fun a m => lin_ev hwP (ihc a (by simp [SNode.children, m]))), sumR_eq, List.map_map]
    rfl
  | sub as =>
    simp only [Tab.at_eq, expect, hn] at h
    cases as with
    | nil =>
      simp only [Option.some.injEq] at h; subst h
      rw [hv]; simp only [Surf.evalNode, Shape.ev, Lia.eval, enc_num]
      congr 1; grind
    | cons a rest =>
      simp only [Option.some.injEq] at h; subst h
      rw [hv]; simp only [Surf.evalNode, surf_get_values, Shape.ev, enc_num]
      congr 1
      have hr := sumForms_eval (fun u => (ρ u).toR) (linOf P tr) (fun a => (vs a).toR) rest
        (fun b m => lin_ev hwP (ihc b (by simp [SNode.children, m])))
      have ha := lin_ev hwP (ihc a (by simp [SNode.children]))
      rw [eval_append, Lia.eval_neg, Ring.intCast_sub, sumR_eq, List.map_map, ← ha]
      have : ((rest.map (Low.get (Surf.values Ms.toInterp SP.nodes))).map Val.toR) = rest.map (fun a => (vs a).toR) := by
        rw [List.map_map]; rfl
      simp only [List.map_map] at this hr ⊢
      rw [this, ← hr]
      grind
  | neg a =>
    simp only [Tab.at_eq, expect, hn, Option.some.injEq] at h; subst h
    rw [hv]; simp only [Surf.evalNode, surf_get_values, Shape.ev, enc_num]
    congr 1
    have ha := lin_ev hwP (ihc a (by simp [SNode.children]))
    rw [Lia.eval_neg, Ring.intCast_neg, ← ha]
    grind
  | mul as =>
    simp only [Tab.at_eq, expect, hn, Option.map_eq_some_iff] at h
    obtain ⟨p, hp, rfl⟩ := h
    rw [hv]; simp only [Surf.evalNode, Shape.ev, enc_num]
    congr 1
    rw [mulForms_eval _ (linOf P tr) (fun a => (vs a).toR) as
      (fun a m => lin_ev hwP (ihc a (by simp [SNode.children, m]))) p hp, prodR_eq, List.map_map]
    rfl
  | eq as =>
    simp only [Tab.at_eq, expect, hn] at h
    cases as with
    | nil => cases h
    | cons a rest =>
      simp only at h
      split at h
      · cases h
      · rename_i hnb
        simp only [Option.some.injEq] at h; subst h
        simp only [Tab.at_eq, Tab.at_eq, Surf.nodeTyped, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hty
        have sorts : ∀ x ∈ a :: rest, SP.sort x = SP.sort a := by
          intro x m; simp only [List.mem_cons] at m
          rcases m with rfl | m
          · rfl
          · exact hty.2 x m
        have mem : ∀ x ∈ a :: rest, x ∈ (SNode.eq (a :: rest)).children := fun x m => m
        obtain ⟨b, hb, hr⟩ := chain_ev MI ρ (a :: rest)
          (fun x y => eqS (SP.isArith a) (.same (tr.at x)) (.same (tr.at y))) (fun x y => vs x = vs y)
          (fun x mx y my => by
            have ex := ihc x (mem x mx)
            have ey := ihc y (mem y my)
            unfold eqS
            split
            · rename_i hnum
              have nx : SP.isArith x = true := by
                unfold SProblem.isArith SProblem.isNum SProblem.isBv SProblem.width at hnum ⊢
                rw [sorts x mx]; exact hnum
              have ny : SP.isArith y = true := by
                unfold SProblem.isArith SProblem.isNum SProblem.isBv SProblem.width at hnum ⊢
                rw [sorts y my]; exact hnum
              obtain ⟨rx, hrx⟩ := v_arith hM hw ht (lenc x (mem x mx)) nx
              obtain ⟨ry, hry⟩ := v_arith hM hw ht (lenc y (mem y my)) ny
              refine ⟨_, rfl, ?_⟩
              simp only [Shape.allTrue, Shape.ev, ex, ey, toR_enc, hrx, hry, toR_num, truth_bool, Bool.and_true,
                Bool.and_eq_true, decide_eq_true_eq, Val.num.injEq]
              constructor
              · rintro ⟨h1, h2⟩; exact Std.le_antisymm h1 h2
              · rintro rfl; exact ⟨Std.le_refl _, Std.le_refl _⟩
            · refine ⟨_, rfl, ?_⟩
              simp only [Shape.ev, ex, ey, decide_eq_true_eq]
              exact ⟨enc_inj, fun e => by rw [e]⟩)
        rw [hb, hv]; simp only [Surf.evalNode, enc_bool]
        congr 1
        apply bool_eq_decide
        exact hr.trans (chainP_map _ _ _).symm
  | distinct as =>
    simp only [Tab.at_eq, expect, hn] at h
    cases as with
    | nil => cases h
    | cons a rest =>
      simp only at h
      simp only [Tab.at_eq, Tab.at_eq, Surf.nodeTyped, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hty
      have sorts : ∀ x ∈ a :: rest, SP.sort x = SP.sort a := by
        intro x m; simp only [List.mem_cons] at m
        rcases m with rfl | m
        · rfl
        · exact hty.2 x m
      have mem : ∀ x ∈ a :: rest, x ∈ (SNode.distinct (a :: rest)).children := fun x m => m
      have finish : ∀ (mk : Nat → Nat → Shape),
          (∀ x ∈ a :: rest, ∀ y ∈ a :: rest, ∃ b, (mk x y).ev MI ρ = .bool b ∧ (b = true ↔ vs x ≠ vs y)) →
          (Shape.and ((allPairs (a :: rest)).map fun p => mk p.1 p.2)).ev MI ρ = enc (vs i) := by
        intro mk hmk
        obtain ⟨b, hb, hr⟩ := pairs_ev MI ρ (a :: rest) mk (fun x y => vs x ≠ vs y) hmk
        rw [hb, hv]; simp only [Surf.evalNode, enc_bool]
        congr 1
        apply bool_eq_decide
        exact hr.trans (pairwiseP_map _ _ _).symm
      split at h
      · cases h
      · split at h
        · rename_i hint
          simp only [Option.some.injEq] at h; subst h
          apply finish (fun x y => Shape.or [ltInt P tr x y, ltInt P tr y x])
          intro x mx y my
          have ix : SP.isIntLike x = true := by
            unfold SProblem.isIntLike SProblem.isInt SProblem.isBv SProblem.width at hint ⊢
            rw [sorts x mx]; exact hint
          have iy : SP.isIntLike y = true := by
            unfold SProblem.isIntLike SProblem.isInt SProblem.isBv SProblem.width at hint ⊢
            rw [sorts y my]; exact hint
          obtain ⟨kx, hkx⟩ := v_intLike hM hw ht (lenc x (mem x mx)) ix
          obtain ⟨ky, hky⟩ := v_intLike hM hw ht (lenc y (mem y my)) iy
          refine ⟨_, rfl, ?_⟩
          simp only [Shape.anyTrue, ltInt_ev hwP (ihc x (mem x mx)) (ihc y (mem y my)),
            ltInt_ev hwP (ihc y (mem y my)) (ihc x (mem x mx)), truth_bool, Bool.or_false, Bool.or_eq_true,
            decide_eq_true_eq, hkx, hky, toR_num, cast_succ_le_iff, ne_eq, num_int_eq_iff]
          omega
        · split at h
          · rename_i hnum
            simp only [Option.some.injEq] at h; subst h
            apply finish (fun x y => Shape.or [.lt (.same (tr.at x)) (.same (tr.at y)), .lt (.same (tr.at y)) (.same (tr.at x))])
            intro x mx y my
            have nx : SP.isNum x = true := by unfold SProblem.isNum at hnum ⊢; rw [sorts x mx]; exact hnum
            have ny : SP.isNum y = true := by unfold SProblem.isNum at hnum ⊢; rw [sorts y my]; exact hnum
            obtain ⟨rx, hrx⟩ := v_num hM hw ht (lenc x (mem x mx)) nx
            obtain ⟨ry, hry⟩ := v_num hM hw ht (lenc y (mem y my)) ny
            refine ⟨_, rfl, ?_⟩
            simp only [Shape.ev, Shape.anyTrue, ihc x (mem x mx), ihc y (mem y my), toR_enc,
              truth_bool, Bool.or_false, Bool.or_eq_true, decide_eq_true_eq, hrx, hry, toR_num, ne_eq, Val.num.injEq]
            exact (ne_iff_lt_or_gt (R := R)).symm
          · simp only [Option.some.injEq] at h; subst h
            apply finish (fun x y => Shape.not (.eq (.same (tr.at x)) (.same (tr.at y))))
            intro x mx y my
            refine ⟨_, rfl, ?_⟩
            simp only [Shape.ev, ihc x (mem x mx), ihc y (mem y my), truth_bool, Bool.not_eq_true',
              decide_eq_false_iff_not, ne_eq]
            exact ⟨fun h1 e => h1 (by rw [e]), fun h1 e => h1 (enc_inj e)⟩
  | bvlit w v => exact bvlit_sound hM hw ht hn h
  | bvun op w a => exact bvun_sound hM hw ht hwP hn h ih
  | concat wa wb a b => exact concat_sound hM hw ht hwP hn h ih
  | bv2int sg w a => exact bv2int_sound hM hw ht hn h ih
  | bvcmp op w a b => exact bvcmp_sound hM hw ht hwP hn h ih
  | bvbin op w a b => simp only [Tab.at_eq, expect, hn] at h; cases h
  | int2bv w a => simp only [Tab.at_eq, expect, hn] at h; cases h
  | rat _ _ | div _ | toReal _ | toInt _ | isInt _ | letIn _ _ | bound _ => simp only [Tab.at_eq, expect, hn] at h; cases h
  | le as =>
    simp only [Tab.at_eq, expect, hn, Option.some.injEq] at h; subst h
    obtain ⟨b, hb, hr⟩ := chain_ev MI ρ as (fun x y => .le (.same (tr.at x)) (.same (tr.at y)))
      (fun x y => (vs x).toR ≤ (vs y).toR) (fun x mx y my =>
        ⟨_, le_ev (ihc x mx) (ihc y my), by simp only [decide_eq_true_eq]⟩)
    rw [hb, hv]; simp only [Surf.evalNode, surf_get_values, enc_bool]
    congr 1
    apply bool_eq_decide
    exact hr.trans (chainP_map _ _ _).symm
  | ge as =>
    simp only [Tab.at_eq, expect, hn, Option.some.injEq] at h; subst h
    obtain ⟨b, hb, hr⟩ := chain_ev MI ρ as (fun x y => .le (.same (tr.at y)) (.same (tr.at x)))
      (fun x y => (vs y).toR ≤ (vs x).toR) (fun x mx y my =>
        ⟨_, le_ev (ihc y my) (ihc x mx), by simp only [decide_eq_true_eq]⟩)
    rw [hb, hv]; simp only [Surf.evalNode, surf_get_values, enc_bool]
    congr 1
    apply bool_eq_decide
    exact hr.trans (chainP_map (fun x y => y ≤ x) (fun a => (vs a).toR) as).symm
  | lt as =>
    simp only [Tab.at_eq, expect, hn] at h
    split at h
    · rename_i hint
      simp only [Option.some.injEq] at h; subst h
      simp only [List.all_eq_true] at hint
      obtain ⟨b, hb, hr⟩ := chain_ev MI ρ as (fun x y => ltInt P tr x y)
        (fun x y => (vs x).toR < (vs y).toR) (fun x mx y my => by
          obtain ⟨kx, hkx⟩ := v_int hM hw ht (lenc x mx) (hint x mx)
          obtain ⟨ky, hky⟩ := v_int hM hw ht (lenc y my) (hint y my)
          refine ⟨_, ltInt_ev hwP (ihc x mx) (ihc y my), ?_⟩
          simp only [decide_eq_true_eq, hkx, hky, toR_num, cast_succ_le_iff, cast_lt_iff])
      rw [hb, hv]; simp only [Surf.evalNode, surf_get_values, enc_bool]
      congr 1
      apply bool_eq_decide
      exact hr.trans (chainP_map _ _ _).symm
    · simp only [Option.some.injEq] at h; subst h
      obtain ⟨b, hb, hr⟩ := chain_ev MI ρ as (fun x y => .lt (.same (tr.at x)) (.same (tr.at y)))
        (fun x y => (vs x).toR < (vs y).toR) (fun x mx y my =>
          ⟨_, lt_ev (ihc x mx) (ihc y my), by simp only [decide_eq_true_eq]⟩)
      rw [hb, hv]; simp only [Surf.evalNode, surf_get_values, enc_bool]
      congr 1
      apply bool_eq_decide
      exact hr.trans (chainP_map _ _ _).symm
  | gt as =>
    simp only [Tab.at_eq, expect, hn] at h
    split at h
    · rename_i hint
      simp only [Option.some.injEq] at h; subst h
      simp only [List.all_eq_true] at hint
      obtain ⟨b, hb, hr⟩ := chain_ev MI ρ as (fun x y => ltInt P tr y x)
        (fun x y => (vs y).toR < (vs x).toR) (fun x mx y my => by
          obtain ⟨kx, hkx⟩ := v_int hM hw ht (lenc x mx) (hint x mx)
          obtain ⟨ky, hky⟩ := v_int hM hw ht (lenc y my) (hint y my)
          refine ⟨_, ltInt_ev hwP (ihc y my) (ihc x mx), ?_⟩
          simp only [decide_eq_true_eq, hkx, hky, toR_num, cast_succ_le_iff, cast_lt_iff])
      rw [hb, hv]; simp only [Surf.evalNode, surf_get_values, enc_bool]
      congr 1
      apply bool_eq_decide
      exact hr.trans (chainP_map (fun x y => y < x) (fun a => (vs a).toR) as).symm
    · simp only [Option.some.injEq] at h; subst h
      obtain ⟨b, hb, hr⟩ := chain_ev MI ρ as (fun x y => .lt (.same (tr.at y)) (.same (tr.at x)))
        (fun x y => (vs y).toR < (vs x).toR) (fun x mx y my =>
          ⟨_, lt_ev (ihc y my) (ihc x mx), by simp only [decide_eq_true_eq]⟩)
      rw [hb, hv]; simp only [Surf.evalNode, surf_get_values, enc_bool]
      congr 1
      apply bool_eq_decide
      exact hr.trans (chainP_map (fun x y => y < x) (fun a => (vs a).toR) as).symm

end

/-! ## The checks, and the theorem -/

/-- What `Trace.check` says. -/
structure CheckSpec (SP : SProblem) (P : Problem) (tr : Trace) (A : Answer) : Prop where
  wf : Surf.wellFormed SP.nodes = true
  typed : Surf.typed SP.sig SP.nodes SP.sortOf = true
  sorts : SortsSpec SP
  sig : SigSpec SP P tr
  nodes : ∀ i < SP.nodes.length, tr.at i < P.nodes.length ∧
    ((∃ s, expect SP P tr i = some s ∧ fits P.sig P.nodes P.sortOf (tr.at i) s = true) ∨ tr.bvOk SP P i = true)
  inputs : ∀ f ∈ P.inputs, f < P.nodes.length ∧ ∃ w, tr.inputOk SP P f w = true
  assumed : ∀ s ∈ A.assumed, ∀ fs, A.levels.lookup s = some fs →
    ∀ f ∈ fs, f < P.nodes.length ∧ ∃ w, tr.inputOk SP P f w = true

/-- A check over two lists of the same length covers each element of the first. -/
theorem zip_all_left {α β : Type} {xs : List α} {ys : List β} {g : α × β → Bool}
    (hl : xs.length = ys.length) (h : ∀ p ∈ xs.zip ys, g p = true) : ∀ x ∈ xs, ∃ y, g (x, y) = true := by
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
  have hj' : j < ys.length := by omega
  refine ⟨ys[j], h _ ?_⟩
  have e : (xs.zip ys)[j]'(by simp; omega) = (xs[j], ys[j]) := List.getElem_zip
  rw [← e]
  exact List.getElem_mem _

theorem check_spec {SP : SProblem} {P : Problem} {tr : Trace} {A : Answer} (h : tr.check SP P A = true) :
    CheckSpec SP P tr A := by
  simp only [Trace.check, Trace.nodeOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hw, ht⟩, hs⟩, hg⟩, _⟩, hn⟩, hlen⟩, hi⟩, hal⟩, hlv⟩ := h
  refine ⟨hw, ht, sortsOk_spec hs, sigOk_spec hg, ?_, ?_, ?_⟩
  · intro i hi'
    have := hn i hi'
    simp only [decide_eq_true_eq] at this
    refine ⟨this.1, ?_⟩
    have h2 := this.2
    simp only [Bool.or_eq_true] at h2
    rcases h2 with h2 | h2
    · split at h2
      · rename_i s hs'; exact .inl ⟨s, hs', h2⟩
      · cases h2
    · exact .inr h2
  · intro f hf
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hf
    have hj' : j < tr.inputs.length := by omega
    have hm : (P.inputs[j], tr.inputs[j]) ∈ P.inputs.zip tr.inputs := by
      have e : (P.inputs.zip tr.inputs)[j]'(by simp; omega) = (P.inputs[j], tr.inputs[j]) := List.getElem_zip
      rw [← e]
      exact List.getElem_mem _
    have := hi _ hm
    simp only [decide_eq_true_eq] at this
    exact ⟨this.1, _, this.2⟩
  · intro s hs fs hfs f hf
    obtain ⟨ws, hw⟩ := zip_all_left hal hlv s hs
    simp only [hfs, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hw
    obtain ⟨w, hw⟩ := zip_all_left (g := fun q => decide (q.1 < P.nodes.length) && tr.inputOk SP P q.1 q.2)
      hw.1 (fun q hq => by simpa only [Tab.at_eq, Bool.and_eq_true] using hw.2 q hq) f hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hw
    exact ⟨hw.1, _, hw.2⟩

section
variable {SP : SProblem} {P : Problem} {tr : Trace} {A : Answer} {Ms : Surf.Model R U} {size : Val R U → Nat}
  (hc : CheckSpec SP P tr A) (hA : Accepted P A) (hL : SP.Laws Ms size)

set_option quotPrecheck false in
local notation "ρ" => Low.val (lowModel SP P tr Ms).toInterp P.nodes
local notation "vs" => Surf.val Ms.toInterp SP.nodes
set_option quotPrecheck false in
local notation "MI" => (lowModel SP P tr Ms).toInterp

include hc hA hL

/-- The lowered nodes of bit-vector sorts take values in their ranges: they are
    symbols and applications, whose values are surface ones. -/
theorem low_rng : ∀ j < P.nodes.length, inRange P.bvIndex (P.sortOf[j]?.getD 0) (ρ j) := by
  have hM := lowModel_sound hc.sorts hc.sig hL hc.wf hc.typed hA.wf
  have hS := hL.sound
  have hG := hc.sig
  -- by the order `mu`: the depth of the rule symbols a node depends on, then its number
  suffices hmu : ∀ M, ∀ j < P.nodes.length, tr.mu SP P j = M →
      inRange P.bvIndex (P.sortOf[j]?.getD 0) (ρ j) from fun j hj => hmu _ j hj rfl
  intro M
  induction M using Nat.strongRecOn with
  | ind M ihM =>
  intro j hj hM'
  subst hM'
  have ih : ∀ y < P.nodes.length, tr.mu SP P y < tr.mu SP P j →
      inRange P.bvIndex (P.sortOf[y]?.getD 0) (ρ y) := fun y hy hl => ihM _ hl y hy rfl
  -- the children of a node come before it
  have muc : ∀ {y : Nat} {n : Node}, P.nodes[y]? = some n → ∀ c ∈ n.children, tr.mu SP P c < tr.mu SP P y := by
    intro y n hn c hc'
    have h1 := (depth_node (rank := tr.rank SP) hA.wf hn).2 c hc'
    have h2 := Low.children_lt hA.wf hn c hc'
    have := Nat.mul_le_mul_right P.nodes.length h1
    unfold Trace.mu; omega
  intro w hlw
  rw [hG.bvIndex, lookup_bvIndex] at hlw
  -- a number in range
  by_cases hnum : ∃ c : Int, P.nodes[j]? = some (.num c) ∧ 0 ≤ c ∧ c < 2 ^ w
  · obtain ⟨c, hc, h0, h1⟩ := hnum
    rw [Low.val_num hA.wf hc]; exact ⟨c, rfl, h0, h1⟩
  -- a sum in range
  by_cases hiv : ivSub (tr.fixedAt SP P (tr.mu SP P j) 2 j) 0 (2 ^ w - 1) = true
  · obtain ⟨q, hq, h0, h1⟩ := ivSub_sound hiv
    obtain ⟨k, ek, k0, k1⟩ := fixedAt_sound (R := R) (U := U) (Ms := Ms) hA.wf hG ih 2 j q hq
    exact ⟨k, ek, by omega, by omega⟩
  generalize hs : P.sortOf[j]?.getD 0 = s at hlw
  have hsw := sortWidth_eq.mp hlw
  have hsl : s < SP.sig.sorts.length := lt_of_get hsw
  -- a surface value of sort `s` is in range
  suffices h : ∃ v, Ms.dom s v ∧ ρ j = enc v by
    obtain ⟨v, hv, e⟩ := h
    obtain ⟨x, rfl⟩ := (dom_bv_iff hS hsw).mp hv
    rw [e, ofBv_num, enc_num]
    exact ⟨_, rfl, Vik.val_nonneg x, Vik.val_lt x⟩
  have hty : ∀ {n : Node}, P.nodes[j]? = some n → Low.nodeTyped P.sig P.sortOf n s = true := by
    intro n hn; rw [← hs]; exact typed_node hA.typed hn
  obtain ⟨k, hk⟩ | ⟨f, xs, hfx⟩ | hn | hn := hG.bvNodes j hj w (by rw [hs]; exact hlw)
  rotate_left 2
  · exact absurd hn hnum
  · exact absurd hn hiv
  · have hd := hty hk
    simp only [Tab.at_eq, Tab.at_eq, Low.nodeTyped, beq_iff_eq] at hd
    rw [Low.val_const hA.wf hk]
    rcases Nat.lt_or_ge k SP.sig.decls.length with hkl | hkl
    · rw [hG.decls k hkl] at hd
      exact ⟨_, hS.const k s hd, const_base SP P tr Ms hkl⟩
    · obtain ⟨m, rfl, x, hx⟩ := mint_of hc.sorts hG hL hkl s hd
      have hm : SP.sig.decls.length + m - SP.sig.decls.length = m := by omega
      cases x with
      | ite i =>
        obtain ⟨⟨c, a, b, hi⟩, _, hd'⟩ := hG.ite m i hx
        rw [hd] at hd'; cases hd'
        exact ⟨_, dom_at hS hc.wf hc.typed (lt_of_get hi), const_ite SP P tr Ms hkl (by rw [hm]; exact hx)⟩
      | store s0 =>
        obtain ⟨_, _, ds, _, hd', hle, _, _⟩ := hG.store m s0 hx
        rw [hd] at hd'; cases hd'
        omega
      | rule r j' =>
        obtain ⟨⟨s1, hd1, hs1 | ⟨w', hs1, hout⟩⟩, hargs⟩ := hG.rule m r j' hx
        · rw [hd] at hd1; cases hd1
          rw [hsw] at hs1; cases hs1
        · rw [hd] at hd1; cases hd1
          rw [hsw] at hs1; cases hs1
          rw [const_rule SP P tr Ms hA.wf hx (fun x hx' => (hargs x hx').2)]
          obtain ⟨h0, h1⟩ : 0 ≤ Rule.ival (fun x => intOf (ρ x)) (fun x => (ρ x).truth) r j' ∧
              Rule.ival (fun x => intOf (ρ x)) (fun x => (ρ x).truth) r j' < 2 ^ w := by
            rcases hout with hout | hout
            · exact Rule.bvOut_range hout (fun x => intOf (ρ x)) (fun x => (ρ x).truth)
            · -- from the intervals of its arguments, of lower depth
              obtain ⟨q, hq, q0, q1⟩ := ivSub_sound hout
              have hdj : m + 1 ≤ depthOf (depths (tr.rank SP) P.nodes) j := by
                have := (depth_node (rank := tr.rank SP) hA.wf hk).1
                simp only [Node.own, Trace.rank, Tab.at_eq, hm, hx, Nat.le_add_right, if_true] at this
                omega
              have hr : ∀ y < P.nodes.length, tr.mu SP P y < (m + 1) * P.nodes.length →
                  inRange P.bvIndex (P.sortOf[y]?.getD 0) (ρ y) := by
                intro y hy hl
                refine ih y hy ?_
                have := Nat.mul_le_mul_right P.nodes.length hdj
                unfold Trace.mu at hl ⊢; omega
              obtain ⟨a0, a1⟩ := fixedIv_sound (R := R) (U := U) (Ms := Ms) hA.wf _
                (fixedAt_sound hA.wf hG hr 2) r j' q hq
              exact ⟨by omega, by omega⟩
          refine ⟨ofBv (BitVec.ofInt w (Rule.ival (fun x => intOf (ρ x)) (fun x => (ρ x).truth) r j')),
            (dom_bv_iff hS hsw).mpr ⟨_, rfl⟩, ?_⟩
          rw [ofBv_num, Vik.val_ofInt, Int.emod_eq_of_lt h0 h1]; rfl
      | real r =>
        obtain ⟨⟨s1, hd1, hs1⟩, _⟩ := hG.real m r hx
        rw [hd] at hd1; cases hd1
        rw [hsw] at hs1; split at hs1 <;> cases hs1
      | pick i =>
        obtain ⟨hil, hd'⟩ := hG.pick m i hx
        rw [hd] at hd'; cases hd'
        exact ⟨_, dom_at hS hc.wf hc.typed hil, const_pick SP P tr Ms hkl (by rw [hm]; exact hx)⟩
      | witness s0 =>
        obtain ⟨hd1, _⟩ := hG.witness m s0 hx
        rw [hd] at hd1; cases hd1
        refine ⟨.num ((0 : Int) : R), (hS.bv s _ _ hsw).mpr ⟨0, rfl, Int.le_refl 0, Int.pow_pos (by decide)⟩, ?_⟩
        rw [const_witness SP P tr Ms hkl (by rw [hm]; exact hx)]
        simp [hsw, enc, Ring.intCast_zero]
  · have hd := hty hfx
    simp only [Tab.at_eq, Tab.at_eq, Low.nodeTyped] at hd
    split at hd
    · rename_i as r hfs
      simp only [Bool.and_eq_true, beq_iff_eq] at hd
      obtain ⟨rfl, hargs⟩ := hd
      have hfj := child_lt hA.wf hfx (j := f) (by simp [Node.children])
      have hxj : ∀ x ∈ xs, x < j := fun x m => child_lt hA.wf hfx (j := x) (by simp [Node.children, m])
      -- the nodes before `j` in the order `mu` take values of their sorts
      have dS := val_dom_sub hM hA.wf hA.typed (fun y => tr.mu SP P y < tr.mu SP P j)
        (fun y n hn hy c hc' => Nat.lt_trans (muc hn c hc') hy)
        (fun y n hn hy c hc' => ih c (Nat.lt_trans (Low.children_lt hA.wf hn c hc') (lt_of_get hn))
          (Nat.lt_trans (muc hn c hc') hy))
      have df := dS f (by omega) (muc hfx f (by simp [Node.children]))
      -- the arguments, in range
      have dxs : Forall2 (fun a x => (lowModel SP P tr Ms).dom a x ∧ inRange SP.bvIndex a x) as (xs.map ρ) := by
        rw [← hG.bvIndex]
        refine forall2_fit hM xs as hargs (fun x m => ⟨?_, ?_⟩)
        · exact dS x (by have := hxj x m; omega) (muc hfx x (by simp [Node.children, m]))
        · exact ih x (by have := hxj x m; omega) (muc hfx x (by simp [Node.children, m]))
      rw [Low.val_app hA.wf hfx]
      rcases Nat.lt_or_ge (P.sortOf[f]?.getD 0) SP.sig.sorts.length with hfl | hfl
      · obtain ⟨x, hx, ex⟩ := surf_sort_of hG hfl hfs
        cases x with
        | fn as' r' =>
          simp only [lowerSort, SortDef.fn.injEq] at ex
          obtain ⟨h1, h2⟩ := ex; subst h1; subst h2
          obtain ⟨F, hF, eF⟩ := dom_enc hc.sorts hG hL hfl hx (by intro _ e; cases e) df
          obtain ⟨ys, eys, hys⟩ := (forall2_base SP P tr Ms hS as' _ (hc.sorts.fn _ _ _ hx).1).mp dxs
          rw [eF, eys, app_enc_enc]
          exact ⟨_, hS.fn _ as' _ F ys hx hF hys, rfl⟩
        | array i e =>
          simp only [lowerSort, SortDef.fn.injEq] at ex
          obtain ⟨h1, h2⟩ := ex; subst h1; subst h2
          obtain ⟨F, hF, eF⟩ := dom_enc hc.sorts hG hL hfl hx (by intro _ e; cases e) df
          obtain ⟨ys, eys, hys⟩ := (forall2_base SP P tr Ms hS [i] _
            (by simpa using (hc.sorts.array _ _ _ hx).1)).mp dxs
          rw [eF, eys]
          match ys, hys with
          | [y], hys =>
            rw [app_enc_enc]
            exact ⟨_, hS.select _ i _ F y hx hF hys.1, rfl⟩
        | _ => simp [lowerSort] at ex
      · obtain ⟨arr, idx, el, hd, harr⟩ := hG.extra _ _ hfl hfs
        simp only [SortDef.fn.injEq] at hd
        obtain ⟨_, rfl⟩ := hd
        rw [harr] at hsw; cases hsw
    · cases hd

/-- Each lowered node of the trace takes the value of its surface node. -/
theorem corr : ∀ i < SP.nodes.length, ρ (tr.at i) = enc (vs i) := by
  have hM := lowModel_sound hc.sorts hc.sig hL hc.wf hc.typed hA.wf
  have hrngP := low_rng hc hA hL
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
  intro hi
  obtain ⟨n, hn⟩ : ∃ n, SP.nodes[i]? = some n := ⟨_, List.getElem?_eq_getElem hi⟩
  obtain ⟨hlt, ⟨s, hs, hf⟩ | hb⟩ := hc.nodes i hi
  · rw [fits_sound hM hA.wf hA.typed hrngP _ hlt s hf]
    exact expect_sound hL.sound hc.wf hc.typed hA.wf hn hs (fun c hci => ih c hci (by omega))
  · exact bvOk_sound hL.sound hc.wf hc.typed hA.wf hA.typed hc.sig hM hrngP hL.defs hn hlt hb
      (fun c hci => ih c hci (by omega)) (fun c hci => (hc.nodes c (by omega)).1)

theorem lt_of_holds {a : Nat} (h : Surf.holds Ms.toInterp SP.nodes a) : a < SP.nodes.length := by
  rcases Nat.lt_or_ge a SP.nodes.length with h' | h'
  · exact h'
  · exfalso
    unfold Surf.holds Surf.val Low.get at h
    rw [List.getElem?_eq_none (by rw [Surf.values_length]; exact h')] at h
    cases h

/-- A lowered formula with a reason that `Trace.inputOk` accepts holds when the
    surface assertions do. -/
theorem input_holds (hfloor : ∀ r : R, ∃ k : Int, IsFloor r k)
    (hin : ∀ a ∈ SP.asserts, Surf.holds Ms.toInterp SP.nodes a) {f : Nat} (hfl : f < P.nodes.length)
    {w : InputWhy} (hw : tr.inputOk SP P f w = true) : Low.holds MI P.nodes f := by
  have hM := lowModel_sound hc.sorts hc.sig hL hc.wf hc.typed hA.wf
  have hrngP := low_rng hc hA hL
  have hco := corr hc hA hL
  unfold Low.holds
  cases w with
  | assert a =>
    simp only [Trace.inputOk, Bool.and_eq_true, List.contains_iff_mem] at hw
    have ha := hin a hw.1
    have hal := lt_of_holds hc hA hL ha
    rw [fits_sound hM hA.wf hA.typed hrngP f hfl _ hw.2, form_ev (hco a hal)]
    unfold Surf.holds at ha
    rw [ha, truth_bool]
  | rule r j aux =>
    simp only [Trace.inputOk, Bool.and_eq_true] at hw
    obtain ⟨hok, hfs⟩ := hw
    split at hfs
    · rename_i fs hf
      split at hfs
      · rename_i s hs
        rw [fits_sound hM hA.wf hA.typed hrngP f hfl _ hfs]
        exact ruleFacts_hold hL.sound hc.wf hc.typed hA.wf hA.typed hc.sig hM hrngP hco
          (exactOk_spec hA.wf hA.typed hc.sig hM hrngP) hok hf s
          (List.mem_of_getElem? hs)
      · cases hfs
    · cases hfs
  | real r j =>
    simp only [Trace.inputOk, Bool.and_eq_true] at hw
    obtain ⟨hok, hfs⟩ := hw
    split at hfs
    · rename_i k hk
      split at hfs
      · rename_i s hs
        rw [fits_sound hM hA.wf hA.typed hrngP f hfl _ hfs]
        exact realFacts_hold hA.wf hc.sig hfloor hok hk s (List.mem_of_getElem? hs)
      · cases hfs
    · cases hfs
  | range i =>
    simp only [Trace.inputOk] at hw
    split at hw
    · rename_i wd hwd
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hw
      obtain ⟨hil, hfit⟩ := hw
      rw [fits_sound hM hA.wf hA.typed hrngP f hfl _ hfit]
      obtain ⟨x, hx⟩ := v_width hL.sound hc.wf hc.typed hil hwd
      have e := hco i hil
      have h0 := Vik.val_nonneg x
      have h1 := Vik.val_lt x
      have z : ∀ c : Int, (0 : R) + (c : R) = (c : R) := fun c => by grind
      have p1 : (0 : R) + ((0 : Int) : R) ≤ (ρ (tr.at i)).toR := by
        rw [e, hx, ofBv_num, enc_num, toR_num, z]; exact cast_le_iff.mpr h0
      have p2 : (ρ (tr.at i)).toR ≤ (0 : R) + ((2 ^ wd - 1 : Int) : R) := by
        rw [e, hx, ofBv_num, enc_num, toR_num, z]; exact cast_le_iff.mpr (by omega)
      classical
      simp only [Shape.ev, Shape.allTrue, Lia.eval, truth_bool, toR_num,
        _root_.decide_eq_true p1, _root_.decide_eq_true p2, Bool.and_self]
    · cases hw
  | iteThen k | iteElse k =>
    simp only [Trace.inputOk] at hw
    split at hw
    · rename_i s hs
      rw [fits_sound hM hA.wf hA.typed hrngP f hfl s hw]
      unfold iteFact at hs
      split at hs
      · cases hs
      · rename_i hk
        split at hs
        · rename_i i hm
          split at hs
          · rename_i c a b hn
            have hil := lt_of_get ((Tab.at_eq _ _).symm.trans hn)
            have hch := children_lt hc.wf ((Tab.at_eq _ _).symm.trans hn)
            have hci := hco c (by have := hch c (by simp [SNode.children]); omega)
            have hai := hco a (by have := hch a (by simp [SNode.children]); omega)
            have hbi := hco b (by have := hch b (by simp [SNode.children]); omega)
            have hk' : SP.sig.decls.length ≤ k := by omega
            have hv := Surf.val_node (I := Ms.toInterp) hc.wf ((Tab.at_eq _ _).symm.trans hn)
            simp only [Surf.evalNode, surf_get_values] at hv
            have hK : (lowModel SP P tr Ms).const k = enc (vs i) := const_ite SP P tr Ms hk' ((Tab.at_eq _ _).symm.trans hm)
            -- `k = t` holds when `k` is `t`
            have eqT : ∀ t, t ∈ (SNode.ite c a b).children → vs i = vs t → ρ (tr.at t) = enc (vs t) →
                (eqS (SP.isArith i) (.const k) (.same (tr.at t))).ev MI ρ = .bool true := by
              intro t _ e ht'
              unfold eqS
              split
              · simp only [Shape.ev, Shape.allTrue, truth_bool, Bool.and_true]
                have hK' : (lowModel SP P tr Ms).toInterp.const k = enc (vs t) := by rw [← e]; exact hK
                simp only [hK', ht', Std.le_refl, decide_true, Bool.and_self]
              · simp only [Shape.ev]
                have hK' : (lowModel SP P tr Ms).toInterp.const k = enc (vs t) := by rw [← e]; exact hK
                simp only [hK', ht', decide_true]
            split at hs
            · simp only [Option.some.injEq] at hs; subst hs
              simp only [Shape.ev, form_ev hci, truth_bool]
              by_cases e : (vs c).truth = true
              · rw [eqT a (by simp [SNode.children]) (by rw [hv, if_pos e]) hai]; simp [e, truth_bool]
              · simp [e]
            · simp only [Option.some.injEq] at hs; subst hs
              simp only [Shape.ev, form_ev hci, truth_bool]
              by_cases e : (vs c).truth = true
              · simp [e]
              · rw [eqT b (by simp [SNode.children]) (by rw [hv, if_neg e]) hbi]; simp [e, truth_bool]
          · cases hs
        · cases hs
    · cases hw

end

/-- A lowering checked by `Trace.check`, whose lowered problem has an answer
    that `Problem.accepts` accepts, has no model: no model of the surface
    script satisfies its assertions, over any ordered field whose elements
    have floors (the reals). -/
theorem Trace.unsat {SP : SProblem} {P : Problem} {tr : Trace} {A : Answer}
    (hc : tr.check SP P A = true) (hA : P.accepts A = true) (Ms : Surf.Model R U) (size : Val R U → Nat)
    (hL : SP.Laws Ms size) (hfloor : ∀ r : R, ∃ k : Int, IsFloor r k)
    (hin : ∀ a ∈ SP.asserts, Surf.holds Ms.toInterp SP.nodes a) : False := by
  have hcs := check_spec hc
  have hAc := accepted hA
  apply Problem.accepts_sound hA (lowModel SP P tr Ms) (fun v => size (dec v))
    (lowModel_laws hcs.sorts hcs.sig hL hcs.wf hcs.typed hAc.wf) 
    (fun f hf => by
      obtain ⟨hfl, _, hw⟩ := hcs.inputs f hf
      exact input_holds hcs hAc hL hfloor hin hfl hw)
  · intro s hs fs hfs f hf
    obtain ⟨hfl, _, hw⟩ := hcs.assumed s hs fs hfs f hf
    exact input_holds hcs hAc hL hfloor hin hfl hw
  · exact low_rng hcs hAc hL

end Vik.Lower
