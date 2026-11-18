import Vik.Lower.Laws

/-!
# Each surface node and its lowering take the same value

In the lowered model of a surface model (`Vik/Lower/Model.lean`), the
lowered node of each surface node takes the value of the surface node
(`corr`); so the lowered inputs hold when the surface assertions do, and a
lowering checked by `Trace.check` of an answer `Problem.accepts` accepts has
no surface model (`Trace.unsat`).
-/

set_option linter.unusedSectionVars false

namespace Vik.Lower

open Lean.Grind Vik.Real Vik.Low Vik.Surf

variable {R V : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R]
  [OrderedRing R] [IsCharP R 0]

attribute [local instance low] Lean.Grind.Ring.intCast

/-! ## Shapes of lists -/

theorem bool_eq_decide {b : Bool} {p : Prop} {_ : Decidable p} (h : b = true ↔ p) : b = decide p := by
  cases b <;> simp_all

/-- A shape that takes a Boolean value. -/
def IsBool (I : Low.Interp R V) (ρ : Nat → Val R V) (s : Shape) : Prop := ∃ b, s.ev I ρ = .bool b

section
variable (I : Low.Interp R V) (ρ : Nat → Val R V)

theorem chainS_ev (ss : List Shape) (h : ∀ s ∈ ss, IsBool I ρ s) : (chainS ss).ev I ρ = (Shape.and ss).ev I ρ := by
  match ss, h with
  | [s], h =>
    obtain ⟨b, hb⟩ := h s (by simp)
    simp only [chainS, Shape.ev, Shape.allTrue, hb, truth_bool, Bool.and_true]
  | [], _ => rfl
  | _ :: _ :: _, _ => rfl

/-- A chain of conditions on consecutive pairs. -/
theorem chain_ev {α : Type} (l : List α) (mk : α → α → Shape) (r : α → α → Prop)
    (h : ∀ x ∈ l, ∀ y ∈ l, ∃ b, (mk x y).ev I ρ = .bool b ∧ (b = true ↔ r x y)) :
    ∃ b, (chainS ((consec l).map fun p => mk p.1 p.2)).ev I ρ = .bool b ∧ (b = true ↔ chainP r l) := by
  rw [chainS_ev]
  · refine ⟨_, rfl, ?_⟩
    rw [Shape.allTrue_eq]
    induction l with
    | nil => simp [consec, chainP]
    | cons x l ih =>
      cases l with
      | nil => simp [consec, chainP]
      | cons y l =>
        simp only [consec, List.map_cons, List.all_cons, Bool.and_eq_true, chainP]
        obtain ⟨b, hb, hr⟩ := h x (by simp) y (by simp)
        rw [hb, truth_bool, hr]
        have := ih (fun a ma c mc => h a (by simp_all) c (by simp_all))
        rw [this]
  · intro s m
    obtain ⟨⟨x, y⟩, hp, rfl⟩ := List.mem_map.mp m
    have : x ∈ l ∧ y ∈ l := by
      clear h m
      induction l with
      | nil => simp [consec] at hp
      | cons a l ih =>
        cases l with
        | nil => simp [consec] at hp
        | cons b l =>
          simp only [consec, List.mem_cons] at hp
          rcases hp with hp | hp
          · cases hp; simp
          · have := ih hp; simp_all
    obtain ⟨b, hb, _⟩ := h x this.1 y this.2
    exact ⟨b, hb⟩

theorem mem_allPairs {α : Type} {l : List α} {x y : α} (h : (x, y) ∈ allPairs l) : x ∈ l ∧ y ∈ l := by
  induction l with
  | nil => simp [allPairs] at h
  | cons a l ih =>
    simp only [allPairs, List.mem_append, List.mem_map, Prod.mk.injEq] at h
    rcases h with ⟨b, hb, rfl, rfl⟩ | h
    · simp [hb]
    · have := ih h; simp_all

/-- A condition on all pairs. -/
theorem pairs_ev {α : Type} (l : List α) (mk : α → α → Shape) (r : α → α → Prop)
    (h : ∀ x ∈ l, ∀ y ∈ l, ∃ b, (mk x y).ev I ρ = .bool b ∧ (b = true ↔ r x y)) :
    ∃ b, (Shape.and ((allPairs l).map fun p => mk p.1 p.2)).ev I ρ = .bool b ∧ (b = true ↔ pairwiseP r l) := by
  refine ⟨_, rfl, ?_⟩
  rw [Shape.allTrue_eq]
  induction l with
  | nil => simp [allPairs, pairwiseP]
  | cons x l ih =>
    simp only [allPairs, List.map_append, List.map_map, List.all_append, Bool.and_eq_true, pairwiseP]
    rw [ih (fun a ma c mc => h a (by simp [ma]) c (by simp [mc]))]
    simp only [List.all_eq_true, List.mem_map, Function.comp_apply]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun y my => ?_, h2⟩
      obtain ⟨b, hb, hr⟩ := h x (by simp) y (by simp [my])
      have := h1 _ ⟨y, my, rfl⟩
      rw [hb, truth_bool] at this
      exact hr.mp this
    · rintro ⟨h1, h2⟩
      refine ⟨fun t ⟨y, my, e⟩ => ?_, h2⟩
      subst e
      obtain ⟨b, hb, hr⟩ := h x (by simp) y (by simp [my])
      rw [hb, truth_bool]
      exact hr.mpr (h1 y my)

theorem impliesS_ev (l : List Shape) (bs : List Bool) (hl : l.map (fun s => s.ev I ρ) = bs.map Val.bool)
    {s : Shape} (h : impliesS l = some s) : s.ev I ρ = .bool (impliesR bs) := by
  induction l generalizing bs s with
  | nil => simp [impliesS] at h
  | cons t l ih =>
    cases bs with
    | nil => simp at hl
    | cons b bs =>
      simp only [List.map_cons, List.cons.injEq] at hl
      cases l with
      | nil =>
        cases bs with
        | cons _ _ => simp at hl
        | nil => simp only [impliesS, Option.some.injEq] at h; subst h; simp [impliesR, hl.1]
      | cons u l =>
        simp only [impliesS] at h
        cases e : impliesS (u :: l) with
        | none => simp [e] at h
        | some s' =>
          rw [e] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h
          have := ih bs hl.2 e
          cases bs with
          | nil => simp at hl
          | cons b' bs => simp only [Shape.ev, hl.1, this, truth_bool, impliesR]

theorem xorS_ev (l : List Shape) (bs : List Bool) (hl : l.map (fun s => s.ev I ρ) = bs.map Val.bool)
    {s : Shape} (h : xorS l = some s) : s.ev I ρ = .bool (xorL bs) := by
  cases l with
  | nil => simp [xorS] at h
  | cons t l =>
    cases bs with
    | nil => simp at hl
    | cons b bs =>
      simp only [xorS, Option.some.injEq] at h; subst h
      simp only [List.map_cons, List.cons.injEq] at hl
      simp only [xorL]
      obtain ⟨h1, h2⟩ := hl
      induction l generalizing bs t b with
      | nil => cases bs <;> simp_all
      | cons u l ih =>
        cases bs with
        | nil => simp at h2
        | cons c bs =>
          simp only [List.map_cons, List.cons.injEq] at h2
          simp only [List.foldl_cons]
          apply ih _ (b != c) bs _ h2.2
          simp only [Shape.ev, h1, h2.1, truth_bool]
          rfl

end

theorem chainP_map {α β : Type} (r : β → β → Prop) (f : α → β) :
    ∀ l : List α, chainP r (l.map f) ↔ chainP (fun x y => r (f x) (f y)) l
  | [] => by simp [chainP]
  | [_] => by simp [chainP]
  | x :: y :: l => by
    simp only [List.map_cons, chainP]
    rw [← List.map_cons, chainP_map r f (y :: l)]

theorem pairwiseP_map {α β : Type} (r : β → β → Prop) (f : α → β) :
    ∀ l : List α, pairwiseP r (l.map f) ↔ pairwiseP (fun x y => r (f x) (f y)) l
  | [] => by simp [pairwiseP]
  | x :: l => by
    simp only [List.map_cons, pairwiseP, List.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    rw [pairwiseP_map r f l]

theorem cast_le_iff {a b : Int} : (a : R) ≤ (b : R) ↔ a ≤ b := by
  constructor
  · intro h
    rcases Int.lt_or_le b a with h' | h'
    · have := cast_lt (R := R) h'
      exact absurd h (by grind)
    · exact h'
  · exact cast_le

theorem cast_lt_iff {a b : Int} : (a : R) < (b : R) ↔ a < b := by
  constructor
  · intro h
    rcases Int.lt_or_le a b with h' | h'
    · exact h'
    · have := cast_le (R := R) h'
      exact absurd h (by grind)
  · exact cast_lt

theorem cast_succ_le_iff {a b : Int} : (a : R) + 1 ≤ (b : R) ↔ a < b := by
  have : (a : R) + 1 = ((a + 1 : Int) : R) := by rw [Ring.intCast_add, Ring.intCast_one]
  rw [this, cast_le_iff]; omega

theorem num_int_eq_iff {U : Type} {a b : Int} : (Val.num (a : R) : Val R U) = .num (b : R) ↔ a = b := by
  constructor
  · intro h; injection h with h'; exact cast_inj h'
  · intro h; rw [h]

theorem ne_iff_lt_or_gt {a b : R} : a ≠ b ↔ a < b ∨ b < a := by
  constructor
  · intro h
    rcases Std.le_total (a := a) (b := b) with h1 | h1
    · by_cases h2 : b ≤ a
      · exact absurd (Std.le_antisymm h1 h2) h
      · exact .inl (Std.lt_iff_le_and_not_ge.mpr ⟨h1, h2⟩)
    · by_cases h2 : a ≤ b
      · exact absurd (Std.le_antisymm h2 h1) h
      · exact .inr (Std.lt_iff_le_and_not_ge.mpr ⟨h1, h2⟩)
  · rintro (h | h) rfl <;> exact (Std.lt_iff_le_and_not_ge.mp h).2 (Std.le_refl _)

@[simp] theorem toR_num {U : Type} (r : R) : (Val.num r : Val R U).toR = r := rfl

/-! ## Arithmetic -/

section
variable (ρ : Nat → R)

theorem sumForms_eval {α : Type} (F : α → Lia.Form × Int) (v : α → R) :
    ∀ l : List α, (∀ a ∈ l, Lia.eval ρ (F a).1 + ((F a).2 : R) = v a) →
      Lia.eval ρ (sumForms (l.map F)).1 + ((sumForms (l.map F)).2 : R) = (l.map v).foldr (· + ·) 0
  | [], _ => by simp [sumForms, Lia.eval]; grind
  | a :: l, h => by
    simp only [List.map_cons, sumForms, List.foldr_cons]
    rw [eval_append, Ring.intCast_add, ← sumForms_eval F v l (fun b m => h b (by simp [m])), ← h a (by simp)]
    grind

theorem mul2_eval {p q r : Lia.Form × Int} (h : mul2 p q = some r) :
    Lia.eval ρ r.1 + (r.2 : R) = (Lia.eval ρ p.1 + (p.2 : R)) * (Lia.eval ρ q.1 + (q.2 : R)) := by
  unfold mul2 at h
  split at h
  · rename_i hp
    cases h
    obtain ⟨f, c⟩ := p
    simp only [List.isEmpty_iff] at hp
    simp only at hp ⊢; subst hp
    rw [Lia.eval_scale, Lia.rat_intCast, Ring.intCast_mul]
    simp only [Lia.eval]; grind
  · split at h
    · rename_i _ hq
      cases h
      obtain ⟨g, d⟩ := q
      simp only [List.isEmpty_iff] at hq
      simp only at hq ⊢; subst hq
      rw [Lia.eval_scale, Lia.rat_intCast, Ring.intCast_mul]
      simp only [Lia.eval]; grind
    · cases h

theorem mulForms_eval {α : Type} (F : α → Lia.Form × Int) (v : α → R) :
    ∀ (l : List α), (∀ a ∈ l, Lia.eval ρ (F a).1 + ((F a).2 : R) = v a) → ∀ (r : Lia.Form × Int),
      mulForms (l.map F) = some r → Lia.eval ρ r.1 + (r.2 : R) = (l.map v).foldr (· * ·) 1
  | [], _, r, hr => by
    simp only [List.map_nil, mulForms, Option.some.injEq] at hr; subst hr
    simp [Lia.eval]; grind
  | a :: l, h, r, hr => by
    simp only [List.map_cons, mulForms] at hr
    cases e : mulForms (l.map F) with
    | none => rw [e] at hr; cases hr
    | some q =>
      rw [e] at hr
      simp only [Option.bind_some] at hr
      rw [mul2_eval ρ hr, h a (by simp), mulForms_eval F v l (fun b m => h b (by simp [m])) q e]
      rfl

end

theorem sumR_eq {U : Type} (vs : List (Val R U)) : sumR vs = (vs.map Val.toR).foldr (· + ·) 0 := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp only [sumR, ih, List.map_cons, List.foldr_cons]

theorem prodR_eq {U : Type} (vs : List (Val R U)) : prodR vs = (vs.map Val.toR).foldr (· * ·) 1 := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp only [prodR, ih, List.map_cons, List.foldr_cons]

/-! ## Leaves of the lowered model -/

variable {U : Type}

@[simp] theorem surf_get_values (I : Surf.Interp R U) (nodes : List SNode) (a : Nat) :
    Low.get (Surf.values I nodes) a = Surf.val I nodes a := rfl

section
variable {SP : SProblem} {P : Problem} {tr : Trace} {Ms : Surf.Model R U}
  (hM : Ms.Sound SP.sig) (hw : Surf.wellFormed SP.nodes = true) (ht : Surf.typed SP.sig SP.nodes SP.sortOf = true)

set_option quotPrecheck false in
local notation "ρ" => Low.val (lowModel SP P tr Ms).toInterp P.nodes
local notation "vs" => Surf.val Ms.toInterp SP.nodes
set_option quotPrecheck false in
local notation "MI" => (lowModel SP P tr Ms).toInterp

include hM hw ht

theorem dom_at {a : Nat} (ha : a < SP.nodes.length) : Ms.dom (SP.sort a) (vs a) :=
  Surf.val_dom hM hw ht a ha

theorem v_bool {a : Nat} (ha : a < SP.nodes.length) (hb : SP.isBool a = true) : ∃ b, vs a = .bool b := by
  simp only [SProblem.isBool, SSig.is, beq_iff_eq] at hb
  exact (hM.bool _ _ hb).mp (dom_at hM hw ht ha)

theorem v_num {a : Nat} (ha : a < SP.nodes.length) (hb : SP.isNum a = true) : ∃ r, vs a = .num r :=
  Surf.dom_num_of_numeric hM hb (dom_at hM hw ht ha)

theorem v_int {a : Nat} (ha : a < SP.nodes.length) (hb : SP.isInt a = true) : ∃ k : Int, vs a = .num (k : R) := by
  simp only [SProblem.isInt, SSig.is, beq_iff_eq] at hb
  exact (hM.int _ _ hb).mp (dom_at hM hw ht ha)

theorem leaf_ev {a : Nat} (ha : a < SP.nodes.length) (e : ρ (tr.at a) = enc (vs a)) :
    (leaf SP tr a).ev MI ρ = enc (vs a) := by
  unfold leaf
  split
  · rename_i hb
    obtain ⟨b, hb'⟩ := v_bool hM hw ht ha hb
    simp only [Shape.ev, e, hb', enc_bool, truth_bool]
  · exact e

omit hM hw ht in
theorem form_ev {a : Nat} (e : ρ (tr.at a) = enc (vs a)) : (form tr a).ev MI ρ = .bool (vs a).truth := by
  simp only [form, Shape.ev, e, truth_enc]

omit hM hw ht in
theorem lin_ev (hwP : Low.wellFormed P.nodes = true) {a : Nat} (e : ρ (tr.at a) = enc (vs a)) :
    Lia.eval (fun u => (ρ u).toR) (linOf P tr a).1 + ((linOf P tr a).2 : R) = (vs a).toR := by
  have := lin_sound (I := MI) hwP (tr.at a)
  rw [e, toR_enc] at this
  rw [this]; rfl

theorem typed_at {i : Nat} {n : SNode} (hn : SP.nodes[i]? = some n) :
    Surf.nodeTyped SP.sig SP.sortOf n (SP.sort i) = true := by
  have hi := lt_of_get hn
  simp only [Tab.at_eq, Surf.typed, Tab.at_eq, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at ht
  have := ht.2 i hi
  rw [hn] at this
  exact this

omit hM ht in
theorem children_lt {i : Nat} {n : SNode} (hn : SP.nodes[i]? = some n) : ∀ c ∈ n.children, c < i := by
  have := List.all_eq_true.mp hw i (List.mem_range.mpr (lt_of_get hn))
  rw [Tab.at_eq, hn] at this
  simpa using this

open Classical in
omit hM hw ht in
theorem ltInt_ev (hwP : Low.wellFormed P.nodes = true) {x y : Nat} (ex : ρ (tr.at x) = enc (vs x))
    (ey : ρ (tr.at y) = enc (vs y)) :
    (ltInt P tr x y).ev MI ρ = .bool (decide ((vs x).toR + 1 ≤ (vs y).toR)) := by
  have e : Lia.eval (fun u => (ρ u).toR) (linOf P tr x).1 + (((linOf P tr x).2 + 1 : Int) : R) = (vs x).toR + 1 := by
    rw [Ring.intCast_add, Ring.intCast_one, ← lin_ev hwP ex]; grind
  simp only [ltInt, Shape.ev, toR_num, e, ey, toR_enc]

open Classical in
omit hM hw ht in
theorem le_ev {x y : Nat} (ex : ρ (tr.at x) = enc (vs x)) (ey : ρ (tr.at y) = enc (vs y)) :
    (Shape.le (.same (tr.at x)) (.same (tr.at y))).ev MI ρ = .bool (decide ((vs x).toR ≤ (vs y).toR)) := by
  simp only [Shape.ev, ex, ey, toR_enc]

open Classical in
omit hM hw ht in
theorem lt_ev {x y : Nat} (ex : ρ (tr.at x) = enc (vs x)) (ey : ρ (tr.at y) = enc (vs y)) :
    (Shape.lt (.same (tr.at x)) (.same (tr.at y))).ev MI ρ = .bool (decide ((vs x).toR < (vs y).toR)) := by
  simp only [Shape.ev, ex, ey, toR_enc]

end

end Vik.Lower
