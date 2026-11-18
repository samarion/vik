import Vik.Lower.Model

/-!
# The lowered model satisfies the laws

What the checks of the signature say, and that the model of
`Vik/Lower/Model.lean` satisfies the laws of the lowered problem
(`Problem.Laws`) when the surface model satisfies those of the script.
-/

set_option linter.unusedSectionVars false

namespace Vik.Lower

open Lean.Grind Vik.Real Vik.Low Vik.Surf

/-! ## What the checks say -/

section
variable {SP : SProblem} {P : Problem} {tr : Trace}

structure SortsSpec (SP : SProblem) : Prop where
  fn : ∀ (s : Nat) (as : List Nat) (r : Nat), SP.sig.sorts[s]? = some (SSort.fn as r) → (∀ a ∈ as, a < SP.sig.sorts.length) ∧ r < SP.sig.sorts.length
  array : ∀ (s i e : Nat), SP.sig.sorts[s]? = some (SSort.array i e) → i < SP.sig.sorts.length ∧ e < SP.sig.sorts.length
  decls : ∀ (k s : Nat), SP.sig.decls[k]? = some s → s < SP.sig.sorts.length
  sortOf : ∀ (i s : Nat), SP.sortOf[i]? = some s → s < SP.sig.sorts.length
  dt : ∀ d cs, (d, cs) ∈ SP.datatypes → d < SP.sig.sorts.length ∧ SP.sig.sorts[d]? = some .user ∧
    ∀ C T Ss, (C, T, Ss) ∈ cs → C < SP.sig.decls.length ∧ T < SP.sig.decls.length ∧
      ∀ S ∈ Ss, S < SP.sig.decls.length

theorem sortsOk_spec (h : SP.sortsOk = true) : SortsSpec SP := by
  simp only [SProblem.sortsOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hs, hd⟩, ho⟩, hdt⟩ := h
  have get_mem : ∀ {α : Type} (l : List α) (i : Nat) (x : α), l[i]? = some x → x ∈ l :=
    fun l i x h => List.mem_of_getElem? h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s as r e; have := hs _ (get_mem _ _ _ e); simpa using this
  · intro s i e' e; have := hs _ (get_mem _ _ _ e); simpa using this
  · intro k s e; exact hd _ (get_mem _ _ _ e)
  · intro i s e; exact ho _ (get_mem _ _ _ e)
  · intro d cs m
    have := hdt _ m
    exact ⟨this.1.1, by simpa using this.1.2, fun C T Ss mc => by
      have := this.2 _ mc
      exact ⟨this.1.1, this.1.2, this.2⟩⟩

structure SigSpec (SP : SProblem) (P : Problem) (tr : Trace) : Prop where
  sorts : ∀ s < SP.sig.sorts.length, P.sig.sorts[s]? = (SP.sig.sorts[s]?).map lowerSort
  decls : ∀ k < SP.sig.decls.length, P.sig.decls[k]? = SP.sig.decls[k]?
  declsLen : P.sig.decls.length = SP.sig.decls.length + tr.mints.length
  extra : ∀ s d, SP.sig.sorts.length ≤ s → P.sig.sorts[s]? = some d →
    ∃ arr idx el, d = .fn [arr, idx, el] arr ∧ SP.sig.sorts[arr]? = some (.array idx el)
  ite : ∀ m i, tr.mints[m]? = some (.ite i) →
    (∃ c a b, SP.nodes[i]? = some (.ite c a b)) ∧ SP.isBool i = false ∧
      P.sig.decls[SP.sig.decls.length + m]? = some (SP.sort i)
  store : ∀ m s, tr.mints[m]? = some (.store s) →
    ∃ idx el ds, SP.sig.sorts[s]? = some (.array idx el) ∧ P.sig.decls[SP.sig.decls.length + m]? = some ds ∧
      SP.sig.sorts.length ≤ ds ∧ P.sig.sorts[ds]? = some (.fn [s, idx, el] s) ∧
      ∀ m' s', m' ≠ m → tr.mints[m']? = some (.store s') → P.sig.decls[SP.sig.decls.length + m']? ≠ some ds
  rule : ∀ m r j, tr.mints[m]? = some (.rule r j) →
    (∃ s, P.sig.decls[SP.sig.decls.length + m]? = some s ∧
      (SP.sig.sorts[s]? = some .int ∨ ∃ w, SP.sig.sorts[s]? = some (.bv w) ∧
        (r.bvOut j w = true ∨
          ivSub (r.fixedIv (tr.fixedAt SP P ((m + 1) * P.nodes.length) 2) j) 0 (2 ^ w - 1) = true))) ∧
      ∀ x ∈ r.args, x < P.nodes.length ∧ depthOf (depths (tr.rank SP) P.nodes) x ≤ m
  real : ∀ m r, tr.mints[m]? = some (.real r) →
    (∃ s, P.sig.decls[SP.sig.decls.length + m]? = some s ∧
      SP.sig.sorts[s]? = some (if r.isInt then .int else .real)) ∧
      ∀ x ∈ r.args, x < P.nodes.length ∧ depthOf (depths (tr.rank SP) P.nodes) x ≤ m
  witness : ∀ m s, tr.mints[m]? = some (.witness s) →
    P.sig.decls[SP.sig.decls.length + m]? = some s ∧
      (SP.sig.sorts[s]? = some .bool ∨ SP.sig.sorts[s]? = some .int ∨ SP.sig.sorts[s]? = some .real ∨
        ∃ w, SP.sig.sorts[s]? = some (.bv w))
  pick : ∀ m i, tr.mints[m]? = some (.pick i) →
    i < SP.nodes.length ∧ P.sig.decls[SP.sig.decls.length + m]? = some (SP.sort i)
  stores : ∀ n ∈ P.stores, SP.sig.decls.length ≤ n ∧ ∃ s, tr.mints[n - SP.sig.decls.length]? = some (.store s)
  datatypes : P.datatypes = SP.datatypes
  bvIndex : P.bvIndex = SP.bvIndex
  bvNodes : ∀ j < P.nodes.length, ∀ w, SP.sortWidth (P.sortOf[j]?.getD 0) = some w →
    (∃ k, P.nodes[j]? = some (.const k)) ∨ (∃ f xs, P.nodes[j]? = some (.app f xs)) ∨
      (∃ c : Int, P.nodes[j]? = some (.num c) ∧ 0 ≤ c ∧ c < 2 ^ w) ∨
      ivSub (tr.fixedAt SP P (tr.mu SP P j) 2 j) 0 (2 ^ w - 1) = true

theorem sigOk_spec (h : tr.sigOk SP P = true) : SigSpec SP P tr := by
  simp only [Tab.at_eq, Trace.sigOk, Tab.at_eq, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hs, hd⟩, hl⟩, hx⟩, hm⟩, hst⟩, hdt⟩, hbv⟩, hbn⟩ := h
  refine ⟨?_, ?_, hl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hdt, hbv, ?_⟩
  · intro s hs'
    rw [← List.getElem?_map, ← hs, List.getElem?_take_of_lt hs']
  · intro k hk
    conv => rhs; rw [← hd]
    rw [List.getElem?_take_of_lt hk]
  · intro s d hle he
    have hlt : s < P.sig.sorts.length := by
      rcases Nat.lt_or_ge s P.sig.sorts.length with h' | h'
      · exact h'
      · rw [List.getElem?_eq_none h'] at he; cases he
    have := hx s hlt
    simp only [Bool.or_eq_true, decide_eq_true_eq] at this
    rcases this with h' | h'
    · omega
    · rw [he] at h'
      split at h'
      · rename_i arr idx el arr' heq
        cases heq
        simp only [Bool.and_eq_true, beq_iff_eq] at h'
        exact ⟨arr, idx, el, by rw [h'.1], h'.2⟩
      · cases h'
  · intro m i hmi
    have hlt : m < tr.mints.length := by
      rcases Nat.lt_or_ge m tr.mints.length with h' | h'
      · exact h'
      · rw [List.getElem?_eq_none h'] at hmi; cases hmi
    have := hm m hlt
    rw [hmi] at this
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at this
    obtain ⟨⟨hn, hb⟩, hdc⟩ := this
    refine ⟨?_, hb, hdc⟩
    split at hn
    · rename_i c a b he; exact ⟨c, a, b, he⟩
    · cases hn
  · intro m s hms
    have hlt : m < tr.mints.length := by
      rcases Nat.lt_or_ge m tr.mints.length with h' | h'
      · exact h'
      · rw [List.getElem?_eq_none h'] at hms; cases hms
    have := hm m hlt
    rw [hms] at this
    simp only at this
    split at this
    · rename_i idx el ds hs1 hd1
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true, List.mem_range,
        Bool.or_eq_true] at this
      obtain ⟨⟨hle, hds⟩, honly⟩ := this
      refine ⟨idx, el, ds, hs1, hd1, hle, hds, fun m' s' hne hm' => ?_⟩
      have hlt' : m' < tr.mints.length := by
        rcases Nat.lt_or_ge m' tr.mints.length with h' | h'
        · exact h'
        · rw [List.getElem?_eq_none h'] at hm'; cases hm'
      rcases honly m' hlt' with h' | h'
      · exact absurd h' hne
      · rw [hm'] at h'; simpa using h'
    · cases this
  · intro m r j hmr
    have hlt : m < tr.mints.length := (List.getElem?_eq_some_iff.mp hmr).1
    have := hm m hlt
    rw [hmr] at this
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at this
    obtain ⟨hd1, hargs⟩ := this
    refine ⟨?_, hargs⟩
    split at hd1
    · rename_i s e
      split at hd1
      · rename_i hs; exact ⟨s, e, .inl hs⟩
      · rename_i w hs; exact ⟨s, e, .inr ⟨w, hs, Bool.or_eq_true_iff.mp hd1⟩⟩
      · cases hd1
    · cases hd1
  · intro m r hmr
    have hlt : m < tr.mints.length := (List.getElem?_eq_some_iff.mp hmr).1
    have := hm m hlt
    rw [hmr] at this
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at this
    obtain ⟨hd1, hargs⟩ := this
    refine ⟨?_, hargs⟩
    split at hd1
    · rename_i s e; exact ⟨s, e, by simpa using hd1⟩
    · cases hd1
  · intro m s hms
    have hlt : m < tr.mints.length := (List.getElem?_eq_some_iff.mp hms).1
    have := hm m hlt
    rw [hms] at this
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    obtain ⟨hd1, hs1⟩ := this
    refine ⟨hd1, ?_⟩
    split at hs1
    · exact .inl (by assumption)
    · exact .inr (.inl (by assumption))
    · exact .inr (.inr (.inl (by assumption)))
    · rename_i w e; exact .inr (.inr (.inr ⟨w, e⟩))
    · cases hs1
  · intro m i hmi
    have hlt : m < tr.mints.length := (List.getElem?_eq_some_iff.mp hmi).1
    have := hm m hlt
    rw [hmi] at this
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    exact this
  · intro n hn
    have := hst n hn
    simp only [decide_eq_true_eq] at this
    refine ⟨this.1, ?_⟩
    split at this
    · rename_i s he; exact ⟨s, he⟩
    · exact absurd this.2 (by simp)
  · intro j hj w hb
    have := hbn j hj
    rw [lookup_bvIndex, hb] at this
    simp only at this
    split at this
    · rename_i k e; exact .inl ⟨k, e⟩
    · rename_i f xs e; exact .inr (.inl ⟨f, xs, e⟩)
    · rename_i c e
      simp only [Bool.and_eq_true, decide_eq_true_eq] at this
      exact .inr (.inr (.inl ⟨c, e, this.1, this.2⟩))
    · exact .inr (.inr (.inr this))
    · cases this

end


/-! ## The laws -/

variable {R U : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R]
  [OrderedRing R] [IsCharP R 0]

attribute [local instance low] Lean.Grind.Ring.intCast

theorem lt_of_get {α : Type} {l : List α} {i : Nat} {x : α} (h : l[i]? = some x) : i < l.length := by
  rcases Nat.lt_or_ge i l.length with h' | h'
  · exact h'
  · rw [List.getElem?_eq_none h'] at h; cases h

theorem forall2_imp {α β : Type} {p q : α → β → Prop} (h : ∀ a b, p a b → q a b) :
    ∀ (as : List α) (bs : List β), Forall2 p as bs → Forall2 q as bs
  | [], [], _ => trivial
  | a :: as, b :: bs, hp => ⟨h a b hp.1, forall2_imp h as bs hp.2⟩
  | [], _ :: _, hp => hp.elim
  | _ :: _, [], hp => hp.elim

section
variable {SP : SProblem} {P : Problem} {tr : Trace} {Ms : Surf.Model R U}
  (hS : SortsSpec SP) (hG : SigSpec SP P tr)

include hG in
/-- A lowered sort that is not a function is one of the script. -/
theorem base_of_not_fn {s : Nat} {d : SortDef} (h : P.sig.sorts[s]? = some d) (hd : ∀ as r, d ≠ .fn as r) :
    s < SP.sig.sorts.length := by
  rcases Nat.lt_or_ge s SP.sig.sorts.length with h' | h'
  · exact h'
  · obtain ⟨arr, idx, el, rfl, _⟩ := hG.extra s d h' h
    exact absurd rfl (hd _ _)

include hG in
theorem surf_sort_of {s : Nat} {d : SortDef} (hs : s < SP.sig.sorts.length) (h : P.sig.sorts[s]? = some d) :
    ∃ x, SP.sig.sorts[s]? = some x ∧ lowerSort x = d := by
  rw [hG.sorts s hs] at h
  cases e : SP.sig.sorts[s]? with
  | none => rw [e] at h; cases h
  | some x => rw [e] at h; cases h; exact ⟨x, rfl, rfl⟩

include hS hG in
theorem argSorts_eq {C : Nat} (hC : C < SP.sig.decls.length) : P.argSorts C = SP.argSorts C := by
  unfold Problem.argSorts SProblem.argSorts
  rw [hG.decls C hC]
  cases e : SP.sig.decls[C]? with
  | none => rfl
  | some s =>
    simp only
    rw [hG.sorts s (hS.decls C s e)]
    generalize Option.map lowerSort SP.sig.sorts[s]? = o
    rcases o with _ | d
    · rfl
    · cases d <;> rfl

include hS in
theorem argSorts_lt (C : Nat) : ∀ a ∈ SP.argSorts C, a < SP.sig.sorts.length := by
  unfold SProblem.argSorts
  cases e : SP.sig.decls[C]? with
  | none => simp
  | some s =>
    simp only
    cases e' : SP.sig.sorts[s]? with
    | none => simp
    | some x =>
      cases x with
      | fn as r => exact (hS.fn s as r e').1
      | array i el => simp [lowerSort]; exact (hS.array s i el e').1
      | _ => simp [lowerSort]

theorem ctorVal_enc {C : Nat} (hC : C < SP.sig.decls.length) (xs : List (Val R U)) :
    ctorVal (lowModel SP P tr Ms) C (xs.map enc) = enc (ctorVal (SModel.low Ms) C xs) := by
  unfold ctorVal
  simp only [List.isEmpty_map]
  split
  · exact const_base SP P tr Ms hC
  · rw [const_base SP P tr Ms hC, app_enc_enc]; rfl

include hS hG in
/-- The arguments of a surface symbol, as lowered values. -/
theorem forall2_args (hM : Ms.Sound SP.sig) {C : Nat} (hC : C < SP.sig.decls.length) (xs : List (Val R (U ⊕ Nat)))
    (h : Forall2 (fun a x => (lowModel SP P tr Ms).dom a x ∧ inRange P.bvIndex a x) (P.argSorts C) xs) :
    ∃ ys, xs = ys.map enc ∧ Forall2 Ms.dom (SP.argSorts C) ys := by
  rw [argSorts_eq hS hG hC, hG.bvIndex] at h
  exact (forall2_base SP P tr Ms hM _ xs (argSorts_lt hS C)).mp h

/-- A sort that is not a bit-vector has no width. -/
theorem sortWidth_none {SP : SProblem} {s : Nat} {x : SSort} (hx : SP.sig.sorts[s]? = some x)
    (h : ∀ w, x ≠ .bv w) : SP.sortWidth s = none := by
  unfold SProblem.sortWidth; rw [hx]
  split
  · rename_i w e; cases e; exact absurd rfl (h w)
  · rfl

/-- A surface value is a lowered one of its sort. -/
theorem dom_of_surf (hM : Ms.Sound SP.sig) {s : Nat} (hs : s < SP.sig.sorts.length) {w : Val R U}
    (h : Ms.dom s w) : (lowModel SP P tr Ms).dom s (enc w) :=
  ((rdom SP P tr Ms hM hs (enc w)).mpr ⟨w, h, rfl⟩).1

end


section
variable {SP : SProblem} {P : Problem} {tr : Trace} {Ms : Surf.Model R U} {size : Val R U → Nat}
  (hS : SortsSpec SP) (hG : SigSpec SP P tr) (hL : SP.Laws Ms size)
  (hw : Surf.wellFormed SP.nodes = true) (ht : Surf.typed SP.sig SP.nodes SP.sortOf = true)
include hS hG hL

/-- A minted symbol is a store or the value of an `ite`. -/
theorem mint_of {k : Nat} (hk : SP.sig.decls.length ≤ k) (s : Nat) (h : P.sig.decls[k]? = some s) :
    ∃ m, k = SP.sig.decls.length + m ∧ ∃ x, tr.mints[m]? = some x := by
  have := lt_of_get h
  rw [hG.declsLen] at this
  refine ⟨k - SP.sig.decls.length, by omega, ?_⟩
  exact ⟨_, List.getElem?_eq_getElem (by omega)⟩

/-- A lowered value of a sort of the script, not a bit-vector, is a surface one. -/
theorem dom_enc {s : Nat} (hs : s < SP.sig.sorts.length) {x : SSort} (hx : SP.sig.sorts[s]? = some x)
    (hb : ∀ w, x ≠ .bv w) {v : Val R (U ⊕ Nat)}
    (h : (lowModel SP P tr Ms).dom s v) : ∃ w, Ms.dom s w ∧ v = enc w :=
  (dom_base SP P tr Ms hs (sortWidth_none hx hb) v).mp h

/-- A lowered value of a sort of the script, in range, is a surface one. -/
theorem dom_enc_rng {s : Nat} (hs : s < SP.sig.sorts.length) {v : Val R (U ⊕ Nat)}
    (h : (lowModel SP P tr Ms).dom s v) (hr : inRange P.bvIndex s v) : ∃ w, Ms.dom s w ∧ v = enc w := by
  rw [hG.bvIndex] at hr
  exact (rdom SP P tr Ms hL.sound hs v).mp ⟨h, hr⟩

include hw ht in
theorem lowModel_sound (hwl : Low.wellFormed P.nodes = true) : (lowModel SP P tr Ms).Sound P.sig P.bvIndex := by
  have hM := hL.sound
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  rotate_right
  · -- the sorts of bit-vectors are lowered to `Int`
    intro s w h
    rw [hG.bvIndex, lookup_bvIndex, sortWidth_eq] at h
    rw [hG.sorts s (lt_of_get h), h]
    rfl
  · intro s v h
    have hs := base_of_not_fn hG h (by intro _ _ e; cases e)
    obtain ⟨x, hx, ex⟩ := surf_sort_of hG hs h
    cases x <;> simp [lowerSort] at ex
    rw [dom_base SP P tr Ms hs (sortWidth_none hx (by intro _ e; cases e))]
    constructor
    · rintro ⟨w, hw', rfl⟩
      obtain ⟨b, rfl⟩ := (hM.bool s w hx).mp hw'
      exact ⟨b, rfl⟩
    · rintro ⟨b, rfl⟩
      exact ⟨.bool b, (hM.bool s _ hx).mpr ⟨b, rfl⟩, rfl⟩
  · intro s v h
    have hs := base_of_not_fn hG h (by intro _ _ e; cases e)
    obtain ⟨x, hx, ex⟩ := surf_sort_of hG hs h
    cases x with
    | bv w => exact dom_bv SP P tr Ms hs (sortWidth_eq.mpr hx) v
    | int =>
      rw [dom_base SP P tr Ms hs (sortWidth_none hx (by intro _ e; cases e))]
      constructor
      · rintro ⟨w, hw', rfl⟩
        obtain ⟨k, rfl⟩ := (hM.int s w hx).mp hw'
        exact ⟨k, rfl⟩
      · rintro ⟨k, rfl⟩
        exact ⟨.num (k : R), (hM.int s _ hx).mpr ⟨k, rfl⟩, rfl⟩
    | _ => simp [lowerSort] at ex
  · intro s v h
    have hs := base_of_not_fn hG h (by intro _ _ e; cases e)
    obtain ⟨x, hx, ex⟩ := surf_sort_of hG hs h
    cases x <;> simp [lowerSort] at ex
    rw [dom_base SP P tr Ms hs (sortWidth_none hx (by intro _ e; cases e))]
    constructor
    · rintro ⟨w, hw', rfl⟩
      obtain ⟨r, rfl⟩ := (hM.real s w hx).mp hw'
      exact ⟨r, rfl⟩
    · rintro ⟨r, rfl⟩
      exact ⟨.num r, (hM.real s _ hx).mpr ⟨r, rfl⟩, rfl⟩
  · intro s as r f xs h hf hxs
    rw [hG.bvIndex] at hxs ⊢
    rcases Nat.lt_or_ge s SP.sig.sorts.length with hs | hs
    · obtain ⟨x, hx, ex⟩ := surf_sort_of hG hs h
      cases x with
      | fn as' r' =>
        obtain ⟨f0, hf0, rfl⟩ := dom_enc hS hG hL hs hx (by intro _ e; cases e) hf
        simp only [lowerSort, SortDef.fn.injEq] at ex
        obtain ⟨h1, h2⟩ := ex
        subst h1; subst h2
        obtain ⟨has, hr⟩ := hS.fn s as' r' hx
        obtain ⟨ys, rfl, hys⟩ := (forall2_base SP P tr Ms hM as' xs has).mp hxs
        rw [app_enc_enc]
        exact (rdom SP P tr Ms hM hr _).mpr ⟨_, hM.fn s as' r' f0 ys hx hf0 hys, rfl⟩
      | array i e =>
        obtain ⟨f0, hf0, rfl⟩ := dom_enc hS hG hL hs hx (by intro _ e; cases e) hf
        simp only [lowerSort, SortDef.fn.injEq] at ex
        obtain ⟨rfl, rfl⟩ := ex
        obtain ⟨hi, he⟩ := hS.array s i e hx
        obtain ⟨ys, rfl, hys⟩ := (forall2_base SP P tr Ms hM [i] xs (by simpa using hi)).mp hxs
        cases ys with
        | nil => exact hys.elim
        | cons y ys =>
          cases ys with
          | cons _ _ => exact hys.2.elim
          | nil =>
            rw [app_enc_enc]
            exact (rdom SP P tr Ms hM he _).mpr ⟨_, hM.select s i e f0 y hx hf0 hys.1, rfl⟩
      | _ => simp [lowerSort] at ex
    · obtain ⟨arr, idx, el, hd, harr⟩ := hG.extra s _ hs h
      simp only [SortDef.fn.injEq] at hd
      obtain ⟨h1, h2⟩ := hd
      subst h1; subst h2
      have hf' := hf
      simp only [lowModel, Nat.not_lt.mpr hs, if_false] at hf'
      obtain ⟨k, rfl, _, _⟩ := hf'
      obtain ⟨hi, he⟩ := hS.array r idx el harr
      have ha := lt_of_get harr
      obtain ⟨ys, rfl, hys⟩ := (forall2_base SP P tr Ms hM [r, idx, el] xs (by simp; omega)).mp hxs
      match ys, hys with
      | [a, i, v], hys =>
        rw [List.map_cons, List.map_cons, List.map_cons, List.map_nil, app_store]
        exact (rdom SP P tr Ms hM ha _).mpr ⟨_, (hM.store r idx el a i v harr hys.1 hys.2.1 hys.2.2.1).1, rfl⟩
  · intro k s h
    rcases Nat.lt_or_ge k SP.sig.decls.length with hk | hk
    · rw [hG.decls k hk] at h
      have hs := hS.decls k s h
      rw [const_base SP P tr Ms hk]
      exact dom_of_surf hM hs (hM.const k s h)
    · obtain ⟨m, rfl, x, hx⟩ := mint_of hS hG hL hk s h
      have hm : SP.sig.decls.length + m - SP.sig.decls.length = m := by omega
      cases x with
      | ite i =>
        obtain ⟨⟨c, a, b, hi⟩, _, hd⟩ := hG.ite m i hx
        rw [h] at hd; cases hd
        rw [const_ite SP P tr Ms hk (by rw [hm]; exact hx)]
        have hil := lt_of_get hi
        have hso : SP.sortOf.length = SP.nodes.length := by
          simp only [Tab.at_eq, Surf.typed, Tab.at_eq, Bool.and_eq_true, beq_iff_eq] at ht; exact ht.1
        have hsl : SP.sort i < SP.sig.sorts.length := by
          unfold SProblem.sort
          rw [List.getElem?_eq_getElem (by omega)]
          exact hS.sortOf i _ (List.getElem?_eq_getElem (by omega))
        exact dom_of_surf hM hsl (Surf.val_dom hM hw ht i hil)
      | store s0 =>
        obtain ⟨idx, el, ds, _, hd, hle, _, _⟩ := hG.store m s0 hx
        rw [h] at hd; cases hd
        rw [const_store SP P tr Ms hk (by rw [hm]; exact hx)]
        simp only [lowModel, Nat.not_lt.mpr hle, if_false]
        exact ⟨_, rfl, ⟨hk, s0, by rw [hm]; exact hx⟩, h⟩
      | rule r j =>
        obtain ⟨⟨s1, hd1, hs1 | ⟨w, hs1, _⟩⟩, hargs⟩ := hG.rule m r j hx
        · rw [h] at hd1; cases hd1
          rw [const_rule SP P tr Ms hwl hx (fun x hx' => (hargs x hx').2)]
          have hsl := lt_of_get hs1
          have hb : SP.sortWidth s = none := sortWidth_none hs1 (by intro _ e; cases e)
          simp only [lowModel, hsl, if_true, hb, Option.isSome_none, Bool.false_eq_true, if_false]
          exact ⟨.num _, (hM.int s _ hs1).mpr ⟨_, rfl⟩, rfl⟩
        · rw [h] at hd1; cases hd1
          rw [const_rule SP P tr Ms hwl hx (fun x hx' => (hargs x hx').2)]
          have hsl := lt_of_get hs1
          have hb : SP.sortWidth s = some w := by simp [SProblem.sortWidth, hs1]
          simp only [lowModel, hsl, if_true, hb, Option.isSome_some, if_true, hs1]
          exact ⟨_, rfl⟩
      | pick i =>
        obtain ⟨hil, hd'⟩ := hG.pick m i hx
        rw [h] at hd'; cases hd'
        rw [const_pick SP P tr Ms hk (by rw [hm]; exact hx)]
        have hso : SP.sortOf.length = SP.nodes.length := by
          simp only [Tab.at_eq, Surf.typed, Tab.at_eq, Bool.and_eq_true, beq_iff_eq] at ht; exact ht.1
        have hsl : SP.sort i < SP.sig.sorts.length := by
          unfold SProblem.sort
          rw [List.getElem?_eq_getElem (by omega)]
          exact hS.sortOf i _ (List.getElem?_eq_getElem (by omega))
        exact dom_of_surf hM hsl (Surf.val_dom hM hw ht i hil)
      | witness s0 =>
        obtain ⟨hd1, hs1⟩ := hG.witness m s0 hx
        rw [h] at hd1; cases hd1
        rw [const_witness SP P tr Ms hk (by rw [hm]; exact hx)]
        rcases hs1 with hs1 | hs1 | hs1 | ⟨w, hs1⟩
        · have hsl := lt_of_get hs1
          have hb : SP.sortWidth s = none := sortWidth_none hs1 (by intro _ e; cases e)
          simp only [lowModel, hsl, if_true, hb, Option.isSome_none, Bool.false_eq_true, if_false, hs1]
          exact ⟨.bool false, (hM.bool s _ hs1).mpr ⟨_, rfl⟩, rfl⟩
        · have hsl := lt_of_get hs1
          have hb : SP.sortWidth s = none := sortWidth_none hs1 (by intro _ e; cases e)
          simp only [lowModel, hsl, if_true, hb, Option.isSome_none, Bool.false_eq_true, if_false, hs1]
          exact ⟨.num ((0 : Int) : R), (hM.int s _ hs1).mpr ⟨_, rfl⟩, by simp [enc, Ring.intCast_zero]⟩
        · have hsl := lt_of_get hs1
          have hb : SP.sortWidth s = none := sortWidth_none hs1 (by intro _ e; cases e)
          simp only [lowModel, hsl, if_true, hb, Option.isSome_none, Bool.false_eq_true, if_false, hs1]
          exact ⟨.num 0, (hM.real s _ hs1).mpr ⟨_, rfl⟩, by simp [enc]⟩
        · have hsl := lt_of_get hs1
          have hb : SP.sortWidth s = some w := by simp [SProblem.sortWidth, hs1]
          simp only [lowModel, hsl, if_true, hb, Option.isSome_some, if_true, hs1]
          exact ⟨0, by simp [Ring.intCast_zero]⟩
      | real r =>
        obtain ⟨⟨s1, hd1, hs1⟩, hargs⟩ := hG.real m r hx
        rw [h] at hd1; cases hd1
        rw [const_real SP P tr Ms hwl hx (fun x hx' => (hargs x hx').2)]
        have hsl := lt_of_get hs1
        have hb : SP.sortWidth s = none := sortWidth_none hs1 (by intro _ e; split at e <;> cases e)
        simp only [lowModel, hsl, if_true, hb, Option.isSome_none, Bool.false_eq_true, if_false]
        cases r with
        | floor t => exact ⟨.num _, (hM.int s _ (by simpa [RRule.isInt] using hs1)).mpr ⟨_, rfl⟩, rfl⟩
        | rat p q => exact ⟨.num _, (hM.real s _ (by simpa [RRule.isInt] using hs1)).mpr ⟨_, rfl⟩, rfl⟩
        | ratmul p q t => exact ⟨.num _, (hM.real s _ (by simpa [RRule.isInt] using hs1)).mpr ⟨_, rfl⟩, rfl⟩

include hw ht in
/-- The lowered model satisfies the laws of the lowered problem. -/
theorem lowModel_laws (hwl : Low.wellFormed P.nodes = true) : P.Laws (lowModel SP P tr Ms) (fun v => size (dec v)) := by
  have hM := hL.sound
  have dtC : ∀ d cs C T Ss, (d, cs) ∈ P.datatypes → (C, T, Ss) ∈ cs →
      (d, cs) ∈ SP.datatypes ∧ d < SP.sig.sorts.length ∧ C < SP.sig.decls.length ∧ T < SP.sig.decls.length ∧
        ∀ S ∈ Ss, S < SP.sig.decls.length := by
    intro d cs C T Ss hd hc
    rw [hG.datatypes] at hd
    have := hS.dt d cs hd
    exact ⟨hd, this.1, this.2.2 C T Ss hc⟩
  have args : ∀ {C : Nat}, C < SP.sig.decls.length → ∀ xs,
      Forall2 (fun a x => (lowModel SP P tr Ms).dom a x ∧ inRange P.bvIndex a x) (P.argSorts C) xs →
      ∃ ys, xs = ys.map enc ∧ Forall2 Ms.dom (SP.argSorts C) ys :=
    fun hC xs h => forall2_args hS hG hM hC xs h
  have dtd : ∀ d cs, (d, cs) ∈ SP.datatypes → ∀ {v : Val R (U ⊕ Nat)}, (lowModel SP P tr Ms).dom d v →
      ∃ w, Ms.dom d w ∧ v = enc w := fun d cs hd v hv =>
    dom_enc hS hG hL (hS.dt d cs hd).1 (hS.dt d cs hd).2.1 (by intro _ e; cases e) hv
  refine ⟨lowModel_sound hS hG hL hw ht hwl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- sel
    intro d cs C T Ss hd hc xs i S x hxs hS' hx
    obtain ⟨hd', _, hC, _, hSs⟩ := dtC d cs C T Ss hd hc
    obtain ⟨ys, rfl, hys⟩ := args hC xs hxs
    have hSl := hSs S (List.mem_of_getElem? hS')
    rw [List.getElem?_map] at hx
    cases e : ys[i]? with
    | none => rw [e] at hx; cases hx
    | some y =>
      rw [e] at hx; cases hx
      rw [ctorVal_enc hC, const_base SP P tr Ms hSl, ← List.map_singleton (f := enc), app_enc_enc,
        hL.sel d cs C T Ss hd' hc ys i S y hys hS' e]
  · -- test
    intro d cs C T Ss hd hc xs hxs
    obtain ⟨hd', _, hC, hT, _⟩ := dtC d cs C T Ss hd hc
    obtain ⟨ys, rfl, hys⟩ := args hC xs hxs
    rw [ctorVal_enc hC, const_base SP P tr Ms hT, ← List.map_singleton (f := enc), app_enc_enc,
      hL.test d cs C T Ss hd' hc ys hys]; rfl
  · -- testOther
    intro d cs C T Ss C' T' Ss' hd hc hc' hne ys hys
    obtain ⟨hd', _, hC, hT, _⟩ := dtC d cs C T Ss hd hc
    obtain ⟨_, _, hC', _, _⟩ := dtC d cs C' T' Ss' hd hc'
    obtain ⟨zs, rfl, hzs⟩ := args hC' ys hys
    rw [ctorVal_enc hC', const_base SP P tr Ms hT, ← List.map_singleton (f := enc), app_enc_enc]
    intro e
    exact hL.testOther d cs C T Ss C' T' Ss' hd' hc hc' hne zs hzs (enc_inj e)
  · -- inj
    intro d cs C T Ss hd hc xs ys hxs hys e
    obtain ⟨hd', _, hC, _, _⟩ := dtC d cs C T Ss hd hc
    obtain ⟨xs0, rfl, hxs0⟩ := args hC xs hxs
    obtain ⟨ys0, rfl, hys0⟩ := args hC ys hys
    rw [ctorVal_enc hC, ctorVal_enc hC] at e
    rw [hL.inj d cs C T Ss hd' hc xs0 ys0 hxs0 hys0 (enc_inj e)]
  · -- distinct
    intro d cs C T Ss C' T' Ss' hd hc hc' hne xs ys hxs hys e
    obtain ⟨hd', _, hC, _, _⟩ := dtC d cs C T Ss hd hc
    obtain ⟨_, _, hC', _, _⟩ := dtC d cs C' T' Ss' hd hc'
    obtain ⟨xs0, rfl, hxs0⟩ := args hC xs hxs
    obtain ⟨ys0, rfl, hys0⟩ := args hC' ys hys
    rw [ctorVal_enc hC, ctorVal_enc hC'] at e
    exact hL.distinct d cs C T Ss C' T' Ss' hd' hc hc' hne xs0 ys0 hxs0 hys0 (enc_inj e)
  · -- expand
    intro d cs C T Ss hd hc v hv ht'
    obtain ⟨hd', hdl, hC, hT, hSs⟩ := dtC d cs C T Ss hd hc
    obtain ⟨v0, hv0, rfl⟩ := dtd d cs hd' hv
    rw [const_base SP P tr Ms hT, ← List.map_singleton (f := enc), app_enc_enc] at ht'
    have e := hL.expand d cs C T Ss hd' hc v0 hv0 (enc_inj ht')
    have hmap : (Ss.map fun S => (lowModel SP P tr Ms).app ((lowModel SP P tr Ms).const S) [enc v0]) =
        (Ss.map fun S => Ms.app (Ms.const S) [v0]).map enc := by
      rw [List.map_map]
      apply List.map_congr_left
      intro S m
      simp only [Function.comp_apply]
      rw [const_base SP P tr Ms (hSs S m), ← List.map_singleton (f := enc), app_enc_enc]
    rw [hmap, ctorVal_enc hC, ← e]
  · -- smaller
    intro d cs C T Ss hd hc xs x hxs hx
    obtain ⟨hd', _, hC, _, _⟩ := dtC d cs C T Ss hd hc
    obtain ⟨xs0, rfl, hxs0⟩ := args hC xs hxs
    obtain ⟨x0, hx0, rfl⟩ := List.mem_map.mp hx
    simp only [dec_enc]
    rw [ctorVal_enc hC, dec_enc]
    exact hL.smaller d cs C T Ss hd' hc xs0 x0 hxs0 hx0
  · -- exhaust
    intro d cs hd v hv
    rw [hG.datatypes] at hd
    obtain ⟨v0, hv0, rfl⟩ := dtd d cs hd hv
    obtain ⟨ct, hct, e⟩ := hL.exhaust d cs hd v0 hv0
    refine ⟨ct, hct, ?_⟩
    obtain ⟨C, T, Ss⟩ := ct
    have hT := ((hS.dt d cs hd).2.2 C T Ss hct).2.1
    rw [const_base SP P tr Ms hT, ← List.map_singleton (f := enc), app_enc_enc, e]; rfl
  · -- store
    intro n hn s arr idx el hs hsort harr a i v j ha hi hv hj ri rj rv
    obtain ⟨hle, s0, hm⟩ := hG.stores n hn
    obtain ⟨idx0, el0, ds, hs0, hd, hdl, hds, _⟩ := hG.store _ s0 hm
    have hk : SP.sig.decls.length + (n - SP.sig.decls.length) = n := by omega
    rw [hk, hs] at hd; cases hd
    rw [hsort] at hds
    simp only [Option.some.injEq, SortDef.fn.injEq, List.cons.injEq, and_true] at hds
    obtain ⟨⟨rfl, rfl, rfl⟩, -⟩ := hds
    have hal := lt_of_get hs0
    obtain ⟨hil, hel⟩ := hS.array _ _ _ hs0
    obtain ⟨a0, ha0, rfl⟩ := dom_enc hS hG hL hal hs0 (by intro _ e; cases e) ha
    obtain ⟨i0, hi0, rfl⟩ := dom_enc_rng hS hG hL hil hi ri
    obtain ⟨v0, hv0, rfl⟩ := dom_enc_rng hS hG hL hel hv rv
    obtain ⟨j0, hj0, rfl⟩ := dom_enc_rng hS hG hL hil hj rj
    rw [const_store SP P tr Ms hle hm, app_store, ← List.map_singleton (f := enc), app_enc_enc, app_enc_enc]
    have := (hM.store _ _ _ a0 i0 v0 hs0 ha0 hi0 hv0).2 j0 hj0
    refine ⟨fun e => ?_, fun e => ?_⟩
    · rw [this.1 (enc_inj e)]
    · rw [this.2 (fun e' => e (by rw [e']))]
  · -- ext
    intro s as r f g hs hf hg hfg
    rcases Nat.lt_or_ge s SP.sig.sorts.length with hsl | hsl
    · obtain ⟨x, hx, ex⟩ := surf_sort_of hG hsl hs
      have hnb : ∀ w, x ≠ .bv w := by intro w e; subst e; simp [lowerSort] at ex
      obtain ⟨f0, hf0, rfl⟩ := dom_enc hS hG hL hsl hx hnb hf
      obtain ⟨g0, hg0, rfl⟩ := dom_enc hS hG hL hsl hx hnb hg
      have has : (∀ a ∈ as, a < SP.sig.sorts.length) ∧
          (SP.sig.sorts[s]? = some (.fn as r) ∨ ∃ i, as = [i] ∧ SP.sig.sorts[s]? = some (.array i r)) := by
        cases x with
        | fn as' r' =>
          simp only [lowerSort, SortDef.fn.injEq] at ex
          obtain ⟨h1, h2⟩ := ex; subst h1; subst h2
          exact ⟨(hS.fn s _ _ hx).1, .inl hx⟩
        | array i e =>
          simp only [lowerSort, SortDef.fn.injEq] at ex
          obtain ⟨h1, h2⟩ := ex; subst h1; subst h2
          exact ⟨by simpa using (hS.array s i e hx).1, .inr ⟨i, rfl, hx⟩⟩
        | _ => simp [lowerSort] at ex
      congr 1
      apply hM.ext s as r f0 g0 has.2 hf0 hg0
      intro ys hys
      apply enc_inj
      rw [← app_enc_enc SP P tr Ms, ← app_enc_enc SP P tr Ms]
      apply hfg
      have h2 := (forall2_base SP P tr Ms hM as (ys.map enc) has.1).mpr ⟨ys, rfl, hys⟩
      rw [hG.bvIndex]; exact h2
    · have hf' := hf
      have hg' := hg
      simp only [lowModel, Nat.not_lt.mpr hsl, if_false] at hf' hg'
      obtain ⟨k, rfl, ⟨hk, s1, hm1⟩, hd1⟩ := hf'
      obtain ⟨k', rfl, ⟨hk', s2, hm2⟩, hd2⟩ := hg'
      by_cases e : k = k'
      · rw [e]
      · exfalso
        obtain ⟨_, _, ds, _, hd, _, _, honly⟩ := hG.store _ s1 hm1
        have hk1 : SP.sig.decls.length + (k - SP.sig.decls.length) = k := by omega
        rw [hk1, hd1] at hd; cases hd
        apply honly (k' - SP.sig.decls.length) s2 (by omega) hm2
        have hk2 : SP.sig.decls.length + (k' - SP.sig.decls.length) = k' := by omega
        rw [hk2, hd2]

end

end Vik.Lower
