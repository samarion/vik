import Vik.Lower.Trace

/-!
# The lowered model of a surface model

From a model of a surface script, a model of its lowering: the same values,
with one more object for each store symbol, so that applying it is the store
of the surface model. Its minted `ite` symbols take the values of their
`ite`s.
-/

set_option linter.unusedSectionVars false

namespace Vik.Lower

open Lean.Grind Vik.Real Vik.Low Vik.Surf

variable {R U : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R]
  [OrderedRing R] [IsCharP R 0]

attribute [local instance low] Lean.Grind.Ring.intCast

/-! ## Values -/

/-- A surface value as a lowered one. -/
def enc : Val R U → Val R (U ⊕ Nat)
  | .num r => .num r
  | .bool b => .bool b
  | .obj u => .obj (.inl u)

/-- A lowered value as a surface one; a store symbol is not one. -/
def dec : Val R (U ⊕ Nat) → Val R U
  | .num r => .num r
  | .bool b => .bool b
  | .obj (.inl u) => .obj u
  | .obj (.inr _) => .bool false

@[simp] theorem dec_enc (v : Val R U) : dec (enc v) = v := by cases v <;> rfl

theorem enc_inj {v w : Val R U} (h : enc v = enc w) : v = w := by
  have := congrArg dec h; simpa using this

theorem map_dec_enc (vs : List (Val R U)) : (vs.map enc).map dec = vs := by
  simp [List.map_map, Function.comp_def]

@[simp] theorem truth_enc (v : Val R U) : (enc v).truth = v.truth := by
  cases v <;> simp [enc, Val.truth]

@[simp] theorem toR_enc (v : Val R U) : (enc v).toR = v.toR := by
  cases v <;> rfl

@[simp] theorem enc_bool (b : Bool) : enc (.bool b : Val R U) = .bool b := rfl
@[simp] theorem enc_num (r : R) : enc (.num r : Val R U) = .num r := rfl

/-! ## Surface laws -/

/-- The argument sorts of a surface symbol. -/
def SProblem.argSorts (SP : SProblem) (C : Nat) : List Nat :=
  match SP.sig.decls[C]? with
  | some s =>
    match (SP.sig.sorts[s]?).map lowerSort with
    | some (.fn as _) => as
    | _ => []
  | none => []

/-- A surface model as a lowered one over the same values, for its datatype
    laws. -/
def SModel.low (Ms : Surf.Model R U) : Low.Model R U := ⟨⟨Ms.const, Ms.app⟩, Ms.dom⟩

/-- What a model of a surface script satisfies: its sorts and symbols, and the
    laws of datatypes, as for lowered problems (`Problem.Laws`). -/
structure SProblem.Laws (SP : SProblem) (Ms : Surf.Model R U) (size : Val R U → Nat) : Prop where
  sound : Ms.Sound SP.sig
  /-- The definitions hold. -/
  defs : ∀ d ∈ SP.defs, d.Holds SP.sig Ms
  sel : ∀ d cs C T Ss, (d, cs) ∈ SP.datatypes → (C, T, Ss) ∈ cs →
    ∀ xs (i : Nat) S x, Forall2 Ms.dom (SP.argSorts C) xs → Ss[i]? = some S → xs[i]? = some x →
      Ms.app (Ms.const S) [ctorVal (SModel.low Ms) C xs] = x
  test : ∀ d cs C T Ss, (d, cs) ∈ SP.datatypes → (C, T, Ss) ∈ cs →
    ∀ xs, Forall2 Ms.dom (SP.argSorts C) xs → Ms.app (Ms.const T) [ctorVal (SModel.low Ms) C xs] = .bool true
  testOther : ∀ d cs C T Ss C' T' Ss', (d, cs) ∈ SP.datatypes → (C, T, Ss) ∈ cs → (C', T', Ss') ∈ cs →
    C ≠ C' → ∀ ys, Forall2 Ms.dom (SP.argSorts C') ys →
      Ms.app (Ms.const T) [ctorVal (SModel.low Ms) C' ys] ≠ .bool true
  inj : ∀ d cs C T Ss, (d, cs) ∈ SP.datatypes → (C, T, Ss) ∈ cs →
    ∀ xs ys, Forall2 Ms.dom (SP.argSorts C) xs → Forall2 Ms.dom (SP.argSorts C) ys →
      ctorVal (SModel.low Ms) C xs = ctorVal (SModel.low Ms) C ys → xs = ys
  distinct : ∀ d cs C T Ss C' T' Ss', (d, cs) ∈ SP.datatypes → (C, T, Ss) ∈ cs → (C', T', Ss') ∈ cs →
    C ≠ C' → ∀ xs ys, Forall2 Ms.dom (SP.argSorts C) xs → Forall2 Ms.dom (SP.argSorts C') ys →
      ctorVal (SModel.low Ms) C xs ≠ ctorVal (SModel.low Ms) C' ys
  expand : ∀ d cs C T Ss, (d, cs) ∈ SP.datatypes → (C, T, Ss) ∈ cs →
    ∀ v, Ms.dom d v → Ms.app (Ms.const T) [v] = .bool true →
      v = ctorVal (SModel.low Ms) C (Ss.map fun S => Ms.app (Ms.const S) [v])
  smaller : ∀ d cs C T Ss, (d, cs) ∈ SP.datatypes → (C, T, Ss) ∈ cs →
    ∀ xs x, Forall2 Ms.dom (SP.argSorts C) xs → x ∈ xs → size x < size (ctorVal (SModel.low Ms) C xs)
  exhaust : ∀ d cs, (d, cs) ∈ SP.datatypes → ∀ v, Ms.dom d v →
    ∃ ct ∈ cs, Ms.app (Ms.const ct.2.1) [v] = .bool true

/-! ## The sorts of bit-vectors -/

theorem lookup_filterMap_range {β : Type} (g : Nat → Option β) : ∀ (n s : Nat),
    ((List.range n).filterMap (fun t => (g t).map (t, ·))).lookup s = if s < n then g s else none
  | 0, s => by simp
  | n + 1, s => by
    rw [List.range_succ, List.filterMap_append]
    have ih := lookup_filterMap_range g n s
    cases e : g n with
    | none =>
      simp only [e, Option.map_none, List.filterMap_cons_none, List.filterMap_nil, List.append_nil, ih]
      by_cases h : s < n
      · simp [h, show s < n + 1 by omega]
      · by_cases h' : s = n
        · subst h'; simp [e]
        · simp [h, show ¬ s < n + 1 by omega]
    | some b =>
      simp only [List.filterMap_cons, e, Option.map_some, List.filterMap_nil]
      rw [List.lookup_append, ih]
      by_cases h : s < n
      · simp [h, show s < n + 1 by omega]
        cases g s <;> simp <;> omega
      · by_cases h' : s = n
        · subst h'; simp [e, List.lookup]
        · simp [h, show ¬ s < n + 1 by omega, List.lookup, show (s == n) = false by simpa using h']

theorem lookup_bvIndex (SP : SProblem) (s : Nat) : SP.bvIndex.lookup s = SP.sortWidth s := by
  unfold SProblem.bvIndex
  rw [lookup_filterMap_range]
  split
  · rfl
  · rename_i h
    unfold SProblem.sortWidth
    rw [List.getElem?_eq_none (by omega)]

theorem sortWidth_eq {SP : SProblem} {s w : Nat} : SP.sortWidth s = some w ↔ SP.sig.sorts[s]? = some (.bv w) := by
  unfold SProblem.sortWidth
  split
  · rename_i w' h; rw [h]; simp
  · rename_i h; simp only [reduceCtorEq, false_iff]; intro e; exact h w e

/-! ## The lowered model -/

/-- The value of a rule symbol only depends on its arguments. -/
theorem Rule.ival_congr (r : Rule) (j : Nat) {ι ι' : Nat → Int} {τ τ' : Nat → Bool}
    (hι : ∀ x ∈ r.args, ι x = ι' x) (hτ : ∀ x ∈ r.args, τ x = τ' x) : r.ival ι τ j = r.ival ι' τ' j := by
  cases r <;> simp only [Rule.args, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at hι hτ <;>
    cases j <;> simp only [Rule.ival, hι, hτ]

theorem pow_two_pos (w : Nat) : (0 : Int) < 2 ^ w := Int.pow_pos (by decide)

theorem one_lt_pow_two {w : Nat} (h : 0 < w) : (1 : Int) < 2 ^ w := by
  obtain ⟨v, rfl⟩ : ∃ v, w = v + 1 := ⟨w - 1, by omega⟩
  rw [Int.pow_succ]; have := pow_two_pos v; omega

/-- A symbol `bvOut` marks is in the range of its width. -/
theorem Rule.bvOut_range {r : Rule} {j w : Nat} (h : r.bvOut j w = true) (ι : Nat → Int) (τ : Nat → Bool) :
    0 ≤ r.ival ι τ j ∧ r.ival ι τ j < 2 ^ w := by
  have hm : ∀ x : Int, 0 ≤ x % 2 ^ w ∧ x % 2 ^ w < 2 ^ w := fun x =>
    ⟨Int.emod_nonneg x (by have := pow_two_pos w; omega), Int.emod_lt_of_pos x (pow_two_pos w)⟩
  cases r with
  | modulo v w' lo hi =>
    cases j with
    | zero => simp only [Rule.bvOut, beq_iff_eq] at h; subst h; exact hm _
    | succ j => simp [Rule.bvOut] at h
  | int2bv t w' =>
    cases j with
    | zero => simp only [Rule.bvOut, beq_iff_eq] at h; subst h; exact hm _
    | succ j => simp [Rule.bvOut] at h
  | udiv a b w' =>
    simp only [Rule.bvOut, beq_iff_eq] at h; subst h
    cases j <;> exact hm _
  | bits t w' =>
    simp only [Rule.bvOut, decide_eq_true_eq] at h
    have := bit_range (ι t) j; have := one_lt_pow_two h
    simp only [Rule.ival]; omega
  | smodz a c w' =>
    simp only [Rule.bvOut, decide_eq_true_eq] at h
    have := one_lt_pow_two h
    simp only [Rule.ival, smodzVal]
    split <;> omega
  | cases | divide | sdivide => cases j <;> simp [Rule.bvOut] at h

/-- The value of the symbol of a real rule, `ϱ` the reals of its arguments. -/
noncomputable def RRule.val (ϱ : Nat → R) : RRule → R
  | .rat p q => (p : R) / ((q : Int) : R)
  | .ratmul p q t => (p : R) / ((q : Int) : R) * ϱ t
  | .floor t => ((floorOf (ϱ t) : Int) : R)

theorem RRule.val_congr (r : RRule) {ϱ ϱ' : Nat → R} (h : ∀ x ∈ r.args, ϱ x = ϱ' x) : r.val ϱ = r.val ϱ' := by
  cases r <;> simp only [RRule.args, List.mem_cons, List.mem_nil_iff, or_false, forall_eq] at h <;>
    simp only [RRule.val, h]

/-- Whether the lowered model computes the value of a minted symbol. -/
def Mint.computed : Mint → Bool
  | .rule _ _ | .real _ => true
  | _ => false

section
variable (SP : SProblem) (P : Problem) (tr : Trace) (Ms : Surf.Model R U)

/-- Whether `k` is a minted store symbol. -/
def isStore (k : Nat) : Prop :=
  SP.sig.decls.length ≤ k ∧ ∃ s, tr.mints[k - SP.sig.decls.length]? = some (.store s)

/-- The applications of the lowered model: a store symbol stores, every
    other value applies as in the surface model. -/
noncomputable def lowApp (f : Val R (U ⊕ Nat)) (xs : List (Val R (U ⊕ Nat))) : Val R (U ⊕ Nat) :=
  match f, xs with
  | .obj (.inr _), [a, i, v] => enc (Ms.store (dec a) (dec i) (dec v))
  | .obj (.inr _), _ => .bool false
  | f, xs => enc (Ms.app (dec f) (xs.map dec))

/-- The symbols of the lowered model, but those of rules. -/
noncomputable def baseConst (k : Nat) : Val R (U ⊕ Nat) :=
  if k < SP.sig.decls.length then enc (Ms.const k)
  else
    match tr.mints[k - SP.sig.decls.length]? with
    | some (.ite i) => enc (Surf.val Ms.toInterp SP.nodes i)
    | some (.store _) => .obj (.inr k)
    | some (.witness s) => if SP.sig.sorts[s]? = some .bool then .bool false else .num 0
    | some (.pick i) => enc (Surf.val Ms.toInterp SP.nodes i)
    | _ => .bool false

/-- The symbols of the lowered model once the first `m` minted symbols have
    their values: a rule symbol takes the value of its rule on its arguments,
    which only depend on the symbols minted before it. -/
noncomputable def ruleConst : Nat → Nat → Val R (U ⊕ Nat)
  | 0 => baseConst SP tr Ms
  | m + 1 => fun k =>
    if k = SP.sig.decls.length + m then
      match tr.mints[m]? with
      | some (.rule r j) =>
        let I : Low.Interp R (U ⊕ Nat) := ⟨ruleConst m, lowApp Ms⟩
        .num ((Rule.ival (fun x => intOf (Low.val I P.nodes x)) (fun x => (Low.val I P.nodes x).truth) r j : Int) : R)
      | some (.real r) =>
        let I : Low.Interp R (U ⊕ Nat) := ⟨ruleConst m, lowApp Ms⟩
        .num (r.val fun x => (Low.val I P.nodes x).toR)
      | _ => ruleConst m k
    else ruleConst m k

noncomputable def lowModel : Low.Model R (U ⊕ Nat) where
  const := ruleConst SP P tr Ms tr.mints.length
  app := lowApp Ms
  dom s v :=
    if s < SP.sig.sorts.length then
      if (SP.sortWidth s).isSome then ∃ k : Int, v = .num (k : R)
      else ∃ w, Ms.dom s w ∧ v = enc w
    else ∃ k, v = .obj (.inr k) ∧ isStore SP tr k ∧ P.sig.decls[k]? = some s

theorem ruleConst_succ_ne {m k : Nat} (h : k ≠ SP.sig.decls.length + m) :
    ruleConst SP P tr Ms (m + 1) k = ruleConst SP P tr Ms m k := by
  simp [ruleConst, h]

/-- The symbols that no rule mints keep their base values. -/
theorem ruleConst_base {k : Nat}
    (h : ∀ mt, SP.sig.decls.length ≤ k → tr.mints[k - SP.sig.decls.length]? = some mt → mt.computed = false) :
    ∀ m, ruleConst SP P tr Ms m k = baseConst SP tr Ms k
  | 0 => rfl
  | m + 1 => by
    by_cases e : k = SP.sig.decls.length + m
    · have hm : tr.mints[m]? = tr.mints[k - SP.sig.decls.length]? := by rw [e]; simp
      simp only [ruleConst, e, if_true]
      rw [← e, hm]
      split
      · rename_i r j hr; cases h _ (by omega) hr
      · rename_i r hr; cases h _ (by omega) hr
      · exact ruleConst_base h m
    · rw [ruleConst_succ_ne SP P tr Ms e]; exact ruleConst_base h m

/-- A minted symbol keeps its value once it has one. -/
theorem ruleConst_stable {m' : Nat} : ∀ M, m' < M →
    ruleConst SP P tr Ms M (SP.sig.decls.length + m') = ruleConst SP P tr Ms (m' + 1) (SP.sig.decls.length + m')
  | 0, h => absurd h (Nat.not_lt_zero _)
  | M + 1, h => by
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | rfl
    · rw [ruleConst_succ_ne SP P tr Ms (by omega)]; exact ruleConst_stable M h
    · rfl

theorem app_enc (f : Val R U) (xs : List (Val R (U ⊕ Nat))) :
    (lowModel SP P tr Ms).app (enc f) xs = enc (Ms.app f (xs.map dec)) := by
  cases f <;> rfl

theorem app_enc_enc (f : Val R U) (xs : List (Val R U)) :
    (lowModel SP P tr Ms).app (enc f) (xs.map enc) = enc (Ms.app f xs) := by
  rw [app_enc, map_dec_enc]

theorem const_base {k : Nat} (h : k < SP.sig.decls.length) :
    (lowModel SP P tr Ms).const k = enc (Ms.const k) := by
  simp only [lowModel]
  rw [ruleConst_base SP P tr Ms (fun _ h' => absurd h' (by omega))]
  simp [baseConst, h]

theorem const_ite {k i : Nat} (h : SP.sig.decls.length ≤ k) (hm : tr.mints[k - SP.sig.decls.length]? = some (.ite i)) :
    (lowModel SP P tr Ms).const k = enc (Surf.val Ms.toInterp SP.nodes i) := by
  simp only [lowModel]
  rw [ruleConst_base SP P tr Ms (fun _ _ e => by rw [hm] at e; cases e; rfl)]
  simp [baseConst, hm, Nat.not_lt.mpr h]

theorem const_store {k s : Nat} (h : SP.sig.decls.length ≤ k) (hm : tr.mints[k - SP.sig.decls.length]? = some (.store s)) :
    (lowModel SP P tr Ms).const k = .obj (.inr k) := by
  simp only [lowModel]
  rw [ruleConst_base SP P tr Ms (fun _ _ e => by rw [hm] at e; cases e; rfl)]
  simp [baseConst, hm, Nat.not_lt.mpr h]

theorem const_pick {k i : Nat} (h : SP.sig.decls.length ≤ k)
    (hm : tr.mints[k - SP.sig.decls.length]? = some (.pick i)) :
    (lowModel SP P tr Ms).const k = enc (Surf.val Ms.toInterp SP.nodes i) := by
  simp only [lowModel]
  rw [ruleConst_base SP P tr Ms (fun _ _ e => by rw [hm] at e; cases e; rfl)]
  simp [baseConst, hm, Nat.not_lt.mpr h]

theorem const_witness {k s : Nat} (h : SP.sig.decls.length ≤ k)
    (hm : tr.mints[k - SP.sig.decls.length]? = some (.witness s)) :
    (lowModel SP P tr Ms).const k = if SP.sig.sorts[s]? = some .bool then .bool false else .num 0 := by
  simp only [lowModel]
  rw [ruleConst_base SP P tr Ms (fun _ _ e => by rw [hm] at e; cases e; rfl)]
  simp [baseConst, hm, Nat.not_lt.mpr h]

/-- The minted symbols agree in the model of the first `m` symbols and in the
    lowered model on the nodes of depth at most `m`. -/
theorem agree_upto (hw : Low.wellFormed P.nodes = true) {m x : Nat} (hm : m ≤ tr.mints.length)
    (hx : depthOf (depths (tr.rank SP) P.nodes) x ≤ m) :
    Low.val (⟨ruleConst SP P tr Ms m, lowApp Ms⟩ : Low.Interp R (U ⊕ Nat)) P.nodes x =
      Low.val (⟨ruleConst SP P tr Ms tr.mints.length, lowApp Ms⟩ : Low.Interp R (U ⊕ Nat)) P.nodes x := by
  refine val_agree (R := R) (U := U ⊕ Nat) (I := ⟨ruleConst SP P tr Ms m, lowApp Ms⟩)
    (I' := ⟨ruleConst SP P tr Ms tr.mints.length, lowApp Ms⟩) hw rfl (fun n hn => ?_) x hx
  show ruleConst SP P tr Ms m n = ruleConst SP P tr Ms tr.mints.length n
  by_cases hr : ∃ mt, SP.sig.decls.length ≤ n ∧ tr.mints[n - SP.sig.decls.length]? = some mt ∧ mt.computed = true
  · obtain ⟨mt, hle, hr', hc⟩ := hr
    have hrank : tr.rank SP n = n - SP.sig.decls.length + 1 := by
      cases mt <;> simp_all [Trace.rank, Mint.computed]
    have hlt' : n - SP.sig.decls.length < tr.mints.length := (List.getElem?_eq_some_iff.mp hr').1
    have e : n = SP.sig.decls.length + (n - SP.sig.decls.length) := by omega
    rw [e, ruleConst_stable SP P tr Ms _ (by omega), ruleConst_stable SP P tr Ms _ hlt']
  · have hb : ∀ mt, SP.sig.decls.length ≤ n → tr.mints[n - SP.sig.decls.length]? = some mt → mt.computed = false :=
      fun mt h e => by cases hc : mt.computed; rfl; exact absurd ⟨mt, h, e, hc⟩ hr
    rw [ruleConst_base SP P tr Ms hb, ruleConst_base SP P tr Ms hb]

/-- A rule symbol takes the value of its rule on the values of its arguments
    in the lowered model, when its arguments only depend on the symbols
    minted before it. -/
theorem const_rule (hw : Low.wellFormed P.nodes = true) {m : Nat} {r : Rule} {j : Nat}
    (hm : tr.mints[m]? = some (.rule r j))
    (hargs : ∀ x ∈ r.args, depthOf (depths (tr.rank SP) P.nodes) x ≤ m) :
    (lowModel SP P tr Ms).const (SP.sig.decls.length + m) =
      .num ((Rule.ival (fun x => intOf (Low.val (lowModel SP P tr Ms).toInterp P.nodes x))
        (fun x => (Low.val (lowModel SP P tr Ms).toInterp P.nodes x).truth) r j : Int) : R) := by
  have hlt : m < tr.mints.length := (List.getElem?_eq_some_iff.mp hm).1
  simp only [lowModel]
  rw [ruleConst_stable SP P tr Ms _ hlt]
  simp only [ruleConst, if_true, hm]
  have agree := fun x hx => agree_upto SP P tr Ms hw (Nat.le_of_lt hlt) (hargs x hx)
  rw [Rule.ival_congr r j (fun x hx => by rw [agree x hx]) (fun x hx => by rw [agree x hx])]

/-- The symbol of a real rule takes its value on the values of its arguments
    in the lowered model. -/
theorem const_real (hw : Low.wellFormed P.nodes = true) {m : Nat} {r : RRule}
    (hm : tr.mints[m]? = some (.real r))
    (hargs : ∀ x ∈ r.args, depthOf (depths (tr.rank SP) P.nodes) x ≤ m) :
    (lowModel SP P tr Ms).const (SP.sig.decls.length + m) =
      .num (r.val fun x => (Low.val (lowModel SP P tr Ms).toInterp P.nodes x).toR) := by
  have hlt : m < tr.mints.length := (List.getElem?_eq_some_iff.mp hm).1
  simp only [lowModel]
  rw [ruleConst_stable SP P tr Ms _ hlt]
  simp only [ruleConst, if_true, hm]
  have agree := fun x hx => agree_upto SP P tr Ms hw (Nat.le_of_lt hlt) (hargs x hx)
  rw [RRule.val_congr r (fun x hx => by rw [agree x hx])]

theorem app_store (k : Nat) (a i v : Val R U) :
    (lowModel SP P tr Ms).app (.obj (.inr k)) [enc a, enc i, enc v] = enc (Ms.store a i v) := by
  simp [lowModel, lowApp]

theorem dom_base {s : Nat} (hs : s < SP.sig.sorts.length) (hb : SP.sortWidth s = none) (v : Val R (U ⊕ Nat)) :
    (lowModel SP P tr Ms).dom s v ↔ ∃ w, Ms.dom s w ∧ v = enc w := by
  simp [lowModel, hs, hb]

theorem dom_bv {s w : Nat} (hs : s < SP.sig.sorts.length) (hb : SP.sortWidth s = some w) (v : Val R (U ⊕ Nat)) :
    (lowModel SP P tr Ms).dom s v ↔ ∃ k : Int, v = .num (k : R) := by
  simp [lowModel, hs, hb]

/-- A lowered value of a sort of the script, in its range, is a surface one. -/
theorem rdom (hM : Ms.Sound SP.sig) {s : Nat} (hs : s < SP.sig.sorts.length) (v : Val R (U ⊕ Nat)) :
    ((lowModel SP P tr Ms).dom s v ∧ inRange SP.bvIndex s v) ↔ ∃ w, Ms.dom s w ∧ v = enc w := by
  unfold inRange
  rw [lookup_bvIndex]
  cases hb : SP.sortWidth s with
  | none =>
    rw [dom_base SP P tr Ms hs hb]
    simp
  | some w0 =>
    rw [dom_bv SP P tr Ms hs hb]
    have hw0 := sortWidth_eq.mp hb
    constructor
    · rintro ⟨-, h⟩
      obtain ⟨k, rfl, h0, h1⟩ := h w0 rfl
      exact ⟨.num (k : R), (hM.bv s w0 _ hw0).mpr ⟨k, rfl, h0, h1⟩, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨k, rfl, h0, h1⟩ := (hM.bv s w0 _ hw0).mp hw
      refine ⟨⟨k, rfl⟩, fun w' e => ?_⟩
      cases e
      exact ⟨k, rfl, h0, h1⟩

theorem forall2_base (hM : Ms.Sound SP.sig) : ∀ (as : List Nat) (xs : List (Val R (U ⊕ Nat))),
    (∀ a ∈ as, a < SP.sig.sorts.length) →
    (Forall2 (fun a x => (lowModel SP P tr Ms).dom a x ∧ inRange SP.bvIndex a x) as xs ↔
      ∃ ys, xs = ys.map enc ∧ Forall2 Ms.dom as ys)
  | [], [], _ => by simp [Forall2]
  | [], _ :: _, _ => by
    simp only [Forall2, false_iff, _root_.not_exists, _root_.not_and]
    intro ys h; cases ys <;> simp_all [Forall2]
  | _ :: _, [], _ => by
    simp only [Forall2, false_iff, _root_.not_exists, _root_.not_and]
    intro ys h; cases ys <;> simp_all [Forall2]
  | a :: as, x :: xs, h => by
    simp only [Forall2]
    rw [rdom SP P tr Ms hM (h a (by simp)), forall2_base hM as xs (fun b m => h b (by simp [m]))]
    constructor
    · rintro ⟨⟨w, hw, rfl⟩, ys, rfl, hys⟩
      exact ⟨w :: ys, rfl, hw, hys⟩
    · rintro ⟨ys, hx, hys⟩
      cases ys with
      | nil => cases hx
      | cons y ys =>
        simp only [List.map_cons, List.cons.injEq] at hx
        exact ⟨⟨y, hys.1, hx.1⟩, ys, hx.2, hys.2⟩

end

end Vik.Lower
