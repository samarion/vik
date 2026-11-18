import Vik.Lower.Bv

/-!
# The facts of rules hold

A rule symbol takes the value of its rule on its arguments (`const_rule`).
The intervals the trace computes for the lowered nodes hold (`ivAt_sound`),
and with them the bounds under which the rules are checked; under those
bounds, each fact of a rule holds of the values of its symbols
(`ruleFact_holds`).
-/

set_option linter.unusedSectionVars false

namespace Vik.Lower

open Lean.Grind Vik.Real Vik.Low Vik.Surf

variable {R U : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R]
  [OrderedRing R] [IsCharP R 0]

attribute [local instance low] Lean.Grind.Ring.intCast

/-! ## Integers -/

theorem two_pow_pred {w : Nat} (hw : 0 < w) : (2 : Int) ^ w = 2 * 2 ^ (w - 1) := by
  obtain ⟨v, rfl⟩ : ∃ v, w = v + 1 := ⟨w - 1, by omega⟩
  rw [Int.pow_succ, Nat.add_sub_cancel]; grind

theorem two_pow_pos (w : Nat) : (0 : Int) < 2 ^ w := Int.pow_pos (by decide)

theorem signedI_bounds {w : Nat} (hw : 0 < w) {t : Int} (h0 : 0 ≤ t) (h1 : t ≤ 2 ^ w - 1) :
    -(2 ^ (w - 1)) ≤ signedI w t ∧ signedI w t ≤ 2 ^ (w - 1) - 1 := by
  have := two_pow_pred hw
  unfold signedI; split <;> omega

theorem ediv_lower {a h d : Int} (hd : 0 < d) (ha : -h ≤ a) : -(h / d) - 1 ≤ a / d := by
  rw [Int.le_ediv_iff_mul_le hd]
  have := Int.lt_ediv_add_one_mul_self h hd
  grind

theorem ediv_bounds {a lo hi d : Int} (hd : 0 < d) (h0 : lo * d ≤ a) (h1 : a ≤ (hi + 1) * d - 1) :
    lo ≤ a / d ∧ a / d ≤ hi := by
  constructor
  · exact (Int.le_ediv_iff_mul_le hd).mpr h0
  · have := (Int.ediv_lt_iff_lt_mul hd (a := a) (b := hi + 1)).mpr (by omega)
    omega

theorem emod_bounds (a : Int) {d : Int} (hd : 0 < d) : 0 ≤ a % d ∧ a % d ≤ d - 1 :=
  ⟨Int.emod_nonneg a (by omega), by have := Int.emod_lt_of_pos a hd; omega⟩

theorem tdiv_bounds {a h d : Int} (hd : 0 < d) (h0 : -h ≤ a) (h1 : a ≤ h - 1) (hh : 0 ≤ h) :
    -(h / d) ≤ a.tdiv d ∧ a.tdiv d ≤ (h - 1) / d := by
  by_cases ha : 0 ≤ a
  · rw [Int.tdiv_eq_ediv_of_nonneg ha]
    exact ⟨by have := Int.ediv_nonneg ha (Int.le_of_lt hd); have := Int.ediv_nonneg hh (Int.le_of_lt hd); omega,
      Int.ediv_le_ediv hd h1⟩
  · have e : a = -(-a) := by omega
    rw [e, Int.neg_tdiv, Int.tdiv_eq_ediv_of_nonneg (by omega)]
    have := Int.ediv_le_ediv hd (show -a ≤ h by omega)
    have := Int.ediv_nonneg (show 0 ≤ -a by omega) (Int.le_of_lt hd)
    have := Int.ediv_nonneg hh (Int.le_of_lt hd)
    have := Int.ediv_nonneg (show 0 ≤ h - 1 by omega) (Int.le_of_lt hd)
    omega

theorem tmod_bounds (a : Int) {d : Int} (hd : 0 < d) :
    -(d - 1) ≤ a.tmod d ∧ a.tmod d ≤ d - 1 ∧ (0 ≤ a → 0 ≤ a.tmod d) ∧ (a < 0 → a.tmod d ≤ 0) := by
  by_cases ha : 0 ≤ a
  · have := Int.tmod_nonneg d ha
    have := Int.tmod_lt_of_pos a hd
    refine ⟨by omega, by omega, fun _ => by omega, fun h => absurd h (by omega)⟩
  · have e : a = -(-a) := by omega
    rw [e, Int.neg_tmod]
    have := Int.tmod_nonneg d (show 0 ≤ -a by omega)
    have := Int.tmod_lt_of_pos (-a) hd
    refine ⟨by omega, by omega, fun h => absurd h (by omega), fun _ => by omega⟩

theorem smodzVal_bounds (a c : Int) (w : Nat) : 0 ≤ smodzVal a c w ∧ smodzVal a c w ≤ 1 := by
  unfold smodzVal; dsimp only; split <;> omega

/-! ## Lists -/

theorem getElem?_idxOf {α : Type} [DecidableEq α] :
    ∀ (l : List α) (a : α), l.idxOf a < l.length → l[l.idxOf a]? = some a
  | [], _, h => absurd h (by simp)
  | b :: l, a, h => by
    by_cases e : b = a
    · subst e; simp [List.idxOf_cons_self]
    · have ei : (b :: l).idxOf a = l.idxOf a + 1 := by
        rw [List.idxOf_cons]; simp [show (b == a) = false from by simpa using e]
      rw [ei] at h ⊢
      simp only [List.getElem?_cons_succ]
      exact getElem?_idxOf l a (by simp at h; omega)

theorem mapM_get {α β : Type} (f : α → Option β) : ∀ (l : List α) (ks : List β), l.mapM f = some ks →
    ∀ i (hi : i < l.length), ∃ b, ks[i]? = some b ∧ f l[i] = some b
  | [], ks, h, i, hi => absurd hi (by simp)
  | a :: l, ks, h, i, hi => by
    simp only [List.mapM_cons] at h
    cases ha : f a with
    | none => simp [ha] at h
    | some b =>
      cases hl : l.mapM f with
      | none => simp [ha, hl] at h
      | some bs =>
        simp [ha, hl] at h; subst h
        cases i with
        | zero => exact ⟨b, rfl, ha⟩
        | succ i => exact mapM_get f l bs hl i (by simp at hi; omega)

/-! ## Intervals of linear combinations -/

/-- Node `x` takes an integer value within `p`. -/
def IvOk {V : Type} (ρ : Nat → Val R V) (x : Nat) (p : Int × Int) : Prop :=
  ∃ k : Int, ρ x = .num (k : R) ∧ p.1 ≤ k ∧ k ≤ p.2

theorem linIv_sound {V : Type} (ρ : Nat → Val R V) (leaf : Nat → Option (Int × Int))
    (hleaf : ∀ u p, leaf u = some p → IvOk ρ u p) :
    ∀ (f : Lia.Form) (p : Int × Int), linIv leaf f = some p →
      ∃ k : Int, Lia.eval (fun u => (ρ u).toR) f = (k : R) ∧ p.1 ≤ k ∧ k ≤ p.2
  | [], p, h => by
    simp only [linIv, Option.some.injEq] at h; subst h
    exact ⟨0, by simp [Lia.eval, Ring.intCast_zero], Int.le_refl _, Int.le_refl _⟩
  | (u, a) :: f, p, h => by
    unfold linIv at h
    split at h
    · rename_i ha
      split at h
      · rename_i l hi L H hu hf
        obtain ⟨ku, eu, hu0, hu1⟩ := hleaf u _ hu
        obtain ⟨K, eK, hK0, hK1⟩ := linIv_sound ρ leaf hleaf f _ hf
        simp only at hu0 hu1 hK0 hK1
        refine ⟨a.num * ku + K, ?_, ?_⟩
        · simp only [Lia.eval, eu, toR_num, eK, Lia.rat_den_one ha, Ring.intCast_add, Ring.intCast_mul]
        · split at h
          · rename_i hn
            simp only [Option.some.injEq] at h; subst h
            exact ⟨by have := Int.mul_le_mul_of_nonneg_left hu0 hn; omega,
              by have := Int.mul_le_mul_of_nonneg_left hu1 hn; omega⟩
          · rename_i hn
            simp only [Option.some.injEq] at h; subst h
            have hn' : a.num ≤ 0 := by omega
            exact ⟨by have := Int.mul_le_mul_of_nonpos_left hn' hu1; omega,
              by have := Int.mul_le_mul_of_nonpos_left hn' hu0; omega⟩
      · cases h
    · cases h

/-! ## Shapes of facts -/

section
variable {V : Type} (I : Low.Interp R V) (ρ' : Nat → Val R V)

theorem ev_num0 (c : Int) : ((Shape.num [] c).ev I ρ').toR = (c : R) := by
  simp only [Shape.ev, Lia.eval, toR_num]; grind

theorem ev_num1 {x : Nat} {X : Int} (hx : ρ' x = .num (X : R)) (c : Int) :
    ((Shape.num [(x, 1)] c).ev I ρ').toR = ((X + c : Int) : R) := by
  simp only [Shape.ev, Lia.eval, toR_num, hx, rat_one, Ring.intCast_add]; grind

theorem ev_num2 {x y : Nat} {X Y : Int} (hx : ρ' x = .num (X : R)) (hy : ρ' y = .num (Y : R)) (a b c : Int) :
    ((Shape.num [(x, (a : Rat)), (y, (b : Rat))] c).ev I ρ').toR = ((a * X + b * Y + c : Int) : R) := by
  simp only [Shape.ev, Lia.eval, toR_num, hx, hy, Lia.rat_intCast, Ring.intCast_add, Ring.intCast_mul]; grind

theorem ev_num2' {x y : Nat} {X Y : Int} (hx : ρ' x = .num (X : R)) (hy : ρ' y = .num (Y : R)) (a b c : Int)
    {a' b' : Rat} (ha : a' = (a : Rat)) (hb : b' = (b : Rat)) :
    ((Shape.num [(x, a'), (y, b')] c).ev I ρ').toR = ((a * X + b * Y + c : Int) : R) := by
  subst ha hb; exact ev_num2 I ρ' hx hy a b c

theorem ev_same_num {x : Nat} {X : Int} (hx : ρ' x = .num (X : R)) : ((Shape.same x).ev I ρ').toR = (X : R) := by
  simp only [Shape.ev, hx, toR_num]

theorem eqI_int {a b : Shape} {A B : Int} (ha : (a.ev I ρ').toR = (A : R)) (hb : (b.ev I ρ').toR = (B : R)) :
    ((eqI a b).ev I ρ').truth = decide (A = B) := by
  simp only [eqI, Shape.ev, Shape.allTrue, truth_bool, Bool.and_true]
  rw [ha, hb]
  by_cases h : A = B
  · subst h; simp [Std.le_refl]
  · simp only [h, decide_false]
    rcases Int.lt_or_gt_of_ne h with h' | h'
    · have : ¬ ((B : R) ≤ (A : R)) := fun e => absurd (cast_le_iff.mp e) (by omega)
      simp [this]
    · have : ¬ ((A : R) ≤ (B : R)) := fun e => absurd (cast_le_iff.mp e) (by omega)
      simp [this]

theorem le_int_holds {a b : Shape} {A B : Int} (ha : (a.ev I ρ').toR = (A : R)) (hb : (b.ev I ρ').toR = (B : R))
    (h : A ≤ B) : ((Shape.le a b).ev I ρ').truth = true := by
  simp only [Shape.ev, truth_bool, decide_eq_true_eq]
  rw [ha, hb]; exact cast_le_iff.mpr h

theorem eqI_holds {a b : Shape} {A B : Int} (ha : (a.ev I ρ').toR = (A : R)) (hb : (b.ev I ρ').toR = (B : R))
    (h : A = B) : ((eqI a b).ev I ρ').truth = true := by
  rw [eqI_int I ρ' ha hb]; simpa using h

theorem le_holds {a b : Shape} {A B : Int} (ha : (a.ev I ρ').toR = (A : R)) (hb : (b.ev I ρ').toR = (B : R))
    (h : A ≤ B) : ((Shape.le a b).ev I ρ').truth = true := by
  simp only [Shape.ev, truth_bool, ha, hb, decide_eq_true_eq]; exact cast_le_iff.mpr h

theorem and2_holds {a b : Shape} (ha : (a.ev I ρ').truth = true) (hb : (b.ev I ρ').truth = true) :
    ((Shape.and [a, b]).ev I ρ').truth = true := by
  simp only [Shape.ev, Shape.allTrue, truth_bool, ha, hb, Bool.and_true]

theorem implies_of_right {a b : Shape} (h : (b.ev I ρ').truth = true) :
    ((Shape.implies a b).ev I ρ').truth = true := by
  simp only [Shape.ev, truth_bool, h, Bool.or_true]

theorem implies_of_left {a b : Shape} (h : (a.ev I ρ').truth = false) :
    ((Shape.implies a b).ev I ρ').truth = true := by
  simp only [Shape.ev, truth_bool, h, Bool.not_false, Bool.true_or]

theorem intS_holds {k : Nat} {K lo hi : Int} (hk : ρ' k = .num (K : R)) (h0 : lo ≤ K) (h1 : K ≤ hi) :
    ∀ s ∈ intS k lo hi, (s.ev I ρ').truth = true := by
  intro s hs
  simp only [intS, List.mem_cons, List.mem_nil_iff, or_false] at hs
  have z : ∀ c : Int, (0 : R) + (c : R) = (c : R) := fun c => by grind
  rcases hs with rfl | rfl
  · simp only [Shape.ev, Lia.eval, hk, toR_num, z, truth_bool, decide_eq_true_eq]
    exact cast_le_iff.mpr h0
  · simp only [Shape.ev, Lia.eval, hk, toR_num, z, truth_bool, decide_eq_true_eq]
    exact cast_le_iff.mpr h1

theorem negS_int {P : Problem} (hwP : Low.wellFormed P.nodes = true) {t w : Nat} {K : Int}
    (hρ : ρ' = Low.val I P.nodes) (ht : ρ' t = .num (K : R)) :
    ((negS P t w).ev I ρ').truth = decide (2 ^ (w - 1) ≤ K) := by
  have z : ∀ c : Int, (0 : R) + (c : R) = (c : R) := fun c => by grind
  unfold negS
  split
  · rename_i v hv
    have hval := Low.val_num (I := I) hwP ((Tab.at_eq _ _).symm.trans hv)
    rw [← hρ, ht] at hval
    have hv' : K = v := (num_int_eq_iff (U := V)).mp hval
    subst hv'
    split <;> simp_all [Shape.ev, truth_bool]
  · simp only [Shape.ev, Lia.eval, truth_bool]
    apply bool_eq_decide
    classical
    rw [decide_eq_true_iff, ht, toR_num, toR_num, z]
    exact cast_le_iff

end

/-- Shapes whose values are Booleans. -/
def boolShape : Shape → Bool
  | .le .. | .lt .. | .and _ | .or _ | .implies .. => true
  | _ => false

theorem ev_of_boolShape {V : Type} (I : Low.Interp R V) (ρ' : Nat → Val R V) {s : Shape} (h : boolShape s = true)
    (ht : (s.ev I ρ').truth = true) : s.ev I ρ' = .bool true := by
  cases s <;> simp_all [boolShape, Shape.ev, truth_bool]

theorem facts_bool (P : Problem) (r : Rule) (ks : List Nat) (aux : Nat) :
    ∀ s ∈ r.facts P ks aux, boolShape s = true := by
  intro s hs
  cases r
  case bits t w =>
    simp only [Rule.facts, intS, eqI, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_singleton,
      List.mem_cons, List.mem_nil_iff, or_false] at hs
    rcases hs with ⟨j, _, rfl | rfl⟩ | rfl <;> rfl
  all_goals simp only [Rule.facts, intS, eqI, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false,
    List.cons_append, List.nil_append] at hs
  all_goals first
    | (rcases hs with rfl | rfl | rfl | rfl | rfl | hs <;> first | rfl |
        (split at hs <;> simp at hs <;> rcases hs with rfl | rfl <;> rfl))
    | (rcases hs with rfl | rfl | hs <;> first | rfl | (split at hs <;> simp at hs <;> rcases hs with rfl | rfl | hs <;>
        first | rfl | (simp at hs; rcases hs with rfl | rfl | rfl <;> rfl) | (rcases hs with rfl <;> rfl)))
    | (rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)

/-- The sum of the bits of `bits(t, w)`, as the linear combination of its fact. -/
theorem eval_bitSum {V : Type} (ρ' : Nat → Val R V) (f : Nat → Nat) (b : Nat → Int) :
    ∀ n, (∀ j < n, ρ' (f j) = .num ((b j : Int) : R)) →
      Lia.eval (fun u => (ρ' u).toR) ((List.range n).map fun (j : Nat) => (f j, ((2 ^ j : Int) : Rat))) =
        ((bitSum n b : Int) : R)
  | 0, _ => by simp only [List.range_zero, List.map_nil, Lia.eval, bitSum, Ring.intCast_zero]
  | n + 1, h => by
    rw [List.range_succ, List.map_append, eval_append, eval_bitSum ρ' f b n (fun j hj => h j (by omega))]
    simp only [List.map_cons, List.map_nil, Lia.eval, h n (by omega), toR_num, Lia.rat_intCast, bitSum,
      Ring.intCast_add, Ring.intCast_mul]
    grind

/-! ## The values of rule symbols and intervals -/

/-- Exact products take the product of the values of their factors, the
    second of width `w` (`exactOk_spec` in `BitOps`). -/
def ExactSpec (SP : SProblem) (P : Problem) (tr : Trace) (Ms : Surf.Model R U) : Prop :=
  ∀ {v kept blasted w : Nat} {K Q : Int}, tr.exactOk SP P v kept blasted w = true →
    v < P.nodes.length → blasted < P.nodes.length → 0 ≤ Q → Q < 2 ^ w →
    Low.val (lowModel SP P tr Ms).toInterp P.nodes kept = .num (K : R) →
    Low.val (lowModel SP P tr Ms).toInterp P.nodes blasted = .num (Q : R) →
    Low.val (lowModel SP P tr Ms).toInterp P.nodes v = .num ((K * Q : Int) : R)

section
variable {SP : SProblem} {P : Problem} {tr : Trace} {Ms : Surf.Model R U}
  (hM : Ms.Sound SP.sig) (hw : Surf.wellFormed SP.nodes = true) (ht : Surf.typed SP.sig SP.nodes SP.sortOf = true)
  (hwP : Low.wellFormed P.nodes = true) (htP : Low.typed P.sig P.nodes P.sortOf = true)
  (hG : SigSpec SP P tr) (hML : (lowModel SP P tr Ms).Sound P.sig P.bvIndex)
  (hrng : ∀ j < P.nodes.length,
    inRange P.bvIndex (P.sortOf[j]?.getD 0) (Low.val (lowModel SP P tr Ms).toInterp P.nodes j))
  (hco : ∀ i < SP.nodes.length,
    Low.val (lowModel SP P tr Ms).toInterp P.nodes (tr.at i) = enc (Surf.val Ms.toInterp SP.nodes i))

set_option quotPrecheck false in
local notation "ρ" => Low.val (lowModel SP P tr Ms).toInterp P.nodes
set_option quotPrecheck false in
local notation "vs" => Surf.val Ms.toInterp SP.nodes
set_option quotPrecheck false in
local notation "MI" => (lowModel SP P tr Ms).toInterp
set_option quotPrecheck false in
local notation "ιρ" => fun y => intOf (Low.val (lowModel SP P tr Ms).toInterp P.nodes y)
set_option quotPrecheck false in
local notation "τρ" => fun y => (Low.val (lowModel SP P tr Ms).toInterp P.nodes y).truth

include hwP hG in
/-- A rule symbol takes the value of its rule. -/
theorem sym_val {x : Nat} {r : Rule} {j : Nat} (h : tr.symAt SP P x = some (r, j)) :
    ρ x = .num ((r.ival ιρ τρ j : Int) : R) := by
  unfold Trace.symAt at h
  split at h
  · rename_i k hk
    split at h
    · rename_i hle
      split at h
      · rename_i r' j' hm
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨m, rfl⟩ : ∃ m, k = SP.sig.decls.length + m := ⟨k - SP.sig.decls.length, by omega⟩
        rw [Nat.add_sub_cancel_left] at hm
        rw [Low.val_const hwP ((Tab.at_eq _ _).symm.trans hk)]
        exact const_rule SP P tr Ms hwP ((Tab.at_eq _ _).symm.trans hm) (fun y hy => ((hG.rule m _ _ ((Tab.at_eq _ _).symm.trans hm)).2 y hy).2)
      · cases h
    · cases h
  · cases h

theorem symNode_sym {r : Rule} {j x : Nat} (h : tr.symNode SP P r j = some x) :
    x < P.nodes.length ∧ tr.symAt SP P x = some (r, j) := by
  unfold Trace.symNode at h
  simp only at h
  split at h
  · rename_i hm
    split at h
    · rename_i hx
      simp only [Option.some.injEq] at h; subst h
      refine ⟨hx, ?_⟩
      have e1 := getElem?_idxOf P.nodes _ hx
      have e2 := getElem?_idxOf tr.mints _ hm
      unfold Trace.symAt
      rw [Tab.at_eq, e1]
      simp only [Tab.at_eq, Nat.le_add_right, if_true, Nat.add_sub_cancel_left, e2]
    · cases h
  · cases h

include hwP htP hML hrng in
/-- A lowered node of sort `Int` takes an integer value. -/
theorem val_int {x : Nat} (hx : x < P.nodes.length) (hs : P.sig.is (P.sortOf[x]?.getD 0) .int = true) :
    ∃ k : Int, ρ x = .num (k : R) := by
  have := Low.val_dom hML hwP htP hrng x hx
  simp only [Sig.is, beq_iff_eq] at hs
  exact (hML.int _ _ hs).mp this

include hwP in
theorem lin_val (x : Nat) : (ρ x).toR = Lia.eval (fun u => (ρ u).toR) (lin P.nodes x).1 + ((lin P.nodes x).2 : R) :=
  lin_sound (I := MI) hwP x

include hwP in
/-- `x + y`, `x` by its linear combination: the lowering flattens sums. -/
theorem ev_lin_add {x y : Nat} {X Y : Int} (hx : ρ x = .num (X : R)) (hy : ρ y = .num (Y : R)) :
    ((Shape.num ((lin P.nodes x).1 ++ [(y, 1)]) (lin P.nodes x).2).ev MI ρ).toR = ((1 * X + 1 * Y + 0 : Int) : R) := by
  have h := lin_val (SP := SP) (tr := tr) (Ms := Ms) hwP x
  rw [hx, toR_num] at h
  simp only [Shape.ev, toR_num, eval_append, Lia.eval, hy, rat_one, Ring.intCast_add, Ring.intCast_mul,
    Ring.intCast_one, Ring.intCast_zero]
  grind

theorem leaf_of_linIv {leaf : Nat → Option (Int × Int)} {x : Nat} {q : Int × Int}
    (h : linIv leaf [(x, 1)] = some q) : ∃ p, leaf x = some p := by
  unfold linIv at h
  simp only [show (1 : Rat).den = 1 from rfl, if_true] at h
  split at h
  · rename_i l hi _ _ hx _; exact ⟨_, hx⟩
  · cases h

include hwP in
theorem nodeIv_sound (leaf : Nat → Option (Int × Int)) (hleaf : ∀ u p, leaf u = some p → IvOk ρ u p)
    (x : Nat) (p : Int × Int) (h : nodeIv P leaf x = some p) : IvOk ρ x p := by
  unfold nodeIv at h
  cases hl : linIv leaf (lin P.nodes x).1 with
  | none => rw [hl] at h; cases h
  | some q =>
    rw [hl] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h
    obtain ⟨k, ek, h0, h1⟩ := linIv_sound ρ leaf hleaf _ q hl
    have hv := lin_val hwP (tr := tr) (Ms := Ms) (SP := SP) x
    have hnum : ∃ r, ρ x = .num r := by
      have viaLeaf : lin P.nodes x = ([(x, 1)], 0) → ∃ r, ρ x = .num r := by
        intro e
        rw [e] at hl
        obtain ⟨p, hp⟩ := leaf_of_linIv hl
        obtain ⟨k, e, -⟩ := hleaf x p hp
        exact ⟨_, e⟩
      cases hn : P.nodes[x]? with
      | none => exact viaLeaf (by simp [lin, Tab.at_eq, hn])
      | some n =>
        cases n
        case num v => exact ⟨_, Low.val_num hwP hn⟩
        case linear ts c => exact ⟨_, by rw [Low.val_node hwP hn]; rfl⟩
        all_goals exact viaLeaf (by simp [lin, Tab.at_eq, hn])
    obtain ⟨r, hr⟩ := hnum
    refine ⟨k + (lin P.nodes x).2, ?_, by simp only at h0 ⊢; omega, by simp only at h1 ⊢; omega⟩
    rw [hr, toR_num] at hv
    rw [hr, hv, ek, Ring.intCast_add]

include hM hw ht hG hrng hco in
theorem bvWidth_sound {l w : Nat} (hl : l < P.nodes.length) (h : tr.bvWidth SP P l = some w) :
    IvOk ρ l (0, 2 ^ w - 1) := by
  unfold Trace.bvWidth at h
  split at h
  · rename_i w' hw'
    cases h
    obtain ⟨k, e, h0, h1⟩ := hrng l hl w (by rw [hG.bvIndex, lookup_bvIndex]; simpa only [Tab.at_eq, Tab.at_eq] using hw')
    exact ⟨k, e, h0, by simp only; omega⟩
  · obtain ⟨i, hi, hfi⟩ := List.exists_of_findSome?_eq_some h
    rw [List.mem_range] at hi
    split at hfi
    · rename_i hat
      obtain ⟨x, hx⟩ := v_width hM hw ht hi hfi
      have e := hco i hi
      rw [beq_iff_eq.mp hat, hx, ofBv_num, enc_num] at e
      exact ⟨_, e, Vik.val_nonneg x, by have := Vik.val_lt x; simp only; omega⟩
    · cases hfi

include hM hw ht hwP hG hrng hco in
theorem leafIv_sound (sym : Rule → Nat → Option (Int × Int))
    (hsym : ∀ x r j p, tr.symAt SP P x = some (r, j) → sym r j = some p → IvOk ρ x p)
    (l : Nat) (p : Int × Int) (h : tr.leafIv SP P sym l = some p) : IvOk ρ l p := by
  unfold Trace.leafIv at h
  split at h
  · rename_i v hv
    cases h; exact ⟨v, Low.val_num hwP ((Tab.at_eq _ _).symm.trans hv), Int.le_refl _, Int.le_refl _⟩
  · rename_i n _ hn
    have hl := lt_of_get ((Tab.at_eq _ _).symm.trans hn)
    split at h
    · rename_i r j hs; exact hsym l r j p hs h
    · obtain ⟨w, hw', rfl⟩ := Option.map_eq_some_iff.mp h
      exact bvWidth_sound hM hw ht hG hrng hco hl hw'
  · cases h

include hwP in
theorem condAtom_sound {x : Nat} (hx : (ρ x).truth = true) :
    ∀ gc ∈ condAtom P x, (0 : R) ≤ Lia.eval (fun u => (ρ u).toR) gc.1 + (gc.2 : R) := by
  intro gc hgc
  unfold condAtom at hgc
  split at hgc
  · rename_i a b hn
    split at hgc
    · simp only [List.mem_singleton] at hgc; subst hgc
      rw [Low.val_node hwP ((Tab.at_eq _ _).symm.trans hn)] at hx
      simp only [Low.evalNode, truth_bool, decide_eq_true_eq] at hx
      change (ρ a).toR ≤ (ρ b).toR at hx
      have ha := lin_val hwP (tr := tr) (Ms := Ms) (SP := SP) a
      have hb := lin_val hwP (tr := tr) (Ms := Ms) (SP := SP) b
      simp only [eval_append, Lia.eval_neg, Ring.intCast_sub]
      grind
    · cases hgc
  · cases hgc

include hwP htP hML hrng in
theorem condCons_sound {c : Nat} {pos : Bool} (hc : (ρ c).truth = pos) :
    ∀ gc ∈ condCons P c pos, (0 : R) ≤ Lia.eval (fun u => (ρ u).toR) gc.1 + (gc.2 : R) := by
  intro gc hgc
  unfold condCons at hgc
  cases pos with
  | true =>
    simp only [Tab.at_eq, if_true] at hgc
    split at hgc
    · rename_i xs hn
      obtain ⟨x, hx, hgx⟩ := List.mem_flatMap.mp hgc
      rw [Low.val_node hwP hn] at hc
      simp only [Low.evalNode, truth_bool, List.all_eq_true] at hc
      exact condAtom_sound hwP (hc x hx) gc hgx
    · exact condAtom_sound hwP hc gc hgc
  | false =>
    simp only [Tab.at_eq, Bool.false_eq_true, if_false] at hgc
    split at hgc
    · rename_i a b hn
      split at hgc
      · rename_i hab
        simp only [List.mem_singleton] at hgc; subst hgc
        simp only [Bool.and_eq_true] at hab
        have hcl := lt_of_get hn
        have hal : a < P.nodes.length := Nat.lt_trans (child_lt hwP hn (by simp [Node.children])) hcl
        have hbl : b < P.nodes.length := Nat.lt_trans (child_lt hwP hn (by simp [Node.children])) hcl
        obtain ⟨ka, ea⟩ := val_int hwP htP hML hrng hal hab.1
        obtain ⟨kb, eb⟩ := val_int hwP htP hML hrng hbl hab.2
        rw [Low.val_node hwP hn] at hc
        simp only [Low.evalNode, truth_bool, decide_eq_false_iff_not] at hc
        change ¬ (ρ a).toR ≤ (ρ b).toR at hc
        have ha := lin_val hwP (tr := tr) (Ms := Ms) (SP := SP) a
        have hb := lin_val hwP (tr := tr) (Ms := Ms) (SP := SP) b
        rw [ea, toR_num] at hc ha
        rw [eb, toR_num] at hc hb
        have hlt : kb < ka := by
          rcases Int.lt_or_le kb ka with h | h
          · exact h
          · exact absurd (cast_le_iff.mpr h) hc
        have h0 : ((0 : Int) : R) ≤ ((ka - kb - 1 : Int) : R) := cast_le_iff.mpr (by omega)
        simp only [Ring.intCast_zero, Ring.intCast_sub, Ring.intCast_one] at h0
        simp only [eval_append, Lia.eval_neg, Ring.intCast_sub, Ring.intCast_one]
        grind
      · cases hgc
    · cases hgc

theorem refine_sound (t : Nat) (f : Lia.Form × Int)
    (hf : (ρ t).toR = Lia.eval (fun u => (ρ u).toR) f.1 + (f.2 : R)) :
    ∀ (cons : List (Lia.Form × Int)), (∀ gc ∈ cons, (0 : R) ≤ Lia.eval (fun u => (ρ u).toR) gc.1 + (gc.2 : R)) →
      ∀ (i : Option (Int × Int)) (p : Int × Int), (∀ q, i = some q → IvOk ρ t q) → refine f cons i = some p → IvOk ρ t p
  | [], _, i, p, hi, h => hi p h
  | gc :: cons, hcons, i, p, hi, h => by
    simp only [refine, List.foldl_cons] at h
    refine refine_sound t f hf cons (fun g m => hcons g (by simp [m])) _ p ?_ h
    intro q hq
    obtain ⟨p0, hp0, rfl⟩ := Option.map_eq_some_iff.mp hq
    obtain ⟨k, ek, h0, h1⟩ := hi p0 hp0
    have hg := hcons gc (by simp)
    rw [ek, toR_num] at hf
    refine ⟨k, ek, ?_, ?_⟩ <;> dsimp only
    · split
      · rename_i he
        have e := eval_canon (fun u => (ρ u).toR) (f.1 ++ Lia.neg gc.1)
        rw [List.isEmpty_iff.mp he, eval_append, Lia.eval_neg] at e
        simp only [Lia.eval] at e
        have : ((f.2 - gc.2 : Int) : R) ≤ (k : R) := by rw [Ring.intCast_sub]; grind
        exact Int.max_le.mpr ⟨h0, cast_le_iff.mp this⟩
      · exact h0
    · split
      · rename_i he
        have e := eval_canon (fun u => (ρ u).toR) (f.1 ++ gc.1)
        rw [List.isEmpty_iff.mp he, eval_append] at e
        simp only [Lia.eval] at e
        have : (k : R) ≤ ((f.2 + gc.2 : Int) : R) := by rw [Ring.intCast_add]; grind
        exact Int.le_min.mpr ⟨h1, cast_le_iff.mp this⟩
      · exact h1

include hwP htP hML hrng in
theorem branchIv_sound (node : Nat → Option (Int × Int)) (hnode : ∀ x q, node x = some q → IvOk ρ x q)
    {c t : Nat} {pos : Bool} (hc : (ρ c).truth = pos) {p : Int × Int} (h : branchIv P node c t pos = some p) :
    IvOk ρ t p :=
  refine_sound t (lin P.nodes t) (lin_val hwP t) _ (condCons_sound hwP htP hML hrng hc) _ p (hnode t) h

theorem ivSub_sound {i : Option (Int × Int)} {lo hi : Int} (h : ivSub i lo hi = true) :
    ∃ q, i = some q ∧ lo ≤ q.1 ∧ q.2 ≤ hi := by
  unfold ivSub at h
  split at h
  · rename_i a b
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨_, rfl, h.1, h.2⟩
  · cases h

include hwP htP hML hrng in
/-- The value of a rule symbol is within the interval of the rule. -/
theorem ruleIv_sound (node : Nat → Option (Int × Int)) (hnode : ∀ x q, node x = some q → IvOk ρ x q)
    (r : Rule) (j : Nat) (p : Int × Int) (h : Rule.iv P node r j = some p) :
    p.1 ≤ r.ival ιρ τρ j ∧ r.ival ιρ τρ j ≤ p.2 := by
  have hk : ∀ x q, node x = some q → ∃ k, intOf (ρ x) = k ∧ q.1 ≤ k ∧ k ≤ q.2 := by
    intro x q hq
    obtain ⟨k, e, h0, h1⟩ := hnode x q hq
    exact ⟨k, by rw [e, intOf_num], h0, h1⟩
  cases r with
  | modulo v w lo hi =>
    cases j with
    | zero =>
      simp only [Rule.iv, Option.some.injEq] at h; subst h
      exact emod_bounds _ (two_pow_pos w)
    | succ j =>
      simp only [Rule.iv] at h
      obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨k, ek, h0, h1⟩ := hk v q hq
      simp only [Rule.ival, ek]
      exact ⟨Int.ediv_le_ediv (two_pow_pos w) h0, Int.ediv_le_ediv (two_pow_pos w) h1⟩
  | cases c t e lo hi =>
    simp only [Rule.iv] at h
    unfold ivHull at h
    split at h
    · rename_i a b a' b' h1 h2
      simp only [Option.some.injEq] at h; subst h
      simp only [Rule.ival]
      by_cases hc : (ρ c).truth = true
      · rw [if_pos hc]
        obtain ⟨k, ek, k0, k1⟩ := branchIv_sound hwP htP hML hrng node hnode hc h1
        rw [ek, intOf_num]
        exact ⟨Int.le_trans (Int.min_le_left _ _) k0, Int.le_trans k1 (Int.le_max_left _ _)⟩
      · rw [if_neg hc]
        obtain ⟨k, ek, k0, k1⟩ := branchIv_sound hwP htP hML hrng node hnode (by simpa using hc) h2
        rw [ek, intOf_num]
        exact ⟨Int.le_trans (Int.min_le_right _ _) k0, Int.le_trans k1 (Int.le_max_right _ _)⟩
    · cases h
  | divide v d qmax =>
    cases j with
    | zero =>
      simp only [Rule.iv] at h
      split at h
      · rename_i hd
        obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨k, ek, h0, h1⟩ := hk v q hq
        simp only [Rule.ival, ek]
        exact ⟨Int.ediv_le_ediv hd h0, Int.ediv_le_ediv hd h1⟩
      · cases h
    | succ j =>
      simp only [Rule.iv] at h
      split at h
      · rename_i hd
        simp only [Option.some.injEq] at h; subst h
        exact emod_bounds _ hd
      · cases h
  | sdivide t w d fl =>
    cases j with
    | zero =>
      simp only [Rule.iv] at h
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        obtain ⟨⟨hd, hw0⟩, hsub⟩ := hc
        obtain ⟨q, hq, q0, q1⟩ := ivSub_sound hsub
        obtain ⟨k, ek, h0, h1⟩ := hk t q hq
        have hs := signedI_bounds hw0 (Int.le_trans q0 h0) (Int.le_trans h1 q1)
        have hh : (0 : Int) ≤ 2 ^ (w - 1) := Int.le_of_lt (two_pow_pos _)
        simp only [Rule.ival, ek]
        cases fl with
        | true =>
          simp only [if_true, Option.some.injEq] at h ⊢; subst h
          exact ⟨Int.ediv_le_ediv hd hs.1, Int.ediv_le_ediv hd hs.2⟩
        | false =>
          simp only [Bool.false_eq_true, if_false, Option.some.injEq] at h ⊢; subst h
          exact tdiv_bounds hd hs.1 hs.2 hh
      · cases h
    | succ j =>
      simp only [Rule.iv] at h
      split at h
      · rename_i hd
        cases fl with
        | true =>
          simp only [if_true, Option.some.injEq] at h; subst h
          exact emod_bounds _ hd
        | false =>
          simp only [Bool.false_eq_true, if_false, Option.some.injEq] at h; subst h
          have := tmod_bounds (signedI w (intOf (ρ t))) hd
          exact ⟨this.1, this.2.1⟩
      · cases h
  | int2bv t w =>
    cases j with
    | zero =>
      simp only [Rule.iv, Option.some.injEq] at h; subst h
      exact emod_bounds _ (two_pow_pos w)
    | succ j => simp only [Rule.iv] at h; cases h
  | smodz a c w =>
    simp only [Rule.iv, Option.some.injEq] at h; subst h
    simp only [Rule.ival]
    exact smodzVal_bounds _ _ _
  | bits t w =>
    simp only [Rule.iv, Option.some.injEq] at h; subst h
    simp only [Rule.ival]
    exact bit_range _ _
  | udiv a b w =>
    simp only [Rule.iv, Option.some.injEq] at h; subst h
    cases j <;> exact emod_bounds _ (two_pow_pos w)

include hwP in
/-- The value of a rule symbol is within the interval its arguments give. -/
theorem fixedIv_sound (node : Nat → Option (Int × Int)) (hnode : ∀ x q, node x = some q → IvOk ρ x q)
    (r : Rule) (j : Nat) (p : Int × Int) (h : r.fixedIv node j = some p) :
    p.1 ≤ r.ival ιρ τρ j ∧ r.ival ιρ τρ j ≤ p.2 := by
  cases r with
  | modulo v w lo hi =>
    cases j with
    | zero =>
      simp only [Rule.fixedIv, Option.some.injEq] at h; subst h
      exact emod_bounds _ (two_pow_pos w)
    | succ j => simp only [Rule.fixedIv] at h; cases h
  | cases c t e lo hi =>
    simp only [Rule.fixedIv] at h
    unfold ivHull at h
    split at h
    · rename_i a b a' b' h1 h2
      simp only [Option.some.injEq] at h; subst h
      simp only [Rule.ival]
      split
      · obtain ⟨k, ek, k0, k1⟩ := hnode t _ h1
        rw [ek, intOf_num]
        exact ⟨Int.le_trans (Int.min_le_left _ _) k0, Int.le_trans k1 (Int.le_max_left _ _)⟩
      · obtain ⟨k, ek, k0, k1⟩ := hnode e _ h2
        rw [ek, intOf_num]
        exact ⟨Int.le_trans (Int.min_le_right _ _) k0, Int.le_trans k1 (Int.le_max_right _ _)⟩
    · cases h
  | int2bv t w =>
    cases j with
    | zero =>
      simp only [Rule.fixedIv, Option.some.injEq] at h; subst h
      exact emod_bounds _ (two_pow_pos w)
    | succ j => simp only [Rule.fixedIv] at h; cases h
  | smodz a c w =>
    simp only [Rule.fixedIv, Option.some.injEq] at h; subst h
    simp only [Rule.ival]
    exact smodzVal_bounds _ _ _
  | bits t w =>
    simp only [Rule.fixedIv, Option.some.injEq] at h; subst h
    simp only [Rule.ival]
    exact bit_range _ _
  | udiv a b w =>
    simp only [Rule.fixedIv, Option.some.injEq] at h; subst h
    cases j <;> exact emod_bounds _ (two_pow_pos w)
  | _ => simp only [Rule.fixedIv] at h; cases h

include hwP hG in
theorem fixedLeaf_sound {B : Nat}
    (hr : ∀ y < P.nodes.length, tr.mu SP P y < B → inRange P.bvIndex (P.sortOf[y]?.getD 0) (ρ y))
    (sym : Rule → Nat → Option (Int × Int))
    (hsym : ∀ r j p, sym r j = some p → p.1 ≤ r.ival ιρ τρ j ∧ r.ival ιρ τρ j ≤ p.2)
    (u : Nat) (p : Int × Int) (h : tr.fixedLeaf SP P B sym u = some p) : IvOk ρ u p := by
  unfold Trace.fixedLeaf at h
  split at h
  · rename_i v hv
    simp only [Option.some.injEq] at h; subst h
    exact ⟨v, Low.val_num hwP ((Tab.at_eq _ _).symm.trans hv), Int.le_refl _, Int.le_refl _⟩
  · rename_i n _ hn
    split at h
    · rename_i r j hs
      obtain ⟨h0, h1⟩ := hsym r j p h
      exact ⟨_, sym_val hwP hG hs, h0, h1⟩
    · split at h
      · rename_i hB
        obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
        have hl := lt_of_get ((Tab.at_eq _ _).symm.trans hn)
        rw [Tab.at_eq] at hw
        obtain ⟨k, ek, k0, k1⟩ := hr u hl hB w (by rw [hG.bvIndex, lookup_bvIndex]; exact hw)
        exact ⟨k, ek, k0, by simp only; omega⟩
      · cases h
  · cases h

include hwP hG in
/-- The intervals that numbers, rule symbols and nodes of bit-vector sorts
    before `B` give hold, when those nodes are in range. -/
theorem fixedAt_sound {B : Nat}
    (hr : ∀ y < P.nodes.length, tr.mu SP P y < B → inRange P.bvIndex (P.sortOf[y]?.getD 0) (ρ y)) :
    ∀ n x p, tr.fixedAt SP P B n x = some p → IvOk ρ x p
  | 0, x, p, h => by
    simp only [Trace.fixedAt] at h
    exact nodeIv_sound hwP _ (fixedLeaf_sound hwP hG hr _
      (fixedIv_sound hwP _ (fun _ _ e => by cases e))) x p h
  | n + 1, x, p, h => by
    simp only [Trace.fixedAt] at h
    exact nodeIv_sound hwP _ (fixedLeaf_sound hwP hG hr _
      (fixedIv_sound hwP _ (fixedAt_sound hr n))) x p h

include hM hw ht hwP htP hG hML hrng hco in
/-- The intervals the trace computes hold. -/
theorem ivAt_sound : ∀ n x p, tr.ivAt SP P n x = some p → IvOk ρ x p
  | 0, x, p, h => by
    simp only [Trace.ivAt] at h
    exact nodeIv_sound hwP _ (leafIv_sound hM hw ht hwP hG hrng hco _ (fun _ _ _ _ _ e => by cases e)) x p h
  | n + 1, x, p, h => by
    simp only [Trace.ivAt] at h
    refine nodeIv_sound hwP _ (leafIv_sound hM hw ht hwP hG hrng hco _ (fun y r j q hs hq => ?_)) x p h
    rw [IvOk, sym_val hwP hG hs]
    obtain ⟨h0, h1⟩ := ruleIv_sound hwP htP hML hrng _ (ivAt_sound n) r j q hq
    exact ⟨_, rfl, h0, h1⟩

include hM hw ht hwP htP hG hML hrng hco in
theorem iv_sound {x : Nat} {p : Int × Int} (h : tr.iv SP P x = some p) : IvOk ρ x p :=
  ivAt_sound hM hw ht hwP htP hG hML hrng hco _ x p h

include hG in
theorem symAt_args {x : Nat} {r : Rule} {j : Nat} (h : tr.symAt SP P x = some (r, j)) :
    x < P.nodes.length ∧ ∀ y ∈ r.args, y < P.nodes.length := by
  unfold Trace.symAt at h
  split at h
  · rename_i k hk
    split at h
    · rename_i hle
      split at h
      · rename_i r' j' hm
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨lt_of_get ((Tab.at_eq _ _).symm.trans hk), fun y hy => ((hG.rule _ _ _ ((Tab.at_eq _ _).symm.trans hm)).2 y hy).1⟩
      · cases h
    · cases h
  · cases h

include hwP htP hG hML hrng in
/-- A node `signed(t, w)` takes the signed value of `t`. -/
theorem signedOk_sound {t w x : Nat} {K : Int} (hok : tr.signedOk SP P t w x = true) (htv : ρ t = .num (K : R)) :
    ρ x = .num ((signedI w K : Int) : R) := by
  unfold Trace.signedOk at hok
  split at hok
  · rename_i v hv
    have e := Low.val_num (I := MI) hwP ((Tab.at_eq _ _).symm.trans hv)
    rw [htv] at e
    have := (num_int_eq_iff (U := U ⊕ Nat)).mp e
    subst this
    exact Low.val_num hwP (by simpa using hok)
  · split at hok
    · rename_i c thn els lo hi hs
      simp only [Bool.and_eq_true, beq_iff_eq] at hok
      obtain ⟨⟨⟨⟨_, _⟩, hc⟩, hthn⟩, hel⟩ := hok
      have hargs := (symAt_args hG hs).2
      have hcl : c < P.nodes.length := hargs c (by simp [Rule.args])
      have hthl : thn < P.nodes.length := hargs thn (by simp [Rule.args])
      rw [sym_val hwP hG hs]
      simp only [Rule.ival]
      have ec := fits_sound hML hwP htP hrng c hcl _ hc
      have etc := negS_int MI ρ hwP (w := w) rfl htv
      rw [← ec] at etc
      have eth := fits_sound hML hwP htP hrng thn hthl _ hthn
      have hl := lin_val hwP (tr := tr) (Ms := Ms) (SP := SP) t
      rw [htv, toR_num] at hl
      have ethn : ρ thn = .num (((K - 2 ^ w : Int)) : R) := by
        rw [eth]; simp only [Shape.ev]; congr 1
        rw [Ring.intCast_sub, Ring.intCast_sub]; grind
      rw [etc, ethn, intOf_num, hel, htv, intOf_num]
      unfold signedI
      by_cases hn : 2 ^ (w - 1) ≤ K <;> simp [hn]
    · cases hok

include hM hw ht hwP htP hG hML hrng hco in
/-- The facts of a rule hold, within the bounds `Trace.ruleOk` checks. -/
theorem ruleFacts_truth (hex : ExactSpec SP P tr Ms) {r : Rule} {aux : Nat} {fs : List Shape} (hok : tr.ruleOk SP P r aux = true)
    (hf : tr.ruleFacts SP P r aux = some fs) : ∀ s ∈ fs, (s.ev MI ρ).truth = true := by
  unfold Trace.ruleFacts at hf
  obtain ⟨ks, hks, rfl⟩ := Option.map_eq_some_iff.mp hf
  have sym : ∀ j < r.nsyms, tr.symAt SP P (ks.getD j 0) = some (r, j) ∧
      ρ (ks.getD j 0) = .num ((r.ival ιρ τρ j : Int) : R) := by
    intro j hj
    obtain ⟨x, hx, hsx⟩ := mapM_get _ _ ks hks j (by simpa using hj)
    simp only [List.getElem_range] at hsx
    have hsa := (symNode_sym hsx).2
    rw [List.getD_eq_getElem?_getD, hx, Option.getD_some]
    exact ⟨hsa, sym_val hwP hG hsa⟩
  have args := fun (j : Nat) (hj : j < r.nsyms) => (symAt_args hG (sym j hj).1).2
  have ivs := fun {x : Nat} {q : Int × Int} (h : tr.iv SP P x = some q) =>
    iv_sound hM hw ht hwP htP hG hML hrng hco h
  have zero1 : ∀ c : Int, ((1 : Int) : Rat) = 1 := fun _ => rfl
  intro s hs
  cases r with
  | modulo v w lo hi =>
    simp only [Trace.ruleOk, Bool.and_eq_true] at hok
    obtain ⟨_, hsub⟩ := hok
    obtain ⟨q, hq, q0, q1⟩ := ivSub_sound hsub
    obtain ⟨K, eK, k0, k1⟩ := ivs hq
    have hm := two_pow_pos w
    have ⟨d0, d1⟩ := ediv_bounds hm (Int.le_trans q0 k0) (Int.le_trans k1 q1)
    have ⟨r0, r1⟩ := emod_bounds K hm
    have hid := Int.emod_add_mul_ediv K (2 ^ w)
    have er := (sym 0 (by simp only [Rule.nsyms]; split <;> decide)).2
    simp only [Rule.ival, eK, intOf_num] at er
    simp only [Rule.facts, List.mem_append] at hs
    rcases hs with hs | hs
    · exact intS_holds MI ρ er r0 r1 s hs
    · split at hs
      · rename_i hsmall
        simp only [List.mem_singleton] at hs; subst hs
        simp only [Shape.ev, truth_bool, Shape.anyTrue_eq, List.any_map, List.any_eq_true, List.mem_range,
          Function.comp_def]
        refine ⟨(K / 2 ^ w - lo).toNat, by omega, ?_⟩
        refine eqI_holds MI ρ (ev_same_num MI ρ eK) (ev_num1 MI ρ er _) ?_
        have : (lo + ((K / 2 ^ w - lo).toNat : Int)) = K / 2 ^ w := by omega
        rw [this]; grind
      · rename_i hsmall
        simp only [List.mem_append, List.mem_singleton] at hs
        have eq := (sym 1 (by simp only [Rule.nsyms]; rw [if_neg hsmall]; decide)).2
        simp only [Rule.ival, eK, intOf_num] at eq
        rcases hs with hs | rfl
        · exact intS_holds MI ρ eq d0 d1 s hs
        · refine eqI_holds MI ρ (ev_same_num MI ρ eK) (ev_num2' MI ρ er eq 1 (2 ^ w) 0 rfl rfl) ?_
          grind
  | cases c t e lo hi =>
    simp only [Tab.at_eq, Trace.ruleOk, Bool.and_eq_true] at hok
    obtain ⟨⟨⟨⟨hti, hei⟩, _⟩, hbt⟩, hbe⟩ := hok
    have ek := (sym 0 (by simp [Rule.nsyms])).2
    have ha := args 0 (by simp [Rule.nsyms])
    obtain ⟨Kt, eKt⟩ := val_int hwP htP hML hrng (ha t (by simp [Rule.args])) hti
    obtain ⟨Ke, eKe⟩ := val_int hwP htP hML hrng (ha e (by simp [Rule.args])) hei
    simp only [Rule.ival] at ek
    simp only [Rule.facts, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hs
    rcases hs with hs | rfl | rfl
    · by_cases hc : (ρ c).truth = true
      · obtain ⟨q, hq, q0, q1⟩ := ivSub_sound hbt
        obtain ⟨k, e1, k0, k1⟩ := branchIv_sound hwP htP hML hrng _ (fun _ _ h => ivs h) hc hq
        rw [if_pos hc, e1, intOf_num] at ek
        exact intS_holds MI ρ ek (Int.le_trans q0 k0) (Int.le_trans k1 q1) s hs
      · obtain ⟨q, hq, q0, q1⟩ := ivSub_sound hbe
        obtain ⟨k, e1, k0, k1⟩ := branchIv_sound hwP htP hML hrng _ (fun _ _ h => ivs h)
          (by simpa using hc) hq
        rw [if_neg hc, e1, intOf_num] at ek
        exact intS_holds MI ρ ek (Int.le_trans q0 k0) (Int.le_trans k1 q1) s hs
    · simp only [Shape.ev, truth_bool]
      by_cases hc : (ρ c).truth = true
      · rw [if_pos hc, eKt, intOf_num] at ek
        rw [hc, eqI_holds MI ρ (ev_same_num MI ρ ek) (ev_same_num MI ρ eKt) rfl]; rfl
      · simp [hc]
    · simp only [Shape.ev, truth_bool]
      by_cases hc : (ρ c).truth = true
      · simp [hc]
      · rw [if_neg hc, eKe, intOf_num] at ek
        rw [eqI_holds MI ρ (ev_same_num MI ρ ek) (ev_same_num MI ρ eKe) rfl]; simp
  | divide v d qmax =>
    simp only [Trace.ruleOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨_, hd⟩, hsub⟩ := hok
    obtain ⟨q, hq, q0, q1⟩ := ivSub_sound hsub
    obtain ⟨K, eK, k0, k1⟩ := ivs hq
    have ⟨d0, d1⟩ := ediv_bounds hd (a := K) (lo := 0) (hi := qmax) (by omega)
      (by have : (qmax + 1) * d - 1 = qmax * d + d - 1 := by grind
          rw [this]; exact Int.le_trans k1 q1)
    have ⟨r0, r1⟩ := emod_bounds K hd
    have hid := Int.mul_ediv_add_emod K d
    have eq := (sym 0 (by simp [Rule.nsyms])).2
    have er := (sym 1 (by simp [Rule.nsyms])).2
    simp only [Rule.ival, eK, intOf_num] at eq er
    simp only [Rule.facts, List.mem_append, List.mem_singleton] at hs
    rcases hs with (hs | hs) | rfl
    · exact intS_holds MI ρ eq d0 d1 s hs
    · exact intS_holds MI ρ er r0 r1 s hs
    · refine eqI_holds MI ρ (ev_same_num MI ρ eK) (ev_num2' MI ρ eq er d 1 0 rfl rfl) ?_
      grind
  | sdivide t w d fl =>
    simp only [Trace.ruleOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨⟨_, hd⟩, hw0⟩, hsub⟩, hsg⟩ := hok
    obtain ⟨q, hq, q0, q1⟩ := ivSub_sound hsub
    obtain ⟨K, eK, k0, k1⟩ := ivs hq
    have hs' := signedI_bounds hw0 (Int.le_trans q0 k0) (Int.le_trans k1 q1)
    have hh : (0 : Int) ≤ 2 ^ (w - 1) := Int.le_of_lt (two_pow_pos _)
    have eaux := signedOk_sound hwP htP hG hML hrng hsg eK
    have eq := (sym 0 (by simp [Rule.nsyms])).2
    have er := (sym 1 (by simp [Rule.nsyms])).2
    simp only [Rule.ival, eK, intOf_num] at eq er
    simp only [Rule.facts, List.mem_append, List.mem_singleton] at hs
    cases fl with
    | true =>
      simp only [if_true] at eq er hs
      have ⟨r0, r1⟩ := emod_bounds (signedI w K) hd
      have hid := Int.mul_ediv_add_emod (signedI w K) d
      rcases hs with ((hs | hs) | rfl) | hs
      · exact intS_holds MI ρ eq (ediv_lower hd hs'.1) (Int.ediv_le_ediv hd hs'.2) s hs
      · exact intS_holds MI ρ er r0 r1 s hs
      · refine eqI_holds MI ρ (ev_same_num MI ρ eaux) (ev_num2' MI ρ eq er d 1 0 rfl rfl) ?_
        grind
      · cases hs
    | false =>
      simp only [Bool.false_eq_true, if_false] at eq er hs
      have ⟨r0, r1, rpos, rneg⟩ := tmod_bounds (signedI w K) hd
      have hid := Int.mul_tdiv_add_tmod (signedI w K) d
      have ⟨t0, t1⟩ := tdiv_bounds hd hs'.1 hs'.2 hh
      have hng := negS_int MI ρ hwP (w := w) rfl eK
      have hw2 := two_pow_pred hw0
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hs
      rcases hs with ((hs | hs) | rfl) | rfl | rfl
      · exact intS_holds MI ρ eq (by omega) t1 s hs
      · exact intS_holds MI ρ er r0 r1 s hs
      · refine eqI_holds MI ρ (ev_same_num MI ρ eaux) (ev_num2' MI ρ eq er d 1 0 rfl rfl) ?_
        grind
      · by_cases hn : 2 ^ (w - 1) ≤ K
        · exact implies_of_right MI ρ (le_int_holds MI ρ (ev_same_num MI ρ er) (ev_num0 MI ρ 0)
            (rneg (by unfold signedI; rw [if_pos hn]; omega)))
        · exact implies_of_left MI ρ (by rw [hng]; simp [hn])
      · by_cases hn : 2 ^ (w - 1) ≤ K
        · exact implies_of_left MI ρ (by simp only [Shape.ev, truth_bool]; rw [hng]; simp [hn])
        · exact implies_of_right MI ρ (le_int_holds MI ρ (ev_num0 MI ρ 0) (ev_same_num MI ρ er)
            (rpos (by unfold signedI; rw [if_neg hn]; omega)))
  | int2bv t w =>
    simp only [Trace.ruleOk] at hok
    have ha := args 0 (by simp [Rule.nsyms])
    obtain ⟨K, eK⟩ := val_int hwP htP hML hrng (ha t (by simp [Rule.args])) hok
    have hm := two_pow_pos w
    have ⟨r0, r1⟩ := emod_bounds K hm
    have hid := Int.emod_add_mul_ediv K (2 ^ w)
    have e0 := (sym 0 (by simp [Rule.nsyms])).2
    have e1 := (sym 1 (by simp [Rule.nsyms])).2
    simp only [Rule.ival, eK, intOf_num] at e0 e1
    simp only [Rule.facts, List.mem_append, List.mem_singleton] at hs
    rcases hs with hs | rfl
    · exact intS_holds MI ρ e0 r0 r1 s hs
    · refine eqI_holds MI ρ (ev_same_num MI ρ eK) (ev_num2' MI ρ e0 e1 1 (2 ^ w) 0 rfl rfl) ?_
      grind
  | smodz a c w =>
    simp only [Trace.ruleOk, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, beq_iff_eq] at hok
    obtain ⟨⟨⟨hai, hw0⟩, hT⟩, hsa⟩ := hok
    have ha := args 0 (by simp [Rule.nsyms])
    obtain ⟨K, eK⟩ := val_int hwP htP hML hrng (ha a (by simp [Rule.args])) hai
    have ez := (sym 0 (by simp [Rule.nsyms])).2
    have eaux := sym_val (Ms := Ms) hwP hG hsa
    simp only [Rule.ival, eK, intOf_num, Bool.false_eq_true, if_false] at ez eaux
    have hng := negS_int MI ρ hwP (w := w) rfl eK
    unfold smodzVal at ez
    simp only at ez
    have hdiff : ((if 0 < smodT c w then negS P a w else Shape.not (negS P a w)).ev MI ρ).truth =
        (if 0 < smodT c w then decide (2 ^ (w - 1) ≤ K) else !decide (2 ^ (w - 1) ≤ K)) := by
      split <;> simp only [Shape.ev, truth_bool, hng]
    have hrz := eqI_int MI ρ (ev_same_num MI ρ eaux) (ev_num0 MI ρ 0)
    generalize (if 0 < smodT c w then decide (2 ^ (w - 1) ≤ K) else !decide (2 ^ (w - 1) ≤ K)) = D at hdiff ez
    generalize (signedI w K).tmod ↑(smodT c w).natAbs = rm at hrz ez
    simp only [Rule.facts, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hs
    rcases hs with hs | rfl | rfl | rfl
    · exact intS_holds MI ρ ez (by split <;> omega) (by split <;> omega) s hs
    · cases D
      · exact implies_of_right MI ρ (eqI_holds MI ρ (ev_same_num MI ρ ez) (ev_num0 MI ρ 0) (by simp))
      · exact implies_of_left MI ρ (by simp only [Shape.ev, truth_bool, hdiff, Bool.not_true])
    · by_cases h : rm = 0
      · exact implies_of_right MI ρ (eqI_holds MI ρ (ev_same_num MI ρ ez) (ev_num0 MI ρ 0) (by simp [h]))
      · exact implies_of_left MI ρ (by rw [hrz]; simpa using h)
    · by_cases h : D = true ∧ rm ≠ 0
      · exact implies_of_right MI ρ (eqI_holds MI ρ (ev_same_num MI ρ ez) (ev_num0 MI ρ 1) (by simp [h]))
      · refine implies_of_left MI ρ ?_
        simp only [Shape.ev, Shape.allTrue, truth_bool, hdiff, hrz, Bool.and_true]
        cases D <;> by_cases h' : rm = 0 <;> simp_all
  | bits t w =>
    simp only [Trace.ruleOk, Bool.and_eq_true] at hok
    obtain ⟨_, hsub⟩ := hok
    obtain ⟨q, hq, q0, q1⟩ := ivSub_sound hsub
    obtain ⟨K, eK, k0, k1⟩ := ivs hq
    have eb : ∀ j < w, ρ (ks.getD j 0) = .num ((bit K j : Int) : R) := by
      intro j hj
      have := (sym j (by simpa [Rule.nsyms] using hj)).2
      simpa only [Tab.at_eq, Rule.ival, eK, intOf_num] using this
    simp only [Rule.facts, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_singleton] at hs
    rcases hs with ⟨j, hj, hs⟩ | rfl
    · exact intS_holds MI ρ (eb j hj) (bit_range K j).1 (bit_range K j).2 s hs
    · refine eqI_holds MI ρ (ev_same_num MI ρ eK) (B := bitSum w (bit K)) ?_
        (bits_facts (t := K) (w := w) ⟨Int.le_trans q0 k0, Int.le_trans k1 q1⟩).2
      simp only [Shape.ev, toR_num, Ring.intCast_zero]
      rw [eval_bitSum (R := R) _ _ _ w eb]; grind
  | udiv a b w =>
    simp only [Trace.ruleOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨⟨⟨_, _⟩, hsa⟩, hsb⟩, hauxl⟩, hq⟩ := hok
    obtain ⟨qa, hqa, qa0, qa1⟩ := ivSub_sound hsa
    obtain ⟨A, eA, a0, a1⟩ := ivs hqa
    obtain ⟨qb, hqb, qb0, qb1⟩ := ivSub_sound hsb
    obtain ⟨B, eB, b0, b1⟩ := ivs hqb
    have hm := two_pow_pos w
    have hA0 : 0 ≤ A := by omega
    have hA1 : A < 2 ^ w := by omega
    have hB0 : 0 ≤ B := by omega
    have eq := (sym 0 (by simp [Rule.nsyms])).2
    have er := (sym 1 (by simp [Rule.nsyms])).2
    simp only [Rule.ival, eA, eB, intOf_num] at eq er
    have ⟨Q0, Q1⟩ := emod_bounds (if B = 0 then 2 ^ w - 1 else A / B) hm
    have ⟨R0, R1⟩ := emod_bounds (if B = 0 then A else A % B) hm
    simp only [Rule.facts, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hs
    rcases hs with (hs | hs) | rfl | rfl
    · exact intS_holds MI ρ eq Q0 Q1 s hs
    · exact intS_holds MI ρ er R0 R1 s hs
    all_goals
      have vq : (if B = 0 then 2 ^ w - 1 else A / B) % 2 ^ w = if B = 0 then 2 ^ w - 1 else A / B := by
        split
        · exact Int.emod_eq_of_lt (by omega) (by omega)
        · have : A / B ≤ A := Int.ediv_le_self _ hA0
          exact Int.emod_eq_of_lt (Int.ediv_nonneg hA0 hB0) (by omega)
      have vr : (if B = 0 then A else A % B) % 2 ^ w = if B = 0 then A else A % B := by
        split
        · exact Int.emod_eq_of_lt hA0 hA1
        · rename_i hB
          have := Int.emod_lt_of_pos A (show 0 < B by omega)
          exact Int.emod_eq_of_lt (Int.emod_nonneg _ (by omega)) (by omega)
      rw [vq] at eq; rw [vr] at er
      have hz := eqI_int MI ρ (ev_same_num MI ρ eB) (ev_num0 MI ρ 0)
    · by_cases hB : B = 0
      · refine implies_of_right MI ρ (and2_holds MI ρ ?_ ?_)
        · exact eqI_holds MI ρ (ev_same_num MI ρ eq) (ev_num0 MI ρ _) (by simp [hB])
        · exact eqI_holds MI ρ (ev_same_num MI ρ er) (ev_same_num MI ρ eA) (by simp [hB])
      · exact implies_of_left MI ρ (by rw [hz]; simpa using hB)
    · by_cases hB : B = 0
      · exact implies_of_left MI ρ (by simp only [Shape.ev, truth_bool, hz]; simp [hB])
      · split at hq
        · rename_i q' hq'
          have eq' := sym_val (Ms := Ms) hwP hG (symNode_sym hq').2
          simp only [Rule.ival, eA, eB, intOf_num] at eq'
          rw [vq] at eq'
          rw [vq] at Q0 Q1
          have eaux := hex hq hauxl (symNode_sym hq').1 Q0 (by omega) eB eq'
          simp only [hB, if_false] at eaux er
          refine implies_of_right MI ρ (and2_holds MI ρ ?_ ?_)
          · refine eqI_holds MI ρ (ev_same_num MI ρ eA) (ev_lin_add hwP eaux er) ?_
            have := Int.mul_ediv_add_emod A B; omega
          · refine le_holds MI ρ (ev_num1 MI ρ er 1) (ev_same_num MI ρ eB) ?_
            have := Int.emod_lt_of_pos A (show 0 < B by omega); omega
        · cases hq

include hM hw ht hwP htP hG hML hrng hco in
/-- The facts of a rule hold, within the bounds `Trace.ruleOk` checks. -/
theorem ruleFacts_hold (hex : ExactSpec SP P tr Ms) {r : Rule} {aux : Nat} {fs : List Shape} (hok : tr.ruleOk SP P r aux = true)
    (hf : tr.ruleFacts SP P r aux = some fs) : ∀ s ∈ fs, s.ev MI ρ = .bool true := by
  intro s hs
  have hf' := hf
  unfold Trace.ruleFacts at hf'
  obtain ⟨ks, _, rfl⟩ := Option.map_eq_some_iff.mp hf'
  exact ev_of_boolShape MI ρ (facts_bool P r ks aux s hs)
    (ruleFacts_truth hM hw ht hwP htP hG hML hrng hco hex hok hf s hs)

include hwP hG in
/-- The symbol of a real rule takes its value. -/
theorem real_val {x : Nat} {r : RRule} (h : tr.realAt SP P x = some r) :
    ρ x = .num (r.val fun y => (ρ y).toR) := by
  unfold Trace.realAt at h
  split at h
  · rename_i k hk
    split at h
    · rename_i hle
      split at h
      · rename_i r' hm
        simp only [Option.some.injEq] at h; subst h
        obtain ⟨m, rfl⟩ : ∃ m, k = SP.sig.decls.length + m := ⟨k - SP.sig.decls.length, by omega⟩
        rw [Nat.add_sub_cancel_left] at hm
        rw [Low.val_const hwP ((Tab.at_eq _ _).symm.trans hk)]
        exact const_real SP P tr Ms hwP ((Tab.at_eq _ _).symm.trans hm) (fun y hy => ((hG.real m _ ((Tab.at_eq _ _).symm.trans hm)).2 y hy).2)
      · cases h
    · cases h
  · cases h

theorem realNode_real {r : RRule} {x : Nat} (h : tr.realNode SP P r = some x) :
    x < P.nodes.length ∧ tr.realAt SP P x = some r := by
  unfold Trace.realNode at h
  simp only at h
  split at h
  · rename_i hm
    split at h
    · rename_i hx
      simp only [Option.some.injEq] at h; subst h
      refine ⟨hx, ?_⟩
      have e1 := getElem?_idxOf P.nodes _ hx
      have e2 := getElem?_idxOf tr.mints _ hm
      unfold Trace.realAt
      rw [Tab.at_eq, e1]
      simp only [Tab.at_eq, Nat.le_add_right, if_true, Nat.add_sub_cancel_left, e2]
    · cases h
  · cases h

theorem eqR_holds {V : Type} (I : Low.Interp R V) (ρ' : Nat → Val R V) {a b : Shape} {A : R}
    (ha : (a.ev I ρ').toR = A) (hb : (b.ev I ρ').toR = A) : ((eqI a b).ev I ρ').truth = true := by
  simp only [eqI, Shape.ev, Shape.allTrue, truth_bool, ha, hb, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq]
  exact ⟨Std.le_refl A, Std.le_refl A⟩

include hwP hG in
/-- The facts of a real rule hold, `floor` when reals have floors. -/
theorem realFacts_hold (hfl : ∀ r : R, ∃ k : Int, IsFloor r k) {r : RRule} {k : Nat} (hok : r.ok = true)
    (hk : tr.realNode SP P r = some k) : ∀ s ∈ r.facts k, s.ev MI ρ = .bool true := by
  have ek := real_val (Ms := Ms) hwP hG (realNode_real hk).2
  intro s hs
  have hb : ∀ {s : Shape}, (s.ev MI ρ).truth = true → boolShape s = true → s.ev MI ρ = .bool true :=
    fun h hbs => ev_of_boolShape MI ρ hbs h
  cases r with
  | rat p q =>
    simp only [RRule.facts, List.mem_singleton] at hs; subst hs
    simp only [RRule.ok, decide_eq_true_eq] at hok
    have hq : ((q : Int) : R) ≠ 0 := cast_ne_zero (by omega)
    refine hb (eqR_holds MI ρ (A := (p : R)) ?_ ?_) rfl
    · simp only [Shape.ev, Lia.eval, ek, toR_num, RRule.val, Lia.rat_intCast]
      grind
    · simp only [Shape.ev, Lia.eval, toR_num]; grind
  | ratmul p q t =>
    simp only [RRule.facts, List.mem_singleton] at hs; subst hs
    simp only [RRule.ok, decide_eq_true_eq] at hok
    have hq : ((q : Int) : R) ≠ 0 := cast_ne_zero (by omega)
    refine hb (eqR_holds MI ρ (A := (p : R) * (ρ t).toR) ?_ ?_) rfl
    · simp only [Shape.ev, Lia.eval, ek, toR_num, RRule.val, Lia.rat_intCast]
      grind
    · simp only [Shape.ev, Lia.eval, Lia.rat_intCast, toR_num]; grind
  | floor t =>
    have ⟨f0, f1⟩ := floorOf_spec (hfl (ρ t).toR)
    simp only [RRule.facts, List.mem_cons, List.mem_nil_iff, or_false] at hs
    rcases hs with rfl | rfl
    · refine hb ?_ rfl
      simp only [Shape.ev, truth_bool, ek, toR_num, RRule.val, decide_eq_true_eq]
      exact f0
    · refine hb ?_ (by rfl)
      simp only [Shape.ev, Lia.eval, truth_bool, ek, toR_num, RRule.val, decide_eq_true_eq, rat_one]
      grind

end

end Vik.Lower
