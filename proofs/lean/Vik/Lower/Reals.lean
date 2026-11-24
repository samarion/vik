import Vik.Lower.Defs

/-!
# Operations on reals

Rational literals, division by a literal, `to_real`, `to_int` and `is_int`.
The lowering keeps integers as numbers and makes the rest symbols: `rat(p, q)`
for a rational, `ratmul(p, q, t)` for `p / q · t`, and `floor(t)` for
`to_int`. `Trace.realOk` checks those, and `realOk_sound` proves that the
lowered node takes the value of the surface one.
-/

set_option linter.unusedSectionVars false

namespace Vik.Lower

open Lean.Grind Vik.Real Vik.Low Vik.Surf

variable {R U : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R]
  [OrderedRing R] [IsCharP R 0]

attribute [local instance low] Lean.Grind.Ring.intCast

/-! ## Rationals -/

theorem cast_pos {q : Int} (hq : 0 < q) : (0 : R) < (q : R) := by
  have h1 := cast_le (R := R) (show 1 ≤ q by omega)
  have := OrderedRing.zero_lt_one (R := R)
  rw [Ring.intCast_one] at h1
  exact Std.lt_of_lt_of_le this h1

theorem div_eq_of_mul {a b c : Int} (hb : b ≠ 0) (h : c * b = a) : (a : R) / (b : R) = (c : R) := by
  have := cast_ne_zero (R := R) hb
  subst h; rw [Ring.intCast_mul]; grind

theorem div_eq_div {p q p' q' : Int} (hq : q ≠ 0) (hq' : q' ≠ 0) (h : p' * q = p * q') :
    (p' : R) / (q' : R) = (p : R) / (q : R) := by
  have e := congrArg (fun z : Int => (z : R)) h
  simp only [Ring.intCast_mul] at e
  have := cast_ne_zero (R := R) hq
  have := cast_ne_zero (R := R) hq'
  grind

/-- The floor of `p / q` is the integer quotient. -/
theorem floor_rat (p : Int) {q : Int} (hq : 0 < q) : IsFloor ((p : R) / (q : R)) (p / q) := by
  have hq0 := cast_pos (R := R) hq
  have hqne := cast_ne_zero (R := R) (show q ≠ 0 by omega)
  have hx : (p : R) / (q : R) * (q : R) = (p : R) := by grind
  have k1 : (p / q) * q ≤ p := Int.ediv_mul_le p (by omega)
  have k2 : p < (p / q + 1) * q := by
    have := Int.lt_ediv_add_one_mul_self p hq; rw [Int.add_mul, Int.one_mul]; rw [Int.add_mul, Int.one_mul] at this
    omega
  have c1 := cast_le (R := R) k1
  have c2 := cast_le (R := R) (show p + 1 ≤ (p / q + 1) * q by omega)
  simp only [Ring.intCast_mul, Ring.intCast_add, Ring.intCast_one] at c1 c2
  constructor
  · apply Classical.byContradiction; intro hn
    have hlt : (p : R) / (q : R) < ((p / q : Int) : R) :=
      Classical.byContradiction fun h2 => hn (Std.not_lt.mp h2)
    have := OrderedRing.mul_lt_mul_of_pos_right hlt hq0
    rw [hx] at this
    grind
  · apply Classical.byContradiction; intro hn
    have hle : ((p / q : Int) : R) + 1 ≤ (p : R) / (q : R) := Std.not_lt.mp hn
    have := OrderedRing.mul_le_mul_of_nonneg_left hle (Std.le_of_lt hq0)
    have e : (q : R) * ((p : R) / (q : R)) = p := by grind
    rw [e] at this
    grind

theorem floorOf_rat (p : Int) {q : Int} (hq : 0 < q) : floorOf ((p : R) / (q : R)) = p / q :=
  floor_unique (floorOf_spec ⟨_, floor_rat p hq⟩) (floor_rat p hq)

theorem floorOf_int (c : Int) : floorOf ((c : R)) = c := by
  have h : IsFloor (c : R) c := ⟨Std.le_refl _, by
    have := OrderedRing.zero_lt_one (R := R); grind⟩
  exact floor_unique (floorOf_spec ⟨_, h⟩) h

open Classical in
theorem isInt_rat (p : Int) {q : Int} (hq : 0 < q) :
    decide ((p : R) / (q : R) = ((floorOf ((p : R) / (q : R)) : Int) : R)) = (p % q == 0) := by
  rw [floorOf_rat p hq]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, beq_iff_eq]
  constructor
  · intro h
    have hqne := cast_ne_zero (R := R) (show q ≠ 0 by omega)
    have e : (p : R) = ((p / q * q : Int) : R) := by rw [Ring.intCast_mul]; grind
    have := cast_inj e
    have := Int.emod_add_ediv p q
    rw [Int.mul_comm] at this
    omega
  · intro h
    exact div_eq_of_mul (by omega) (Int.ediv_mul_cancel (Int.dvd_of_emod_eq_zero h))

section
variable {SP : SProblem} {P : Problem} {tr : Trace} {Ms : Surf.Model R U}
  (hM : Ms.Sound SP.sig) (hw : Surf.wellFormed SP.nodes = true) (ht : Surf.typed SP.sig SP.nodes SP.sortOf = true)
  (hwP : Low.wellFormed P.nodes = true) (htP : Low.typed P.sig P.nodes P.sortOf = true)
  (hG : SigSpec SP P tr) (hML : (lowModel SP P tr Ms).Sound P.sig P.bvIndex)
  (hrng : ∀ j < P.nodes.length,
    inRange P.bvIndex (P.sortOf[j]?.getD 0) (Low.val (lowModel SP P tr Ms).toInterp P.nodes j))

set_option quotPrecheck false in
local notation "ρ" => Low.val (lowModel SP P tr Ms).toInterp P.nodes
set_option quotPrecheck false in
local notation "vs" => Surf.val Ms.toInterp SP.nodes
set_option quotPrecheck false in
local notation "MI" => (lowModel SP P tr Ms).toInterp

include hwP hG in
/-- A rational. -/
theorem ratOk_sound {l : Nat} {p : Int} {q : Nat} (h : tr.ratOk SP P l p q = true) :
    0 < q ∧ ρ l = .num ((p : R) / ((q : Int) : R)) := by
  unfold Trace.ratOk at h
  try simp only [Tab.at_eq] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hq, h⟩ := h
  refine ⟨hq, ?_⟩
  split at h
  · rename_i c hc
    rw [Low.val_num hwP hc]
    congr 1
    exact (div_eq_of_mul (by omega) (by simpa using h)).symm
  · split at h
    · rename_i p' q' hr
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
      rw [real_val (Ms := Ms) hwP hG hr]
      simp only [RRule.val]
      congr 1
      exact div_eq_div (by omega) (by omega) h.2
    · cases h

include hwP htP hG hML hrng in
/-- A rational multiple of `t`. -/
theorem ratmulOk_sound {l t : Nat} {p : Int} {q : Nat} (h : tr.ratmulOk SP P l p q t = true)
    (hl : l < P.nodes.length) :
    ρ l = .num ((p : R) / ((q : Int) : R) * (ρ t).toR) := by
  unfold Trace.ratmulOk at h
  try simp only [Tab.at_eq] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨hq, h | h⟩ := h
  · obtain ⟨hdiv, hf⟩ := h
    have lt := lin_val hwP (tr := tr) (Ms := Ms) (SP := SP) t
    rw [fits_sound hML hwP htP hrng l hl _ hf]
    simp only [Shape.ev]
    have e := evf_scale ρ (lin P.nodes t) (p / q)
    unfold evf at e
    rw [e, ← lt, div_eq_of_mul (c := p / q) (by omega) (Int.ediv_mul_cancel (Int.dvd_of_emod_eq_zero hdiv))]
  · split at h
    · rename_i p' q' t' hr
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
      obtain ⟨⟨rfl, _⟩, hc⟩ := h
      rw [real_val (Ms := Ms) hwP hG hr]
      simp only [RRule.val]
      rw [div_eq_div (by omega) (by omega) hc]
    · cases h

omit [IsCharP R 0] in
open Classical in
theorem eqR_ev {V : Type} (I : Low.Interp R V) (ρ' : Nat → Val R V) {a b : Shape} {A B : R}
    (ha : (a.ev I ρ').toR = A) (hb : (b.ev I ρ').toR = B) : (eqI a b).ev I ρ' = .bool (decide (A = B)) := by
  simp only [eqI, Shape.ev, Shape.allTrue, truth_bool, ha, hb, Bool.and_true]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2⟩; exact Std.IsPartialOrder.le_antisymm _ _ h1 h2
  · intro h; rw [h]; exact ⟨Std.le_refl _, Std.le_refl _⟩

include hM hw ht hwP hG in
/-- A literal. -/
theorem litOf_sound {a : Nat} {p : Int} {q : Nat} (h : tr.litOf SP P a = some (p, q)) (ha : a < SP.nodes.length)
    (e : ρ (tr.at a) = enc (vs a)) : 0 < q ∧ vs a = .num ((p : R) / ((q : Int) : R)) := by
  unfold Trace.litOf at h
  try simp only [Tab.at_eq] at h
  split at h
  · rename_i p' q' hn
    split at h
    · rename_i hq
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      refine ⟨hq, ?_⟩
      rw [Surf.val_node (I := Ms.toInterp) hw hn]; rfl
    · cases h
  · split at h
    · rename_i hnum
      split at h
      · rename_i c hc
        simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
        refine ⟨by decide, ?_⟩
        obtain ⟨r, hr⟩ := v_num hM hw ht ha hnum
        have l := lin_ev hwP e
        rw [constOf_eval hc, hr, toR_num] at l
        rw [hr, ← l]
        congr 1
        have : ((1 : Nat) : Int) = 1 := rfl
        rw [this, Ring.intCast_one]; grind
      · split at h
        · rename_i p' q' hr
          split at h
          · rename_i hq
            simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
            refine ⟨hq, enc_inj ?_⟩
            rw [← e, real_val (Ms := Ms) hwP hG hr]; rfl
          · cases h
        · cases h
    · cases h

include hM hw ht hwP hG in
/-- The literal factors of a product. -/
theorem mulLits_sound {as : List Nat} {p : Int} {q : Nat} {o : Option Nat}
    (h : tr.mulLits SP P as = some ((p, q), o))
    (has : ∀ a ∈ as, a < SP.nodes.length ∧ ρ (tr.at a) = enc (vs a)) :
    0 < q ∧ (∀ t, o = some t → t ∈ as) ∧
      prodR (as.map vs) = (p : R) / ((q : Int) : R) * (match o with | none => 1 | some t => (vs t).toR) := by
  induction as generalizing p q o with
  | nil =>
    simp only [Trace.mulLits, List.foldr_nil, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    refine ⟨by decide, by simp, ?_⟩
    simp only [List.map_nil, prodR]
    have : ((1 : Nat) : Int) = 1 := rfl
    rw [this, Ring.intCast_one]; grind
  | cons a as ih =>
    have hr : ∃ r, tr.mulLits SP P as = some r ∧ _ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨⟨p', q'⟩, o'⟩, hr, hf⟩ := hr
    obtain ⟨hq', ho', he⟩ := ih hr (fun b hb => has b (List.mem_cons_of_mem a hb))
    obtain ⟨hal, ea⟩ := has a List.mem_cons_self
    simp only [List.map_cons, prodR]
    rcases hl : tr.litOf SP P a with _ | ⟨pa, qa⟩
    · cases o' with
      | none =>
        simp only [hl, Option.some.injEq, Prod.mk.injEq] at hf
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hf
        refine ⟨hq', fun t ht => by simp only [Option.some.injEq] at ht; subst ht; exact List.mem_cons_self, ?_⟩
        rw [he]
        grind
      | some _ => simp only [hl, reduceCtorEq] at hf
    · simp only [hl, Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hf
      obtain ⟨hqa, hva⟩ := litOf_sound hM hw ht hwP hG hl hal ea
      refine ⟨Nat.mul_pos hqa hq', fun t ht => List.mem_cons_of_mem a (ho' t ht), ?_⟩
      rw [he, hva, toR_num]
      have h1 := cast_ne_zero (R := R) (show (qa : Int) ≠ 0 by omega)
      have h2 := cast_ne_zero (R := R) (show (q' : Int) ≠ 0 by omega)
      simp only [Int.natCast_mul, Ring.intCast_mul]
      grind

include hM hw ht hwP htP hG hML hrng in
open Classical in
/-- The operations on reals. -/
theorem realOk_sound (hD : ∀ d ∈ SP.defs, d.Holds SP.sig Ms) {i : Nat} {n : SNode} (hn : SP.nodes[i]? = some n) (hl : tr.at i < P.nodes.length)
    (hb : tr.realOk SP P i = true) (ih : ∀ c < i, ρ (tr.at c) = enc (vs c)) :
    ρ (tr.at i) = enc (vs i) := by
  have hil := lt_of_get hn
  have hty := typed_at hM hw ht hn
  have hv := Surf.val_node (I := Ms.toInterp) hw hn
  have hch := children_lt hw hn
  cases n with
  | rat p q =>
    simp only [Tab.at_eq, Trace.realOk, hn] at hb
    obtain ⟨_, e⟩ := ratOk_sound (Ms := Ms) hwP hG hb
    rw [e, hv]; rfl
  | toReal a =>
    simp only [Tab.at_eq, Trace.realOk, hn] at hb
    have hai := hch a (by simp [SNode.children])
    simp only [beq_iff_eq] at hb
    simp only [Tab.at_eq, Tab.at_eq, Surf.nodeTyped, Bool.and_eq_true] at hty
    obtain ⟨r, hr⟩ := v_num hM hw ht (a := a) (by omega) hty.2
    rw [hb, ih a hai, hv]
    simp only [Surf.evalNode, surf_get_values, hr, toR_num]
  | toInt a =>
    simp only [Tab.at_eq, Trace.realOk, hn] at hb
    have hai := hch a (by simp [SNode.children])
    have ea := ih a hai
    simp only [Surf.evalNode, surf_get_values] at hv
    rw [hv]
    split at hb
    · rename_i p q hlit
      obtain ⟨hq, hva⟩ := litOf_sound hM hw ht hwP hG hlit (by omega) ea
      rw [Low.val_num hwP (by simpa using hb), hva, toR_num, floorOf_rat p (by omega)]; rfl
    · rw [real_val (Ms := Ms) hwP hG (beq_iff_eq.mp hb)]
      simp only [RRule.val, ea, toR_enc]; rfl
  | isInt a =>
    simp only [Tab.at_eq, Trace.realOk, hn] at hb
    have hai := hch a (by simp [SNode.children])
    have ea := ih a hai
    simp only [Surf.evalNode, surf_get_values] at hv
    rw [hv]
    split at hb
    · rename_i p q hlit
      obtain ⟨hq, hva⟩ := litOf_sound hM hw ht hwP hG hlit (by omega) ea
      have hx : (vs a).toR = (p : R) / ((q : Int) : R) := by rw [hva, toR_num]
      have hi := isInt_rat (R := R) p (q := (q : Int)) (by omega)
      have e2 : decide ((vs a).toR = ((floorOf (vs a).toR : Int) : R)) = (p % (q : Int) == 0) := by
        rw [← hi]; exact decide_eq_decide.mpr (by rw [hx])
      simp only [beq_iff_eq] at hb
      split at hb
      · rename_i h0
        rw [Low.val_node hwP hb]
        simp only [Low.evalNode, enc_bool]
        congr 1; rw [e2]; simpa using h0
      · rename_i h0
        rw [Low.val_node hwP hb]
        simp only [Low.evalNode, enc_bool]
        congr 1; rw [e2]; simpa using h0
    · split at hb
      · rename_i k hk
        have ek := real_val (Ms := Ms) hwP hG (realNode_real hk).2
        simp only [RRule.val] at ek
        rw [ea, toR_enc] at ek
        rw [fits_sound hML hwP htP hrng _ hl _ hb, enc_bool]
        refine eqR_ev MI ρ ?_ ?_
        · show (ρ (tr.at a)).toR = _; rw [ea, toR_enc]
        · show (ρ k).toR = _; rw [ek, toR_num]
      · cases hb
  | div as =>
    simp only [Tab.at_eq, Trace.realOk, hn] at hb
    match as, hb, hch, hv with
    | [a, b], hb, hch, hv =>
    simp only at hb
    have hai := hch a (by simp [SNode.children])
    have hbi := hch b (by simp [SNode.children])
    simp only [Surf.evalNode, surf_get_values, List.map_cons, List.map_nil, Surf.divR] at hv
    rw [hv]
    split at hb
    · rename_i pb qb hlb
      obtain ⟨hqb, hvb⟩ := litOf_sound hM hw ht hwP hG hlb (by omega) (ih b hbi)
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hb
      obtain ⟨hpb, hb⟩ := hb
      rw [hvb, toR_num]
      have hs : (pb.sign : Int) * (pb.natAbs : Int) = pb := Int.sign_mul_natAbs pb
      have hqbR := cast_ne_zero (R := R) (show (qb : Int) ≠ 0 by omega)
      have hpbR := cast_ne_zero (R := R) hpb
      have habs : ((pb.natAbs : Nat) : Int) ≠ 0 := by omega
      have hsR : ((pb.sign : Int) : R) * (((pb.natAbs : Nat) : Int) : R) = (pb : R) := by
        rw [← Ring.intCast_mul, hs]
      have hsq : ((pb.sign : Int) : R) * ((pb.sign : Int) : R) = 1 := by
        rw [← Ring.intCast_mul]
        rcases Int.lt_or_gt_of_ne hpb with h | h
        · rw [Int.sign_eq_neg_one_of_neg h, show (-1 : Int) * -1 = 1 by decide, Ring.intCast_one]
        · rw [Int.sign_eq_one_of_pos h, show (1 : Int) * 1 = 1 by decide, Ring.intCast_one]
      split at hb
      · rename_i pa qa hla
        obtain ⟨hqa, hva⟩ := litOf_sound hM hw ht hwP hG hla (by omega) (ih a hai)
        obtain ⟨_, e⟩ := ratOk_sound (Ms := Ms) hwP hG hb
        rw [e, hva, toR_num]
        simp only [enc_num]
        congr 1
        have hqaR := cast_ne_zero (R := R) (show (qa : Int) ≠ 0 by omega)
        have habsR := cast_ne_zero (R := R) habs
        simp only [Int.natCast_mul, Ring.intCast_mul]
        grind
      · rw [ratmulOk_sound hwP htP hG hML hrng hb hl, ih a hai, toR_enc]
        simp only [enc_num]
        congr 1
        have habsR := cast_ne_zero (R := R) habs
        simp only [Ring.intCast_mul]
        grind
    · cases hb
    | [], hb, _, _ => exact defOk_sound hM hw ht hD hn (by simpa [Trace.realOk, hn] using hb) ih
    | [_], hb, _, _ => exact defOk_sound hM hw ht hD hn (by simpa [Trace.realOk, hn] using hb) ih
    | _ :: _ :: _ :: _, hb, _, _ => exact defOk_sound hM hw ht hD hn (by simpa [Trace.realOk, hn] using hb) ih
  | mul as =>
    simp only [Tab.at_eq, Trace.realOk, hn] at hb
    have has : ∀ a ∈ as, a < SP.nodes.length ∧ ρ (tr.at a) = enc (vs a) := fun a m =>
      have := hch a (by simp [SNode.children, m]); ⟨by omega, ih a this⟩
    simp only [Surf.evalNode, surf_get_values] at hv
    rw [hv]
    split at hb
    · rename_i p q hm
      obtain ⟨_, _, e⟩ := mulLits_sound hM hw ht hwP hG hm has
      obtain ⟨_, e'⟩ := ratOk_sound (Ms := Ms) hwP hG hb
      rw [e', show as.map (Low.get (Surf.values Ms.toInterp SP.nodes)) = as.map vs from rfl, e]
      simp only [enc_num]
      congr 1; grind
    · rename_i p q t hm
      obtain ⟨_, ht', e⟩ := mulLits_sound hM hw ht hwP hG hm has
      rw [ratmulOk_sound hwP htP hG hML hrng hb hl, (has t (ht' t rfl)).2, toR_enc,
        show as.map (Low.get (Surf.values Ms.toInterp SP.nodes)) = as.map vs from rfl, e]
      rfl
    · cases hb
  | _ => exact defOk_sound hM hw ht hD hn (by simpa [Trace.realOk, hn] using hb) ih

end

end Vik.Lower
