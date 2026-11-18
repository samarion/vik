import Vik.Lower.Facts
import Vik.Bits
import Vik.Shifts

/-!
# Bitwise operations through bits

`bvand`, `bvor` and `bvxor` lower bit by bit: the bits of each operand (a
constant's, a sum of bits, or the symbols of a `bits` decomposition), a gate
per bit, and the sum of the gates' bits. `Trace.bitwiseOk` checks that, and
`bitwiseOk_sound` proves that the lowered node takes the value of the
operation.
-/

set_option linter.unusedSectionVars false

namespace Vik.Lower

open Lean.Grind Vik.Real Vik.Low Vik.Surf

variable {R U : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R]
  [OrderedRing R] [IsCharP R 0]

attribute [local instance low] Lean.Grind.Ring.intCast

theorem constOf_eval {f : Lia.Form × Int} {c : Int} (h : constOf f = some c) (ρ' : Nat → R) :
    Lia.eval ρ' f.1 + (f.2 : R) = (c : R) := by
  unfold constOf at h
  split at h
  · rename_i he
    cases h
    have e := eval_canon ρ' f.1
    rw [List.isEmpty_iff.mp he] at e
    simp only [Lia.eval] at e
    rw [← e]; grind
  · cases h

/-- The value of a linear combination. -/
noncomputable def evf {V : Type} (ρ' : Nat → Val R V) (f : Lia.Form × Int) : R :=
  Lia.eval (fun u => (ρ' u).toR) f.1 + (f.2 : R)

/-- Bit `r` is `b`: its linear combination is `0` or `1`. -/
def RefVal {V : Type} (ρ' : Nat → Val R V) (r : BitRef) (b : Bool) : Prop :=
  evf ρ' r.form = ((bitValue b : Int) : R)

/-- The operation of the gates. -/
def opB : BvBin → Bool → Bool → Bool
  | .and => (· && ·)
  | .or => (· || ·)
  | _ => (· ^^ ·)

section generic
variable {V : Type} (ρ' : Nat → Val R V)

theorem bitValue_cast_inj {a b : Bool} (h : ((bitValue a : Int) : R) = ((bitValue b : Int) : R)) : a = b := by
  have := cast_inj h
  cases a <;> cases b <;> simp_all [bitValue]

open Classical in
theorem le_bit (b : Bool) : decide ((0 : R) + ((1 : Int) : R) ≤ ((bitValue b : Int) : R)) = b := by
  have e : (0 : R) + ((1 : Int) : R) = ((1 : Int) : R) := by grind
  rw [e]
  cases b
  · simp only [bitValue, Bool.false_eq_true, if_false, decide_eq_false_iff_not]
    intro h; exact absurd (cast_le_iff.mp h) (by decide)
  · simp only [bitValue, if_true, decide_eq_true_eq]; exact cast_le_iff.mpr (Int.le_refl 1)

theorem refVal_lit {c b : Bool} : RefVal ρ' (.lit c) b ↔ b = c := by
  unfold RefVal evf
  simp only [BitRef.form, Lia.eval]
  constructor
  · intro h
    have : ((if c then 1 else 0 : Int) : R) = ((bitValue b : Int) : R) := by grind
    exact (bitValue_cast_inj (R := R) (by simpa [bitValue] using this.symm))
  · rintro rfl; simp only [bitValue]; grind

theorem refVal_sym {k : Nat} {b : Bool} : RefVal ρ' (.sym k) b ↔ (ρ' k).toR = ((bitValue b : Int) : R) := by
  unfold RefVal evf
  simp only [BitRef.form, Lia.eval, rat_one]
  constructor <;> intro h <;> grind

theorem refVal_neg {r : BitRef} {b : Bool} : RefVal ρ' (.neg r) b ↔ RefVal ρ' r (!b) := by
  unfold RefVal evf
  simp only [BitRef.form, Lia.eval_neg, bitValue_not, Ring.intCast_sub]
  constructor <;> intro h <;> grind

theorem refVal_flip {r : BitRef} {b : Bool} : RefVal ρ' r.flip b ↔ RefVal ρ' r (!b) := by
  cases r with
  | lit c => simp only [BitRef.flip, refVal_lit]; cases b <;> cases c <;> simp
  | sym k => simp only [BitRef.flip, refVal_neg]
  | neg r => simp only [BitRef.flip, refVal_neg, Bool.not_not]

theorem refVal_unique {r : BitRef} {a b : Bool} (ha : RefVal ρ' r a) (hb : RefVal ρ' r b) : a = b := by
  unfold RefVal at ha hb
  exact bitValue_cast_inj (by rw [← ha, ← hb])

theorem bitsForm_ev (d : Nat → BitRef) (bs : Nat → Bool) :
    ∀ n, (∀ i < n, RefVal ρ' (d i) (bs i)) →
      evf ρ' (bitsForm d n) = ((bitSum n (fun i => bitValue (bs i)) : Int) : R)
  | 0, _ => by simp only [bitsForm, bitSum, evf, Lia.eval]; grind
  | n + 1, h => by
    have ih := bitsForm_ev d bs n (fun i hi => h i (by omega))
    have hn := h n (by omega)
    unfold RefVal at hn
    unfold evf at ih hn ⊢
    simp only [bitsForm, eval_append, Lia.eval_scale, Lia.rat_intCast, bitSum, Ring.intCast_add,
      Ring.intCast_mul] at ih hn ⊢
    grind

theorem bitSum_bounds (f : Nat → Bool) : ∀ n, 0 ≤ bitSum n (fun i => bitValue (f i)) ∧
    bitSum n (fun i => bitValue (f i)) ≤ 2 ^ n - 1
  | 0 => by simp [bitSum]
  | n + 1 => by
    have := bitSum_bounds f n
    have hp : (2 : Int) ^ (n + 1) = 2 * 2 ^ n := by rw [Int.pow_succ]; grind
    have hb : 0 ≤ bitValue (f n) ∧ bitValue (f n) ≤ 1 := by unfold bitValue; split <;> omega
    have h1 := Int.mul_nonneg (Int.le_of_lt (pow_pos' n)) hb.1
    have h2 := Int.mul_le_mul_of_nonneg_left hb.2 (Int.le_of_lt (pow_pos' n))
    rw [Int.mul_one] at h2
    simp only [bitSum]
    omega

theorem bitSum_unique (f g : Nat → Bool) :
    ∀ n, bitSum n (fun i => bitValue (f i)) = bitSum n (fun i => bitValue (g i)) → ∀ i < n, f i = g i
  | 0, _, i, hi => absurd hi (by omega)
  | n + 1, h, i, hi => by
    simp only [bitSum] at h
    have bf := bitSum_bounds f n
    have bg := bitSum_bounds g n
    have hfn : f n = g n := by
      have t1 : bitValue true = 1 := rfl
      have t0 : bitValue false = 0 := rfl
      have hp := pow_pos' n
      cases e1 : f n <;> cases e2 : g n <;> simp only [e1, e2, t0, t1, Int.mul_one, Int.mul_zero, Int.add_zero] at h <;>
        first | rfl | omega
    have hrest : bitSum n (fun i => bitValue (f i)) = bitSum n (fun i => bitValue (g i)) := by
      rw [hfn] at h; omega
    by_cases hin : i = n
    · subst hin; exact hfn
    · exact bitSum_unique f g n hrest i (by omega)

theorem gateOf_ref {op : BvBin} {x y r : BitRef} {bx by' : Bool} (h : gateOf op x y = .ref r)
    (hx : RefVal ρ' x bx) (hy : RefVal ρ' y by') : RefVal ρ' r (opB op bx by') := by
  have L : ∀ {c b : Bool}, RefVal ρ' (.lit c) b → b = c := fun h => (refVal_lit ρ').mp h
  have N : ∀ {r : BitRef} {b : Bool}, RefVal ρ' r (!b) → RefVal ρ' (.neg r) b := fun h => (refVal_neg ρ').mpr h
  unfold gateOf at h
  cases op <;> simp only at h <;>
    repeat' (split at h <;> try (simp only [Gate.ref.injEq, reduceCtorEq] at h))
  all_goals (subst_vars; first
    | (have e := refVal_unique ρ' hx hy; subst e; simp_all [refVal_lit, refVal_neg, opB]; done)
    | (simp_all [refVal_lit, refVal_neg, opB]; done)
    | (rename_i hor; rcases hor with rfl | rfl <;> simp_all [refVal_lit, refVal_neg, opB]; done))

theorem gateOf_and {op : BvBin} {x y r s : BitRef} (h : gateOf op x y = .and r s) : op = .and ∧ r = x ∧ s = y := by
  unfold gateOf at h
  cases op <;> simp only at h <;>
    repeat' (split at h <;> try (simp only [Gate.and.injEq, reduceCtorEq] at h))
  all_goals (obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl, rfl⟩)

theorem gateOf_or {op : BvBin} {x y r s : BitRef} (h : gateOf op x y = .or r s) : op = .or ∧ r = x ∧ s = y := by
  unfold gateOf at h
  cases op <;> simp only at h <;>
    repeat' (split at h <;> try (simp only [Gate.or.injEq, reduceCtorEq] at h))
  all_goals (obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl, rfl⟩)

theorem gateOf_xor {op : BvBin} {x y r s : BitRef} (h : gateOf op x y = .xor r s) :
    (∀ a b, opB op a b = (a ^^ b)) ∧ r = x ∧ s = y := by
  unfold gateOf at h
  cases op <;> simp only at h <;>
    repeat' (split at h <;> try (simp only [Gate.xor.injEq, reduceCtorEq] at h))
  all_goals (obtain ⟨rfl, rfl⟩ := h; exact ⟨fun _ _ => rfl, rfl, rfl⟩)

theorem mapM_length {α β : Type} (f : α → Option β) : ∀ (l : List α) (ks : List β), l.mapM f = some ks →
    ks.length = l.length
  | [], ks, h => by simp at h; subst h; rfl
  | a :: l, ks, h => by
    simp only [List.mapM_cons] at h
    cases ha : f a with
    | none => simp [ha] at h
    | some b =>
      cases hl : l.mapM f with
      | none => simp [ha, hl] at h
      | some bs =>
        simp [ha, hl] at h; subst h
        simp [mapM_length f l bs hl]

theorem bitAt_map {α : Type} (g : α → BitRef) (l : List α) {i : Nat} (hi : i < l.length) :
    bitAt (l.map g) i = g l[i] := by
  simp [bitAt, hi]

theorem bit_beq (K : Int) (i : Nat) : bitValue (bit K i == 1) = bit K i := by
  have := bit_range K i
  by_cases h : bit K i = 1
  · simp [h, bitValue]
  · have : bit K i = 0 := by omega
    simp [this, bitValue]

theorem ofNat_low {w k : Nat} (hk : k ≤ w) {y : BitVec w} (hy : Vik.val y = 2 ^ k - 1) :
    y = BitVec.ofNat w (2 ^ k - 1) := by
  apply Vik.val_inj.mp
  rw [hy]
  have h1 : 2 ^ k ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hk
  have h2 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  simp only [Vik.val, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega), Int.ofNat_sub h2]
  simp

theorem ofNat_high {w k : Nat} (hk : k ≤ w) {y : BitVec w} (hy : Vik.val y = 2 ^ w - 2 ^ k) :
    y = BitVec.ofNat w (2 ^ w - 2 ^ k) := by
  apply Vik.val_inj.mp
  rw [hy]
  have h1 : 2 ^ k ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hk
  have h2 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  simp only [Vik.val, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega), Int.ofNat_sub h1]
  simp

theorem evf_neg {V : Type} (ρ' : Nat → Val R V) (f : Lia.Form × Int) :
    evf ρ' (Lia.neg f.1, -f.2) = -evf ρ' f := by
  unfold evf; simp only [Lia.eval_neg, Ring.intCast_neg]; grind

theorem evf_add {V : Type} (ρ' : Nat → Val R V) (f g : Lia.Form × Int) :
    evf ρ' (f.1 ++ g.1, f.2 + g.2) = evf ρ' f + evf ρ' g := by
  unfold evf; simp only [eval_append, Ring.intCast_add]; grind

theorem evf_sub {V : Type} (ρ' : Nat → Val R V) (f g : Lia.Form × Int) :
    evf ρ' (f.1 ++ Lia.neg g.1, f.2 - g.2) = evf ρ' f - evf ρ' g := by
  unfold evf; simp only [eval_append, Lia.eval_neg, Ring.intCast_sub]; grind

theorem evf_shift {V : Type} (ρ' : Nat → Val R V) (f : Lia.Form × Int) (k : Int) :
    evf ρ' (f.1, f.2 + k) = evf ρ' f + (k : R) := by
  unfold evf; simp only [Ring.intCast_add]; grind

theorem evf_scale {V : Type} (ρ' : Nat → Val R V) (f : Lia.Form × Int) (k : Int) :
    evf ρ' (Lia.scale ((k : Int) : Rat) f.1, k * f.2) = (k : R) * evf ρ' f := by
  unfold evf; simp only [Lia.eval_scale, Lia.rat_intCast, Ring.intCast_mul]; grind

theorem evf_const {V : Type} (ρ' : Nat → Val R V) (c : Int) : evf ρ' ([], c) = (c : R) := by
  unfold evf; simp only [Lia.eval]; grind

theorem evf_sym {V : Type} (ρ' : Nat → Val R V) {x : Nat} {X : Int} (hx : ρ' x = .num (X : R)) (a : Int) :
    evf ρ' ([(x, ((a : Int) : Rat))], 0) = ((a * X : Int) : R) := by
  unfold evf; simp only [Lia.eval, hx, toR_num, Lia.rat_intCast, Ring.intCast_mul]; grind

theorem evf_sym2 {V : Type} (ρ' : Nat → Val R V) {x y : Nat} {X Y : Int} (hx : ρ' x = .num (X : R))
    (hy : ρ' y = .num (Y : R)) (a b : Int) :
    evf ρ' ([(x, ((a : Int) : Rat)), (y, ((b : Int) : Rat))], 0) = ((a * X + b * Y : Int) : R) := by
  unfold evf; simp only [Lia.eval, hx, hy, toR_num, Lia.rat_intCast, Ring.intCast_mul, Ring.intCast_add]; grind

theorem evf_sym1 {V : Type} (ρ' : Nat → Val R V) {x : Nat} {X : Int} (hx : ρ' x = .num (X : R)) :
    evf ρ' ([(x, 1)], 0) = (X : R) := by
  unfold evf; simp only [Lia.eval, hx, toR_num, rat_one]; grind

theorem evf_sym2' {V : Type} (ρ' : Nat → Val R V) {x y : Nat} {X Y : Int} (hx : ρ' x = .num (X : R))
    (hy : ρ' y = .num (Y : R)) (b : Int) :
    evf ρ' ([(x, 1), (y, ((b : Int) : Rat))], 0) = ((X + b * Y : Int) : R) := by
  unfold evf; simp only [Lia.eval, hx, hy, toR_num, rat_one, Lia.rat_intCast, Ring.intCast_mul, Ring.intCast_add]
  grind


/-- A stage of a barrel shifter, by `k`. -/
def stepBv {w : Nat} : BvBin → BitVec w → Nat → BitVec w
  | .shl, x, k => x <<< k
  | .lshr, x, k => x >>> k
  | _, x, k => x.sshiftRight k

theorem stagesOf_spec (w : Nat) : w ≤ 2 ^ stagesOf w ∧ stagesOf w ≤ w := by
  unfold stagesOf
  cases hf : (List.range (w + 1)).find? (fun j => decide (w ≤ 2 ^ j)) with
  | none =>
    have h := List.find?_eq_none.mp hf w (List.mem_range.mpr (by omega))
    have : w < 2 ^ w := Nat.lt_two_pow_self
    simp only [decide_eq_true_eq] at h; omega
  | some j =>
    have h1 := List.find?_some hf
    have h2 := List.mem_range.mp (List.mem_of_find?_eq_some hf)
    simp only [decide_eq_true_eq] at h1
    exact ⟨h1, by simp; omega⟩

end generic

/-- The bit of a bit-vector, as `bit` of its value. -/
theorem bit_getLsbD {w : Nat} (x : BitVec w) (i : Nat) : (bit (Vik.val x) i == 1) = x.getLsbD i := by
  rw [bit_val]; cases x.getLsbD i <;> simp

theorem bitValue_getLsbD {w : Nat} (x : BitVec w) (i : Nat) : bit (Vik.val x) i = bitValue (x.getLsbD i) := by
  rw [bit_val]; rfl

theorem val_bitSum {w : Nat} (x : BitVec w) : Vik.val x = bitSum w (fun i => bitValue (x.getLsbD i)) := val_bits x

/-- The bits of the bitwise operations. -/
theorem bitwise_getLsbD {op op' : BvBin} {neg : Bool} (h : bitwiseOf op = some (op', neg)) {w : Nat}
    (x y : BitVec w) (i : Nat) (hi : i < w) :
    ∃ z : BitVec w, Vik.val (op.apply x y) = Vik.val z ∧
      z.getLsbD i = ((opB op' (x.getLsbD i) (y.getLsbD i)) ^^ neg) := by
  cases op <;> simp only [bitwiseOf, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
    obtain ⟨rfl, rfl⟩ := h <;>
    exact ⟨_, rfl, by simp [BvBin.apply, opB, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_xor, hi]⟩

theorem bitwise_val {op op' : BvBin} {neg : Bool} (h : bitwiseOf op = some (op', neg)) {w : Nat}
    (x y : BitVec w) :
    Vik.val (op.apply x y) = bitSum w (fun i => bitValue ((opB op' (x.getLsbD i) (y.getLsbD i)) ^^ neg)) := by
  cases op <;> simp only [bitwiseOf, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
    obtain ⟨rfl, rfl⟩ := h <;>
    (rw [val_bitSum]; exact bitSum_congr fun i hi => by
      simp only [BvBin.width] at hi
      simp [BvBin.apply, BvBin.width, opB, hi])

theorem bitwise_not {op op' : BvBin} {neg : Bool} (h : bitwiseOf op = some (op', neg)) {w : Nat}
    (x y : BitVec w) :
    Vik.val (op.apply x y) = if neg then 2 ^ w - 1 - Vik.val (op'.apply x y) else Vik.val (op'.apply x y) := by
  cases op <;> simp only [bitwiseOf, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
    obtain ⟨rfl, rfl⟩ := h <;> simp [BvBin.apply, BvBin.width, Vik.not_val]

section
variable {SP : SProblem} {P : Problem} {tr : Trace} {Ms : Surf.Model R U}
  (hwP : Low.wellFormed P.nodes = true) (htP : Low.typed P.sig P.nodes P.sortOf = true)
  (hG : SigSpec SP P tr) (hML : (lowModel SP P tr Ms).Sound P.sig P.bvIndex)
  (hrng : ∀ j < P.nodes.length,
    inRange P.bvIndex (P.sortOf[j]?.getD 0) (Low.val (lowModel SP P tr Ms).toInterp P.nodes j))

set_option quotPrecheck false in
local notation "ρ" => Low.val (lowModel SP P tr Ms).toInterp P.nodes
set_option quotPrecheck false in
local notation "MI" => (lowModel SP P tr Ms).toInterp

include hwP htP hML hrng in
theorem fits_num {x : Nat} {f : Lia.Form × Int} {V : Int} (h : fits P.sig P.nodes P.sortOf x (.num f.1 f.2) = true)
    (hx : x < P.nodes.length) (hf : (evf ρ f) = (V : R)) : ρ x = .num (V : R) := by
  rw [fits_sound hML hwP htP hrng x hx _ h]
  simp only [Shape.ev]; unfold evf at hf; rw [hf]

theorem lt_of_get' {x : Nat} {n : Node} (h : P.nodes[x]? = some n) : x < P.nodes.length := by
  rcases Nat.lt_or_ge x P.nodes.length with h' | h'
  · exact h'
  · rw [List.getElem?_eq_none h'] at h; cases h

include hwP htP hG hML hrng in
/-- A `cases` between `1` and `0` on `c` is `1` exactly when `c` holds. -/
theorem casesBit_val {k : Nat} {p : Nat → Bool} (h : tr.casesBit SP P k p = true) :
    ∃ c, c < P.nodes.length ∧ p c = true ∧ ρ k = .num ((bitValue (ρ c).truth : Int) : R) := by
  unfold Trace.casesBit at h
  split at h
  · rename_i c t e lo hi hs
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨ht', he⟩, hp⟩ := h
    have args := (symAt_args hG hs).2
    refine ⟨c, args c (by simp [Rule.args]), hp, ?_⟩
    rw [sym_val hwP hG hs]
    simp only [Rule.ival]
    have et := fits_num hwP htP hML hrng (f := ([], 1)) ht' (args t (by simp [Rule.args])) (evf_const _ 1)
    have ee := fits_num hwP htP hML hrng (f := ([], 0)) he (args e (by simp [Rule.args])) (evf_const _ 0)
    rw [et, ee, intOf_num, intOf_num]
    cases (ρ c).truth <;> rfl
  · cases h

include hwP htP hG hML hrng in
theorem refOk_ex {r : BitRef} (h : tr.refOk SP P r = true) : ∃ b, RefVal ρ r b := by
  induction r with
  | lit c => exact ⟨c, (refVal_lit ρ).mpr rfl⟩
  | sym k =>
    simp only [Trace.refOk, Trace.bitSym] at h
    split at h
    · rename_i u w j hs
      refine ⟨bit (intOf (ρ u)) j == 1, (refVal_sym ρ).mpr ?_⟩
      rw [sym_val hwP hG hs]
      simp only [Rule.ival, toR_num]
      have := bit_range (intOf (ρ u)) j
      congr 1
      by_cases h1 : bit (intOf (ρ u)) j = 1
      · simp [h1, bitValue]
      · have : bit (intOf (ρ u)) j = 0 := by omega
        simp [this, bitValue]
    · obtain ⟨c, _, _, hk⟩ := casesBit_val hwP htP hG hML hrng h
      exact ⟨(ρ c).truth, (refVal_sym ρ).mpr (by rw [hk, toR_num])⟩
  | neg r ih =>
    obtain ⟨b, hb⟩ := ih h
    exact ⟨!b, (refVal_neg ρ).mpr (by simpa using hb)⟩

include hwP htP hG hML hrng in
/-- A formula node fitting a bit has its truth. -/
theorem refFits_sound {r : BitRef} : ∀ {x : Nat} {b : Bool}, tr.refFits SP P x r = true → RefVal ρ r b →
    (ρ x).truth = b := by
  induction r with
  | lit c =>
    intro x b h hb
    rw [(refVal_lit ρ).mp hb]
    simp only [Tab.at_eq, Trace.refFits, beq_iff_eq] at h
    rw [Low.val_node hwP h]
    cases c <;> simp [Low.evalNode, truth_bool]
  | sym k =>
    intro x b h hb
    have hk := (refVal_sym ρ).mp hb
    simp only [Trace.refFits, Bool.or_eq_true] at h
    rcases h with h | h
    · have hx : x < P.nodes.length := by
        unfold fits at h
        rw [Tab.at_eq] at h
        split at h
        · rename_i n hn; exact lt_of_get' hn
        · cases h
      rw [fits_sound hML hwP htP hrng x hx _ h]
      simp only [Shape.ev, Lia.eval, hk, truth_bool, toR_num]
      rw [hk]; exact le_bit (R := R) b
    · obtain ⟨c, _, hc, hkc⟩ := casesBit_val hwP htP hG hML hrng h
      rw [beq_iff_eq.mp hc] at hkc
      rw [hkc, toR_num] at hk
      exact bitValue_cast_inj hk
  | neg r ih =>
    intro x b h hb
    simp only [Tab.at_eq, Trace.refFits] at h
    split at h
    · rename_i y hy
      rw [Low.val_node hwP hy]
      simp only [Low.evalNode, truth_bool]
      have := ih h ((refVal_neg ρ).mp hb)
      change (!(ρ y).truth) = b
      rw [this, Bool.not_not]
    · cases h

include hwP htP hG hML hrng in
theorem refMatch_sound {d : BitRef} : ∀ {r : BitRef} {bd br : Bool}, tr.refMatch SP P d r = true →
    RefVal ρ d bd → RefVal ρ r br → bd = br := by
  induction d with
  | lit c =>
    intro r bd br h hd hr
    unfold Trace.refMatch at h
    simp only [Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h
    · exact refVal_unique ρ hd hr
    · cases r <;> simp at h
  | sym k =>
    intro r bd br h hd hr
    unfold Trace.refMatch at h
    simp only [Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h
    · exact refVal_unique ρ hd hr
    · obtain ⟨c, _, hc, hkc⟩ := casesBit_val hwP htP hG hML hrng h
      have e1 := refFits_sound hwP htP hG hML hrng hc hr
      have hk := (refVal_sym ρ).mp hd
      rw [hkc, toR_num] at hk
      rw [← bitValue_cast_inj hk, e1]
  | neg d ih =>
    intro r bd br h hd hr
    unfold Trace.refMatch at h
    simp only [Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h
    · exact refVal_unique ρ hd hr
    · cases r with
      | neg r =>
        have := ih h ((refVal_neg ρ).mp hd) ((refVal_neg ρ).mp hr)
        simpa using this
      | _ => simp at h

include hwP htP hG hML hrng in
theorem pairFits_sound {p q : Nat} {r s : BitRef} {br bs : Bool} (h : tr.pairFits SP P p q r s = true)
    (hr : RefVal ρ r br) (hs : RefVal ρ s bs) :
    ((ρ p).truth = br ∧ (ρ q).truth = bs) ∨ ((ρ p).truth = bs ∧ (ρ q).truth = br) := by
  unfold Trace.pairFits at h
  simp only [Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨refFits_sound hwP htP hG hML hrng h1 hr, refFits_sound hwP htP hG hML hrng h2 hs⟩
  · exact Or.inr ⟨refFits_sound hwP htP hG hML hrng h1 hs, refFits_sound hwP htP hG hML hrng h2 hr⟩



include hwP htP hG hML hrng in
theorem gateOk_sound {op : BvBin} {x y d : BitRef} {bx by' bd : Bool} (h : tr.gateOk SP P op x y d = true)
    (hx : RefVal ρ x bx) (hy : RefVal ρ y by') (hd : RefVal ρ d bd) : bd = opB op bx by' := by
  unfold Trace.gateOk at h
  have cb : ∀ {k : Nat} {p : Nat → Bool}, RefVal ρ (.sym k) bd → tr.casesBit SP P k p = true →
      ∃ c, c < P.nodes.length ∧ p c = true ∧ bd = (ρ c).truth := by
    intro k p hd h
    obtain ⟨c, hc, hp, hk⟩ := casesBit_val hwP htP hG hML hrng h
    have := (refVal_sym ρ).mp hd
    rw [hk, toR_num] at this
    exact ⟨c, hc, hp, bitValue_cast_inj this.symm⟩
  split at h
  · rename_i r hg
    exact refMatch_sound hwP htP hG hML hrng h hd (gateOf_ref ρ hg hx hy)
  · rename_i r s hg
    obtain ⟨rfl, rfl, rfl⟩ := gateOf_and hg
    split at h
    · obtain ⟨c, _, hp, rfl⟩ := cb hd h
      split at hp
      · rename_i p q hpq
        rw [Low.val_node hwP ((Tab.at_eq _ _).symm.trans hpq)]
        simp only [Low.evalNode, truth_bool, List.all_cons, List.all_nil, Bool.and_true, opB]
        rcases pairFits_sound hwP htP hG hML hrng hp hx hy with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · change ((ρ p).truth && (ρ q).truth) = _; rw [e1, e2]
        · change ((ρ p).truth && (ρ q).truth) = _; rw [e1, e2, Bool.and_comm]
      · cases hp
    · cases h
  · rename_i r s hg
    obtain ⟨rfl, rfl, rfl⟩ := gateOf_or hg
    split at h
    · obtain ⟨c, _, hp, rfl⟩ := cb hd h
      split at hp
      · rename_i p q hpq
        rw [Low.val_node hwP ((Tab.at_eq _ _).symm.trans hpq)]
        simp only [Low.evalNode, truth_bool, List.any_cons, List.any_nil, Bool.or_false, opB]
        rcases pairFits_sound hwP htP hG hML hrng hp hx hy with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · change ((ρ p).truth || (ρ q).truth) = _; rw [e1, e2]
        · change ((ρ p).truth || (ρ q).truth) = _; rw [e1, e2, Bool.or_comm]
      · cases hp
    · cases h
  · rename_i r s hg
    obtain ⟨hop, rfl, rfl⟩ := gateOf_xor hg
    rw [hop]
    split at h
    · obtain ⟨c, _, hp, rfl⟩ := cb hd h
      split at hp
      · rename_i z hz
        split at hp
        · rename_i p q hpq
          rw [Low.val_node hwP ((Tab.at_eq _ _).symm.trans hz)]
          simp only [Low.evalNode, truth_bool]
          change (!(ρ z).truth) = _
          rw [Low.val_node hwP ((Tab.at_eq _ _).symm.trans hpq)]
          simp only [Low.evalNode, truth_bool]
          rcases pairFits_sound hwP htP hG hML hrng hp hx hy with ⟨e1, e2⟩ | ⟨e1, e2⟩
          · change (!((ρ p).truth == (ρ q).truth)) = _; rw [e1, e2]; cases bx <;> cases by' <;> rfl
          · change (!((ρ p).truth == (ρ q).truth)) = _; rw [e1, e2]; cases bx <;> cases by' <;> rfl
        · cases hp
      · cases hp
    · cases h

include hwP htP hG hML hrng in
theorem sumOk_sound {t : Nat} {D : List BitRef} (h : tr.sumOk SP P t D = true) (ht : t < P.nodes.length) :
    ∃ bs : Nat → Bool, (∀ i < D.length, RefVal ρ (bitAt D i) (bs i)) ∧
      ρ t = .num ((bitSum D.length (fun i => bitValue (bs i)) : Int) : R) := by
  unfold Trace.sumOk at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hall, hf⟩ := h
  have ex : ∀ i, ∃ b, i < D.length → RefVal ρ (bitAt D i) b := by
    intro i
    by_cases hi : i < D.length
    · have e : bitAt D i = D[i] := by simp [bitAt, hi]
      obtain ⟨b, hb⟩ := refOk_ex hwP htP hG hML hrng (hall _ (List.getElem_mem hi))
      exact ⟨b, fun _ => e ▸ hb⟩
    · exact ⟨false, fun h => absurd h hi⟩
  refine ⟨fun i => Classical.choose (ex i), fun i hi => Classical.choose_spec (ex i) hi, ?_⟩
  exact fits_num hwP htP hML hrng hf ht
    (bitsForm_ev ρ _ _ _ (fun i hi => Classical.choose_spec (ex i) hi))

theorem decomp_length {u w : Nat} {rs : List BitRef} (h : tr.decomp SP P u w = some rs) : rs.length = w := by
  unfold Trace.decomp at h
  obtain ⟨ks, hks, rfl⟩ := Option.map_eq_some_iff.mp h
  rw [List.length_map, mapM_length _ _ _ hks]; simp

include hwP htP hG hML hrng in
theorem decomp_sound {u w : Nat} {rs : List BitRef} {K : Int} (h : tr.decomp SP P u w = some rs)
    (hu : ρ u = .num (K : R)) : rs.length = w ∧ ∀ i < w, RefVal ρ (bitAt rs i) (bit K i == 1) := by
  unfold Trace.decomp at h
  obtain ⟨ks, hks, rfl⟩ := Option.map_eq_some_iff.mp h
  have hlen : ks.length = w := by rw [mapM_length _ _ _ hks]; simp
  refine ⟨by simp [hlen], fun i hi => ?_⟩
  obtain ⟨k, hk, hsk⟩ := mapM_get _ _ ks hks i (by simpa using hi)
  simp only [List.getElem_range] at hsk
  have ek := sym_val (Ms := Ms) hwP hG (symNode_sym hsk).2
  simp only [Rule.ival, hu, intOf_num] at ek
  have e : ks[i] = k := by
    have := List.getElem?_eq_getElem (l := ks) (i := i) (by omega)
    rw [hk] at this; exact (Option.some.inj this).symm
  rw [bitAt_map _ _ (by omega), e, refVal_sym, ek, toR_num, bit_beq]

include hwP htP hG hML hrng in
/-- The bits `Trace.tbits` reads are the bits of the value. -/
theorem tbits_sound {t w : Nat} {A : List BitRef} {x : BitVec w} (h : tr.tbits SP P t w = some A)
    (ht : t < P.nodes.length) (hv : ρ t = .num ((Vik.val x : Int) : R)) :
    A.length = w ∧ ∀ i < w, RefVal ρ (bitAt A i) (x.getLsbD i) := by
  have hl := lin_val hwP (tr := tr) (Ms := Ms) (SP := SP) t
  rw [hv, toR_num] at hl
  unfold Trace.tbits at h
  simp only at h
  split at h
  · rename_i v hc
    cases h
    have e := constOf_eval hc (fun u => (ρ u).toR)
    rw [← hl] at e
    have := cast_inj e
    subst this
    refine ⟨by simp, fun i hi => ?_⟩
    rw [bitAt_map _ _ (by simpa using hi), refVal_lit, List.getElem_range, bit_getLsbD]
  · split at h
    · rename_i hs
      cases h
      obtain ⟨bs, hbs, hv'⟩ := sumOk_sound hwP htP hG hML hrng hs ht
      have hlen : (decodeBits (lin P.nodes t) w).length = w := by simp [decodeBits]
      rw [hlen] at hbs hv'
      rw [hv] at hv'
      have e := (num_int_eq_iff (U := U ⊕ Nat)).mp hv'
      rw [val_bitSum] at e
      have u := bitSum_unique _ _ w e
      exact ⟨hlen, fun i hi => (u i hi) ▸ hbs i hi⟩
    · split at h
      · rename_i rs hd
        cases h
        obtain ⟨hlen, hb⟩ := decomp_sound hwP htP hG hML hrng hd hv
        exact ⟨hlen, fun i hi => by rw [← bit_getLsbD]; exact hb i hi⟩
      · split at h
        · rename_i u a hcan
          split at h
          · rename_i hcond
            simp only [Bool.and_eq_true, beq_iff_eq] at hcond
            obtain ⟨⟨ha, hc2⟩, hint⟩ := hcond
            obtain ⟨rs, hd, rfl⟩ := Option.map_eq_some_iff.mp h
            have hlen := decomp_length hd
            refine ⟨by simp [hlen], fun i hi => ?_⟩
            have hul : u < P.nodes.length := by
              unfold Trace.decomp at hd
              obtain ⟨ks, hks, _⟩ := Option.map_eq_some_iff.mp hd
              obtain ⟨k, _, hsk⟩ := mapM_get _ _ ks hks 0 (by simp; omega)
              simp only [List.getElem_range] at hsk
              exact (symAt_args hG (symNode_sym hsk).2).2 u (by simp [Rule.args])
            obtain ⟨K, hK⟩ := val_int hwP htP hML hrng hul (by simpa [isIntN] using hint)
            have e2 : Lia.eval (fun v => (ρ v).toR) (lin P.nodes t).1 = -(K : R) := by
              rw [← eval_canon, hcan, ha]
              simp only [Lia.eval, hK, toR_num]
              rw [show (-1 : Rat) = ((-1 : Int) : Rat) from rfl, Lia.rat_intCast, Ring.intCast_neg]
              grind
            rw [e2, hc2] at hl
            have e3 : ((Vik.val x : Int) : R) = ((2 ^ w - 1 - K : Int) : R) := by
              rw [hl, Ring.intCast_sub]; grind
            have hKx : K = Vik.val (~~~x) := by rw [Vik.not_val]; have := cast_inj e3; omega
            rw [hKx] at hK
            have hb := (decomp_sound hwP htP hG hML hrng hd hK).2 i hi
            rw [bit_getLsbD, BitVec.getLsbD_not] at hb
            simp only [hi, decide_true, Bool.true_and] at hb
            rw [bitAt_map _ _ (by omega), refVal_neg]
            have e : bitAt rs i = rs[i] := by simp [bitAt, show i < rs.length by omega]
            rw [← e]; exact hb
          · cases h
        · cases h


include hwP hG in
/-- `masked`: the bitwise operation with a mask of a run of ones. -/
theorem maskForm_sound {op : BvBin} {t w : Nat} {f E : Lia.Form × Int} {c : Int} {x y : BitVec w}
    (h : tr.maskForm SP P op t f c w = some E) (hop : op = .and ∨ op = .or ∨ op = .xor)
    (ht : ρ t = .num ((Vik.val x : Int) : R)) (hf : evf ρ f = ((Vik.val x : Int) : R)) (hyc : Vik.val y = c) :
    evf ρ E = ((Vik.val (op.apply x y) : Int) : R) := by
  unfold Trace.maskForm at h
  split at h
  · cases h
  · rename_i k hk
    have hkw : k ≤ w := by have := List.mem_range.mp (List.mem_of_find?_eq_some hk); omega
    have hpred := List.find?_some hk
    simp only [Bool.or_eq_true, beq_iff_eq] at hpred
    simp only at h
    obtain ⟨lo, hlo, rfl⟩ := Option.map_eq_some_iff.mp h
    have hlow : evf ρ lo = ((Vik.val x % 2 ^ k : Int) : R) := by
      split at hlo
      · rename_i hkw'
        subst hkw'; cases hlo; rw [hf, Int.emod_eq_of_lt (Vik.val_nonneg x) (Vik.val_lt x)]
      · split at hlo
        · rename_i hk0
          subst hk0; cases hlo; rw [evf_const]; simp
        · obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hlo
          have er := sym_val (Ms := Ms) hwP hG (symNode_sym hr).2
          simp only [Rule.ival, ht, intOf_num] at er
          exact evf_sym1 ρ er
    have hhigh : evf ρ (f.1 ++ Lia.neg lo.1, f.2 - lo.2) = ((Vik.val x - Vik.val x % 2 ^ k : Int) : R) := by
      rw [evf_sub, hf, hlow, Ring.intCast_sub]
    by_cases hm : c = 2 ^ k - 1
    · have hy := ofNat_low hkw (hyc.trans hm)
      have ml := masked_low x hkw
      simp only at ml
      obtain ⟨ea, eo, ex⟩ := ml
      subst hy
      simp only [hm, beq_self_eq_true, if_true]
      rcases hop with rfl | rfl | rfl <;> simp only [BvBin.apply, BvBin.width]
      · rw [ea, hlow]
      all_goals
        first
        | rw [eo]
        | rw [ex]
        unfold evf at hf hlow ⊢
        simp only [eval_append, Lia.eval_neg, Ring.intCast_add, Ring.intCast_sub] at hf hlow ⊢
        grind
    · have hm2 : c = 2 ^ w - 2 ^ k := hpred.resolve_left hm
      have hy := ofNat_high hkw (hyc.trans hm2)
      have ml := masked_high x hkw
      simp only at ml
      obtain ⟨ea, eo, ex⟩ := ml
      subst hy
      have hne : (c == 2 ^ k - 1) = false := by simpa using hm
      simp only [hne, Bool.false_eq_true, if_false]
      rcases hop with rfl | rfl | rfl <;> simp only [BvBin.apply, BvBin.width]
      · rw [ea, hhigh]
      all_goals
        first
        | rw [eo]
        | rw [ex]
        subst hm2
        unfold evf at hf hlow ⊢
        simp only [eval_append, Lia.eval_neg, Ring.intCast_add, Ring.intCast_sub] at hf hlow ⊢
        grind

include hwP htP hG hML hrng in
theorem maskedOf_sound {op : BvBin} {w ta tb : Nat} {E : Lia.Form × Int} {x y : BitVec w}
    (h : tr.maskedOf SP P op w ta tb = some E) (hop : op = .and ∨ op = .or ∨ op = .xor)
    (ea : ρ ta = .num ((Vik.val x : Int) : R)) (eb : ρ tb = .num ((Vik.val y : Int) : R)) :
    evf ρ E = ((Vik.val (op.apply x y) : Int) : R) := by
  have la : evf ρ (lin P.nodes ta) = ((Vik.val x : Int) : R) := by
    have := lin_val hwP (tr := tr) (Ms := Ms) (SP := SP) ta; rw [ea, toR_num] at this; exact this.symm
  have lb : evf ρ (lin P.nodes tb) = ((Vik.val y : Int) : R) := by
    have := lin_val hwP (tr := tr) (Ms := Ms) (SP := SP) tb; rw [eb, toR_num] at this; exact this.symm
  unfold Trace.maskedOf at h
  split at h
  · rename_i c hc
    have e := constOf_eval hc (fun u => (ρ u).toR)
    change evf ρ (lin P.nodes tb) = _ at e
    rw [lb] at e
    exact maskForm_sound hwP hG h hop ea la (cast_inj e)
  · split at h
    · rename_i _ c hc
      have e := constOf_eval hc (fun u => (ρ u).toR)
      change evf ρ (lin P.nodes ta) = _ at e
      rw [la] at e
      rw [maskForm_sound hwP hG h hop eb lb (cast_inj e)]
      rcases hop with rfl | rfl | rfl <;> simp only [BvBin.apply, BvBin.width]
      · rw [BitVec.and_comm]
      · rw [BitVec.or_comm]
      · rw [BitVec.xor_comm]
    · cases h

theorem bitwiseOf_op {op op' : BvBin} {neg : Bool} (h : bitwiseOf op = some (op', neg)) :
    op' = .and ∨ op' = .or ∨ op' = .xor := by
  cases op <;> simp only [bitwiseOf, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
    obtain ⟨rfl, rfl⟩ := h <;> simp

include hwP htP hG hML hrng in
/-- The bitwise operations take their values. -/
theorem bitwiseOk_sound {op : BvBin} {w l ta tb : Nat} {x y : BitVec w}
    (hb : tr.bitwiseOk SP P op w l ta tb = true) (hl : l < P.nodes.length) (hta : ta < P.nodes.length)
    (htb : tb < P.nodes.length) (ea : ρ ta = .num ((Vik.val x : Int) : R))
    (eb : ρ tb = .num ((Vik.val y : Int) : R)) : ρ l = .num ((Vik.val (op.apply x y) : Int) : R) := by
  unfold Trace.bitwiseOk at hb
  split at hb
  · cases hb
  · rename_i op' neg hop
    have hop' := bitwiseOf_op hop
    simp only [Bool.or_eq_true] at hb
    rcases hb with hm | hg
    · split at hm
      · rename_i E hE
        have eE := maskedOf_sound hwP htP hG hML hrng hE hop' ea eb
        rw [bitwise_not hop]
        cases neg
        · simp only [Bool.false_eq_true, if_false] at hm ⊢
          exact fits_num hwP htP hML hrng hm hl eE
        · simp only [if_true] at hm ⊢
          refine fits_num hwP htP hML hrng (f := (Lia.neg E.1, 2 ^ w - 1 - E.2)) hm hl ?_
          have : evf ρ (Lia.neg E.1, 2 ^ w - 1 - E.2) = evf ρ ([], 2 ^ w - 1) - evf ρ E := by
            have := evf_sub ρ ([], 2 ^ w - 1) E
            simpa using this
          rw [this, eE, evf_const, Ring.intCast_sub (2 ^ w - 1), Ring.intCast_sub]
      · cases hm
    · split at hg
      · rename_i A B hA hB
        simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hg
        obtain ⟨⟨⟨_, _⟩, hs⟩, hall⟩ := hg
        obtain ⟨_, rA⟩ := tbits_sound hwP htP hG hML hrng hA hta ea
        obtain ⟨_, rB⟩ := tbits_sound hwP htP hG hML hrng hB htb eb
        obtain ⟨bs, hbs, hv⟩ := sumOk_sound hwP htP hG hML hrng hs hl
        have hlen : (decodeBits (lin P.nodes l) w).length = w := by simp [decodeBits]
        rw [hlen] at hbs hv
        rw [hv, bitwise_val hop]
        congr 2
        refine bitSum_congr fun i hi => ?_
        have hg := hall i hi
        have hd := hbs i hi
        congr 1
        cases neg
        · simp only [Bool.false_eq_true, if_false] at hg
          rw [gateOk_sound hwP htP hG hML hrng hg (rA i hi) (rB i hi) hd]; simp
        · simp only [if_true] at hg
          have hd' : RefVal ρ (bitAt (decodeBits (lin P.nodes l) w) i).flip (!bs i) := by
            rw [refVal_flip, Bool.not_not]; exact hd
          have := gateOk_sound hwP htP hG hML hrng hg (rA i hi) (rB i hi) hd'
          rw [← this]; simp
      · cases hg


include hwP htP hG hML hrng in
theorem sameOk_sound {x : Nat} {r s : BitRef} {br bs : Bool} (h : tr.sameOk SP P x r s = true)
    (hr : RefVal ρ r br) (hs : RefVal ρ s bs) : (ρ x).truth = (br == bs) := by
  have L : ∀ {c b : Bool}, RefVal ρ (.lit c) b → b = c := fun h => (refVal_lit ρ).mp h
  unfold Trace.sameOk at h
  split at h
  · rename_i e; subst e; rw [L hr, refFits_sound hwP htP hG hML hrng h hs]; cases bs <;> rfl
  split at h
  · rename_i e; subst e; rw [L hs, refFits_sound hwP htP hG hML hrng h hr]; cases br <;> rfl
  split at h
  · rename_i e; subst e
    rw [L hr, refFits_sound hwP htP hG hML hrng h ((refVal_neg ρ (b := !bs)).mpr (by simpa using hs))]; cases bs <;> rfl
  split at h
  · rename_i e; subst e
    rw [L hs, refFits_sound hwP htP hG hML hrng h ((refVal_neg ρ (b := !br)).mpr (by simpa using hr))]; cases br <;> rfl
  split at h
  · rename_i e; subst e
    rw [refVal_unique ρ hr hs]
    simp only [Tab.at_eq, beq_iff_eq] at h
    rw [Low.val_node hwP h]; simp [Low.evalNode, truth_bool]
  split at h
  · rename_i p q hpq
    simp only [Bool.and_eq_true] at h
    rw [Low.val_node hwP ((Tab.at_eq _ _).symm.trans hpq)]
    simp only [Low.evalNode, truth_bool]
    change ((ρ p).truth == (ρ q).truth) = _
    rw [refFits_sound hwP htP hG hML hrng h.1 hr, refFits_sound hwP htP hG hML hrng h.2 hs]
  · cases h

include hwP htP hG hML hrng in
/-- `equal` bit by bit is the equality of the values. -/
theorem bitEqOk_sound {x ta tb w : Nat} {X Y : BitVec w} (h : tr.bitEqOk SP P x ta tb w = true)
    (hta : ta < P.nodes.length) (htb : tb < P.nodes.length)
    (ea : ρ ta = .num ((Vik.val X : Int) : R)) (eb : ρ tb = .num ((Vik.val Y : Int) : R)) :
    ρ x = .bool (decide (X = Y)) := by
  unfold Trace.bitEqOk at h
  split at h
  · rename_i A B xs hA hB hx
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
    obtain ⟨⟨⟨_, _⟩, hxl⟩, hall⟩ := h
    obtain ⟨_, rA⟩ := tbits_sound hwP htP hG hML hrng hA hta ea
    obtain ⟨_, rB⟩ := tbits_sound hwP htP hG hML hrng hB htb eb
    rw [Low.val_node hwP ((Tab.at_eq _ _).symm.trans hx)]
    simp only [Low.evalNode, Val.bool.injEq]
    apply bool_eq_decide
    rw [Vik.eq_iff_bits, List.all_eq_true]
    constructor
    · intro hh i hi
      have e := sameOk_sound hwP htP hG hML hrng (hall i hi) (rA i hi) (rB i hi)
      have hm : xs.getD i 0 ∈ xs := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
      have := hh _ hm
      change (ρ (xs.getD i 0)).truth = true at this
      rw [e] at this
      simpa using this
    · intro hh a ha
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
      have e := sameOk_sound hwP htP hG hML hrng (hall i (by omega)) (rA i (by omega)) (rB i (by omega))
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at e
      change (ρ xs[i]).truth = true
      rw [e]; simpa using hh i (by omega)
  · cases h


include hG in
theorem findSym_sym {pred : Rule → Bool} {x : Nat} (h : tr.findSym SP P pred = some x) :
    x < P.nodes.length ∧ ∃ r, tr.symAt SP P x = some (r, 0) ∧ pred r = true := by
  unfold Trace.findSym at h
  split at h
  · rename_i m hm
    simp only at h
    split at h
    · rename_i hx
      simp only [Option.some.injEq] at h; subst h
      refine ⟨hx, ?_⟩
      obtain ⟨hlt, hp, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hm
      have e1 := getElem?_idxOf P.nodes _ hx
      have hmi : tr.mints[m]? = some tr.mints[m] := List.getElem?_eq_getElem hlt
      revert hp hmi
      generalize tr.mints[m] = mt
      intro hp hmi
      cases mt with
      | rule r j =>
        cases j with
        | zero =>
          refine ⟨r, ?_, by simpa using hp⟩
          unfold Trace.symAt
          rw [Tab.at_eq, e1]
          simp only [Tab.at_eq, Nat.le_add_right, if_true, Nat.add_sub_cancel_left, hmi]
        | succ j => simp at hp
      | _ => simp at hp
    · cases h
  · cases h

include hwP htP hG hML hrng in
theorem partialOf_sound {kept i : Nat} {r : BitRef} {b : Bool} {K : Int} {f : Lia.Form × Int}
    (h : tr.partialOf SP P kept r i = some f) (hr : RefVal ρ r b) (hk : evf ρ (lin P.nodes kept) = (K : R)) :
    evf ρ f = ((if b then 2 ^ i * K else 0 : Int) : R) := by
  have hsh : evf ρ (Lia.scale ((2 ^ i : Int) : Rat) (lin P.nodes kept).1, 2 ^ i * (lin P.nodes kept).2) =
      ((2 ^ i * K : Int) : R) := by
    rw [evf_scale, hk, Ring.intCast_mul]
  unfold Trace.partialOf at h
  simp only at h
  split at h
  · cases h; rw [(refVal_lit ρ).mp hr]; simpa using hsh
  · cases h; rw [(refVal_lit ρ).mp hr]; simp [evf_const]
  · obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨hxl, rl, hs, hp⟩ := findSym_sym hG hx
    cases rl with
    | cases c t e lo hi =>
      simp only [Bool.and_eq_true] at hp
      obtain ⟨⟨hc, ht'⟩, he⟩ := hp
      have args := (symAt_args hG hs).2
      have ex := sym_val (Ms := Ms) hwP hG hs
      simp only [Rule.ival] at ex
      rw [fits_num hwP htP hML hrng ht' (args t (by simp [Rule.args])) hsh,
        fits_num hwP htP hML hrng (f := ([], 0)) he (args e (by simp [Rule.args])) (evf_const ρ 0),
        refFits_sound hwP htP hG hML hrng hc hr, intOf_num, intOf_num] at ex
      exact evf_sym1 ρ ex
    | _ => simp at hp

include hwP htP hG hML hrng in
theorem partialForms_sound {kept : Nat} {B : List BitRef} {K Y : Int} (hk : evf ρ (lin P.nodes kept) = (K : R))
    (hB : ∀ i < B.length, RefVal ρ (bitAt B i) (bit Y i == 1)) :
    ∀ n, n ≤ B.length → ∀ {F}, tr.partialForms SP P kept B n = some F → evf ρ F = ((partials K Y n : Int) : R)
  | 0, _, F, h => by simp only [Trace.partialForms, Option.some.injEq] at h; subst h; simp [partials, evf_const]
  | n + 1, hn, F, h => by
    simp only [Trace.partialForms] at h
    obtain ⟨g, hg, hF⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨f, hf, rfl⟩ := Option.map_eq_some_iff.mp hF
    rw [evf_add, partialForms_sound hk hB n (by omega) hg,
      partialOf_sound hwP htP hG hML hrng hf (hB n (by omega)) hk]
    simp only [partials, Ring.intCast_add]
    congr 2
    by_cases h1 : bit Y n = 1
    · simp [h1, Int.mul_comm]
    · simp [h1]

include hwP htP hG hML hrng in
/-- An exact product: the product of the values of its factors. -/
theorem exactOk_sound {v kept blasted w : Nat} {K Q : Int} (h : tr.exactOk SP P v kept blasted w = true)
    (hv : v < P.nodes.length) (hbl : blasted < P.nodes.length) (q0 : 0 ≤ Q) (q1 : Q < 2 ^ w)
    (hk : ρ kept = .num (K : R)) (hb : ρ blasted = .num (Q : R)) : ρ v = .num ((K * Q : Int) : R) := by
  have lk : evf ρ (lin P.nodes kept) = (K : R) := by
    have := lin_val hwP (tr := tr) (Ms := Ms) (SP := SP) kept; rw [hk, toR_num] at this; exact this.symm
  have hY : Vik.val (BitVec.ofNat w Q.toNat) = Q := by
    have : Q.toNat < 2 ^ w := by
      have : ((2 ^ w : Nat) : Int) = 2 ^ w := by simp
      omega
    simp only [Vik.val, BitVec.toNat_ofNat, Nat.mod_eq_of_lt this]; omega
  rw [← hY] at hb ⊢
  unfold Trace.exactOk at h
  split at h
  · rename_i B hB
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hlen, h⟩ := h
    obtain ⟨_, rB⟩ := tbits_sound hwP htP hG hML hrng hB hbl hb
    split at h
    · rename_i F hF
      have hB' : ∀ i < B.length, RefVal ρ (bitAt B i) (bit (Vik.val (BitVec.ofNat w Q.toNat)) i == 1) := by
        intro i hi; rw [bit_getLsbD]; exact rB i (by omega)
      have e := partialForms_sound hwP htP hG hML hrng lk hB' w (by omega) hF
      rw [exactProduct_eq _ (Vik.val_range _)] at e
      exact fits_num hwP htP hML hrng h hv e
    · cases h
  · cases h

/-- The exact products of a trace (for `ruleFacts_hold`). -/
theorem exactOk_spec (hwP : Low.wellFormed P.nodes = true) (htP : Low.typed P.sig P.nodes P.sortOf = true)
    (hG : SigSpec SP P tr) (hML : (lowModel SP P tr Ms).Sound P.sig P.bvIndex)
    (hrng : ∀ j < P.nodes.length,
      inRange P.bvIndex (P.sortOf[j]?.getD 0) (Low.val (lowModel SP P tr Ms).toInterp P.nodes j)) :
    ExactSpec SP P tr Ms :=
  fun h hv hbl q0 q1 hk hb => exactOk_sound hwP htP hG hML hrng h hv hbl q0 q1 hk hb

include hwP htP hG hML hrng in
/-- `bvmul` of two unknowns. -/
theorem productOk_sound {w l ta tb : Nat} {x y : BitVec w} (h : tr.productOk SP P w l ta tb = true)
    (hta : ta < P.nodes.length) (htb : tb < P.nodes.length)
    (ea : ρ ta = .num ((Vik.val x : Int) : R)) (eb : ρ tb = .num ((Vik.val y : Int) : R)) :
    ρ l = .num ((Vik.val (x * y) : Int) : R) := by
  unfold Trace.productOk at h
  split at h
  · rename_i v w' lo hi hsl
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at h
    obtain ⟨rfl, h⟩ := h
    have hv := (symAt_args hG hsl).2 v (by simp [Rule.args])
    rw [sym_val hwP hG hsl]
    simp only [Rule.ival]
    have ev : ρ v = .num ((Vik.val x * Vik.val y : Int) : R) := by
      rcases h with h | h
      · exact exactOk_sound hwP htP hG hML hrng h hv htb (Vik.val_nonneg y) (Vik.val_lt y) ea eb
      · rw [Int.mul_comm]; exact exactOk_sound hwP htP hG hML hrng h hv hta (Vik.val_nonneg x) (Vik.val_lt x) eb ea
    rw [ev, intOf_num]
    simp only [Vik.val, BitVec.toNat_mul, Int.natCast_emod, Int.natCast_mul, Int.natCast_pow, Int.cast_ofNat_Int]
  · cases h


include hwP htP hG hML hrng in
/-- A stage of a barrel shifter. -/
theorem stepNode_sound {op : BvBin} {w t j s : Nat} {X : BitVec w} (hw0 : 0 < w)
    (hop : op = .shl ∨ op = .lshr ∨ op = .ashr) (h : tr.stepNode SP P op w t j = some s)
    (ht : ρ t = .num ((Vik.val X : Int) : R)) : ρ s = .num ((Vik.val (stepBv op X (2 ^ j)) : Int) : R) := by
  have lt : evf ρ (lin P.nodes t) = ((Vik.val X : Int) : R) := by
    have := lin_val hwP (tr := tr) (Ms := Ms) (SP := SP) t; rw [ht, toR_num] at this; exact this.symm
  have hx0 := Vik.val_nonneg X
  have hx1 := Vik.val_lt X
  rcases hop with rfl | rfl | rfl
  · simp only [Trace.stepNode] at h
    split at h
    rotate_left
    · -- a constant, folded
      split at h
      · rename_i c hc
        split at h
        · rename_i hcond
          simp only [Option.some.injEq] at h; subst h
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
          obtain ⟨⟨h0, h1⟩, hx⟩ := hcond
          rw [Low.val_num hwP (getElem?_idxOf _ _ hx)]
          have hX : (Vik.val X : Int) = c := by
            have e := constOf_eval hc (fun u => (ρ u).toR)
            unfold evf at lt
            rw [lt] at e
            have := (IsCharP.intCast_eq_zero_iff (α := R) 0 (Vik.val X - c)).mp
              (by rw [Ring.intCast_sub, e]; grind)
            simp at this; omega
          simp only [stepBv]
          rw [Vik.shl_const_val]
          congr 2
          rw [hX]
          split
          · rename_i hle
            have hD : (2 : Int) ^ w ≤ 2 ^ (2 ^ j) := by
              have := Nat.pow_le_pow_right (n := 2) (by decide) hle; exact_mod_cast this
            have hDp : (0 : Int) < 2 ^ (2 ^ j) := Int.pow_pos (by decide)
            have hc0 : c = 0 := by
              rcases Int.lt_or_le c 1 with h' | h'
              · have : 0 ≤ c := by
                  apply Classical.byContradiction; intro hn
                  have : c * 2 ^ (2 ^ j) < 0 := Int.mul_neg_of_neg_of_pos (by omega) hDp
                  omega
                omega
              · have := Int.mul_le_mul_of_nonneg_right h' (Int.le_of_lt hDp)
                rw [Int.one_mul] at this
                omega
            subst hc0; simp
          · have : ((2 ^ (2 ^ j) : Nat) : Int) = 2 ^ (2 ^ j) := by simp
            rw [this, Int.emod_eq_of_lt h0 h1]
        · cases h
      · cases h
    rename_i s' h'
    simp only [Option.some.injEq] at h; subst h
    obtain ⟨_, rl, hs, hp⟩ := findSym_sym hG h'
    cases rl with
    | modulo v w' lo hi =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hp
      obtain ⟨⟨⟨hw', _⟩, _⟩, hv⟩ := hp
      subst w'
      have ev := fits_num hwP htP hML hrng
        (f := (Lia.scale (((2 ^ (2 ^ j) : Int) : Int) : Rat) (lin P.nodes t).1, 2 ^ (2 ^ j) * (lin P.nodes t).2))
        hv ((symAt_args hG hs).2 v (by simp [Rule.args]))
        (V := 2 ^ (2 ^ j) * Vik.val X) (by rw [evf_scale, lt, Ring.intCast_mul])
      rw [sym_val hwP hG hs]
      simp only [Rule.ival, ev, intOf_num, stepBv]
      rw [Vik.shl_const_val]
      congr 2
      split
      · rename_i hle
        have : (2 : Int) ^ (2 ^ j) = 2 ^ w * 2 ^ (2 ^ j - w) := by rw [← Int.pow_add]; congr 1; omega
        rw [this, Int.mul_assoc, Int.mul_emod_right]
      · rw [Int.mul_comm]; simp
    | _ => simp at hp
  · simp only [Trace.stepNode] at h
    have es := sym_val (Ms := Ms) hwP hG (symNode_sym h).2
    simp only [Rule.ival, ht, intOf_num] at es
    rw [es]
    simp only [stepBv]
    congr 2
    by_cases hj : 2 ^ j < w
    · rw [(Vik.lshr_const_val X _ hj).1]
    · rw [Vik.lshr_const_far X _ (by omega)]
      have : (2 : Int) ^ w ≤ 2 ^ (2 ^ j) := by
        have := Nat.pow_le_pow_right (n := 2) (by decide) (show w ≤ 2 ^ j by omega); exact_mod_cast this
      exact Int.ediv_eq_zero_of_lt hx0 (Int.lt_of_lt_of_le hx1 this)
  · simp only [Trace.stepNode] at h
    obtain ⟨q, hq, hs⟩ := Option.bind_eq_some_iff.mp h
    have eq := sym_val (Ms := Ms) hwP hG (symNode_sym hq).2
    simp only [Rule.ival, ht, intOf_num, if_true] at eq
    have es := sym_val (Ms := Ms) hwP hG (symNode_sym hs).2
    simp only [Rule.ival, eq, intOf_num] at es
    rw [es]
    simp only [stepBv]
    rw [Vik.ashr_const_val, Vik.toInt_eq X hw0]
    rfl

include hwP htP hG hML hrng in
/-- The stages of a barrel shifter. -/
theorem stageNode_sound {op : BvBin} {w ta : Nat} {B : List BitRef} {x y : BitVec w} (hw0 : 0 < w)
    (hop : op = .shl ∨ op = .lshr ∨ op = .ashr) (hB : ∀ i < w, RefVal ρ (bitAt B i) (y.getLsbD i))
    (hta : ρ ta = .num ((Vik.val x : Int) : R)) :
    ∀ j, j ≤ w → ∀ {t}, tr.stageNode SP P op w ta B j = some t →
      ρ t = .num ((Vik.val (Vik.stages (fun j t => stepBv op t (2 ^ j)) y.toNat j x) : Int) : R)
  | 0, _, t, h => by
    simp only [Trace.stageNode, Option.some.injEq] at h; subst h; simpa [Vik.stages] using hta
  | j + 1, hj, t, h => by
    simp only [Trace.stageNode] at h
    obtain ⟨t0, h0, h⟩ := Option.bind_eq_some_iff.mp h
    have e0 := stageNode_sound hw0 hop hB hta j (by omega) h0
    have hb := hB j (by omega)
    simp only [Vik.stages, BitVec.testBit_toNat]
    split at h
    · rename_i hf
      cases h
      rw [hf, refVal_lit] at hb
      rw [hb]; simpa using e0
    · obtain ⟨s, hs, h⟩ := Option.bind_eq_some_iff.mp h
      have es := stepNode_sound hwP htP hG hML hrng hw0 hop hs e0
      split at h
      · rename_i htrue
        cases h
        rw [htrue, refVal_lit] at hb
        rw [hb]; simpa using es
      · obtain ⟨_, rl, hsy, hp⟩ := findSym_sym hG h
        cases rl with
        | cases c th el lo hi =>
          simp only [Bool.and_eq_true, beq_iff_eq] at hp
          obtain ⟨⟨hc, rfl⟩, rfl⟩ := hp
          rw [sym_val hwP hG hsy]
          simp only [Rule.ival]
          rw [refFits_sound hwP htP hG hML hrng hc hb]
          split <;> simp [es, e0, intOf_num]
        | _ => simp at hp

theorem fits_le_lt {x : Nat} {a b : Shape} (h : fits P.sig P.nodes P.sortOf x (.le a b) = true) :
    x < P.nodes.length := by
  unfold fits at h
  rw [Tab.at_eq] at h
  split at h
  · rename_i n hn; exact lt_of_get' hn
  · cases h

include hwP htP hG hML hrng in
/-- The `far` condition: the amount reaches the width. -/
theorem farOk_sound {w n tam c : Nat} {B : List BitRef} {y : BitVec w} (h : tr.farOk SP P w n tam B c = true)
    (hn : w ≤ 2 ^ n) (hB : ∀ i < w, RefVal ρ (bitAt B i) (y.getLsbD i))
    (htam : ρ tam = .num ((Vik.val y : Int) : R)) : (ρ c).truth = decide (w ≤ y.toNat) := by
  have hge : ∀ {x}, fits P.sig P.nodes P.sortOf x (.le (.num [] w) (.same tam)) = true →
      (ρ x).truth = decide (w ≤ y.toNat) := by
    intro x hx
    rw [fits_sound hML hwP htP hrng x (fits_le_lt hx) _ hx]
    simp only [Shape.ev, Lia.eval, htam, toR_num, truth_bool]
    have e : (0 : R) + (((w : Nat) : Int) : R) = (((w : Nat) : Int) : R) := by grind
    rw [e]
    rw [htam, toR_num]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    rw [cast_le_iff]
    simp only [Vik.val]
    omega
  unfold Trace.farOk at h
  split at h
  · rename_i xs hxs
    simp only [Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true, List.any_eq_true, List.mem_range,
      beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    rw [Low.val_node hwP ((Tab.at_eq _ _).symm.trans hxs)]
    simp only [Low.evalNode, truth_bool]
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨x, hx, hxt⟩
      change (ρ x).truth = true at hxt
      rcases h1 x hx with ⟨j, hj, hnj, hf⟩ | hf
      · rw [refFits_sound hwP htP hG hML hrng hf (hB j hj)] at hxt
        have := Nat.ge_two_pow_of_testBit (by rw [BitVec.testBit_toNat]; exact hxt)
        have : 2 ^ n ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) hnj
        omega
      · rw [hge hf] at hxt; simpa using hxt
    · intro hle
      rcases (Vik.far_iff w n y.toNat hn y.isLt).mpr hle with ⟨j, hnj, hjw, hbit⟩ | ⟨hne, -⟩
      · rw [BitVec.testBit_toNat] at hbit
        rcases h2 j hjw with (hjn | hlf) | ⟨x, hx, hf⟩
        · omega
        · have := hB j hjw; rw [hlf, refVal_lit, hbit] at this; cases this
        · exact ⟨x, hx, by change (ρ x).truth = true; rw [refFits_sound hwP htP hG hML hrng hf (hB j hjw), hbit]⟩
      · rcases h3 with h3 | ⟨x, hx, hf⟩
        · exact absurd h3 hne
        · exact ⟨x, hx, by change (ρ x).truth = true; rw [hge hf]; simpa using hle⟩
  · cases h

end

end Vik.Lower
