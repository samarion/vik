import Vik.Arith

/-!
# Shifts

A shift by a constant is a product, a division, or a floor division of the
signed value. A shift by an unknown amount is a barrel shifter: stage `j`
shifts by `2^j` when bit `j` of the amount is set (the `cases` tagged with the
operation's name), and an amount of at least the width gives the value past the
width (the `cases` tagged `…!far`).
-/

namespace Vik

/-! ## `bvashr` by a constant -/

private theorem ipow_le {a b : Nat} (h : a ≤ b) : (2 : Int) ^ a ≤ 2 ^ b := by
  have := Nat.pow_le_pow_right (n := 2) (by decide) h; exact_mod_cast this

private theorem ipow_lt {a b : Nat} (h : a < b) : (2 : Int) ^ a < 2 ^ b := by
  have := Nat.pow_lt_pow_right (a := 2) (by decide) h; exact_mod_cast this

/-- `bvashr` by `c < w`: `modulo(q, w, -1, 0)` for the floor quotient `q` of
    `sdivide(t, w, 2^c, floor = true)`. -/
theorem ashr_const_val {w : Nat} (x : BitVec w) (c : Nat) :
    val (x.sshiftRight c) = (x.toInt / 2 ^ c) % 2 ^ w := by
  rw [val_eq_toInt_emod, BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]; simp

theorem ashr_const_bounds {w : Nat} (x : BitVec w) (c : Nat) (hw : 0 < w) :
    -1 * 2 ^ w ≤ x.toInt / 2 ^ c ∧ x.toInt / 2 ^ c < (0 + 1) * 2 ^ w := by
  have h2 := two_pow_pred hw
  have hp := pow_pos' c
  have hh := pow_pos' (w - 1)
  have ⟨⟨q0, q1⟩, _, _⟩ := sdivide_floor_facts (s := x.toInt) (half := 2 ^ (w - 1)) hp (toInt_range x hw)
  have a1 : (2 : Int) ^ (w - 1) / 2 ^ c ≤ 2 ^ (w - 1) := Int.ediv_le_self _ (Int.le_of_lt hh)
  have a2 : ((2 : Int) ^ (w - 1) - 1) / 2 ^ c ≤ 2 ^ (w - 1) - 1 := Int.ediv_le_self _ (by omega)
  omega

/-- `bvashr` by `c ≥ w`: the `cases` tagged `sign`, then `modulo(-1 or 0, w, -1, 0)`:
    all ones for a negative value, zero otherwise. -/
theorem ashr_far_val {w : Nat} (x : BitVec w) (c : Nat) (hc : w ≤ c) (hw : 0 < w) :
    val (x.sshiftRight c) = (if 2 ^ (w - 1) ≤ val x then -1 else 0) % 2 ^ w := by
  rw [ashr_const_val]
  have ⟨h0, h1⟩ := toInt_range x hw
  have hp : (2 : Int) ^ (w - 1) < 2 ^ c := ipow_lt (by omega)
  have hc' := pow_pos' c
  by_cases hn : 2 ^ (w - 1) ≤ val x
  · have := (toInt_neg_iff x hw).mpr hn
    have q0 : -1 ≤ x.toInt / 2 ^ c := (Int.le_ediv_iff_mul_le hc').mpr (by omega)
    have q1 : x.toInt / 2 ^ c < 0 := (Int.ediv_lt_iff_lt_mul hc').mpr (by omega)
    rw [if_pos hn, show x.toInt / 2 ^ c = -1 by omega]
  · have : ¬x.toInt < 0 := fun h => hn ((toInt_neg_iff x hw).mp h)
    have : x.toInt / 2 ^ c = 0 := Int.ediv_eq_zero_of_lt (by omega) (by omega)
    rw [if_neg hn, this]

/-! ## Shifts by an unknown amount -/

/-- The barrel shifter: `n` stages, stage `j` applying `step j` when bit `j` of
    the amount `b` is set. -/
def stages {w : Nat} (step : Nat → BitVec w → BitVec w) (b : Nat) : Nat → BitVec w → BitVec w
  | 0, x => x
  | j + 1, x => if b.testBit j then step j (stages step b j x) else stages step b j x

/-- If each stage shifts by `2^j`, the stages shift by the low `n` bits of the amount. -/
theorem stages_eq {w : Nat} (shift : BitVec w → Nat → BitVec w)
    (h0 : ∀ x, shift x 0 = x) (hadd : ∀ x a c, shift x (a + c) = shift (shift x a) c)
    (b : Nat) (n : Nat) (x : BitVec w) :
    stages (fun j t => shift t (2 ^ j)) b n x = shift x (b % 2 ^ n) := by
  induction n with
  | zero => simp [stages, Nat.mod_one, h0]
  | succ n ih =>
    simp only [stages, ih]
    rw [Nat.mod_pow_succ, hadd, Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (b / 2 ^ n) with e | e
    · simp [e, h0]
    · simp [e]

/-- With `w ≤ 2^n`, the lowering's `far` condition, a bit at `n` or above, or
    an amount of at least `w` when `w` is not `2^n`, is an amount of at least `w`. -/
theorem far_iff (w n b : Nat) (hn : w ≤ 2 ^ n) (hb : b < 2 ^ w) :
    ((∃ j, n ≤ j ∧ j < w ∧ b.testBit j = true) ∨ (2 ^ n ≠ w ∧ w ≤ b)) ↔ w ≤ b := by
  constructor
  · rintro (⟨j, hj, -, hbit⟩ | ⟨-, h⟩)
    · have := Nat.ge_two_pow_of_testBit hbit
      have : 2 ^ n ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) hj
      omega
    · exact h
  · intro h
    by_cases he : 2 ^ n = w
    · left
      apply Classical.byContradiction
      intro hno
      have : b < 2 ^ n := by
        apply Nat.lt_pow_two_of_testBit
        intro i hi
        by_cases hiw : i < w
        · cases e : b.testBit i
          · rfl
          · exact absurd ⟨i, hi, hiw, e⟩ hno
        · exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide) (by omega)))
      omega
    · exact Or.inr ⟨he, h⟩

/-- `bvshl` by an unknown amount. -/
theorem shl_lowering {w n : Nat} (x y : BitVec w) (hn : w ≤ 2 ^ n) :
    x <<< y = if w ≤ y.toNat then 0#w else stages (fun j t => t <<< (2 ^ j)) y.toNat n x := by
  rw [BitVec.shiftLeft_eq', stages_eq (fun t c => t <<< c) BitVec.shiftLeft_zero
    (fun x a c => BitVec.shiftLeft_add x a c)]
  split
  · exact BitVec.shiftLeft_eq_zero (by assumption)
  · rw [Nat.mod_eq_of_lt (by omega)]

private theorem ushiftRight_add' {w : Nat} (x : BitVec w) (a c : Nat) : x >>> (a + c) = x >>> a >>> c := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_add]

/-- `bvlshr` by an unknown amount. -/
theorem lshr_lowering {w n : Nat} (x y : BitVec w) (hn : w ≤ 2 ^ n) :
    x >>> y = if w ≤ y.toNat then 0#w else stages (fun j t => t >>> (2 ^ j)) y.toNat n x := by
  rw [BitVec.ushiftRight_eq', stages_eq (fun t c => t >>> c) BitVec.ushiftRight_zero ushiftRight_add']
  split
  · exact BitVec.ushiftRight_eq_zero (by assumption)
  · rw [Nat.mod_eq_of_lt (by omega)]

/-- `bvashr` by an unknown amount; past the width, the `cases` tagged `sign`. -/
theorem ashr_lowering {w n : Nat} (x y : BitVec w) (hn : w ≤ 2 ^ n) (hw : 0 < w) :
    val (x.sshiftRight' y) =
      if w ≤ y.toNat then (if 2 ^ (w - 1) ≤ val x then 2 ^ w - 1 else 0)
      else val (stages (fun j t => t.sshiftRight (2 ^ j)) y.toNat n x) := by
  rw [BitVec.sshiftRight_eq', stages_eq (fun t c => t.sshiftRight c) (fun _ => BitVec.sshiftRight_zero)
    (fun _ _ _ => BitVec.sshiftRight_add)]
  split
  · rename_i h
    rw [ashr_far_val x _ h hw]
    have := pow_pos' w
    split
    · rw [show (-1 : Int) = (2 ^ w - 1) + (-1) * 2 ^ w by omega, Int.add_mul_emod_self_right,
        Int.emod_eq_of_lt (by omega) (by omega)]
    · rfl
  · rw [Nat.mod_eq_of_lt (by omega)]

end Vik
