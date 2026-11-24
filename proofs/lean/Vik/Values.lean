import Vik.Rules

/-!
# Values of bit-vectors

A bit-vector `x : BitVec w` lowers to `val x`, its unsigned value. The lowering
decides the sign of a value `t` by `t ≥ 2^(w-1)`, and computes the signed value
with the `cases` rule tagged `signed`.
-/

namespace Vik

/-- The unsigned value of a bit-vector, as the lowering represents it. -/
def val {w : Nat} (x : BitVec w) : Int := x.toNat

theorem val_range {w : Nat} (x : BitVec w) : Range w (val x) := range_toNat x

theorem val_lt {w : Nat} (x : BitVec w) : val x < 2 ^ w := by
  have := (val_range x).2; omega

theorem val_nonneg {w : Nat} (x : BitVec w) : 0 ≤ val x := (val_range x).1

theorem val_inj {w : Nat} {x y : BitVec w} : val x = val y ↔ x = y := by
  simp [val, BitVec.toNat_eq, Int.ofNat_inj]

/-- The unsigned value is the signed one modulo `2^w`. -/
theorem val_eq_toInt_emod {w : Nat} (x : BitVec w) : val x = x.toInt % 2 ^ w := by
  have h := BitVec.toNat_ofInt (n := w) x.toInt
  rw [BitVec.ofInt_toInt] at h
  have hp := pow_pos' w
  have := Int.emod_nonneg x.toInt (Int.ne_of_gt hp)
  simp only [val, h, Int.natCast_pow, Int.cast_ofNat_Int]
  exact Int.toNat_of_nonneg this

/-- A value modulo `2^w` is the value of the bit-vector it denotes. -/
theorem val_ofInt (w : Nat) (i : Int) : val (BitVec.ofInt w i) = i % 2 ^ w := by
  have hp := pow_pos' w
  have := Int.emod_nonneg i (Int.ne_of_gt hp)
  simp only [val, BitVec.toNat_ofInt, Int.natCast_pow, Int.cast_ofNat_Int]
  exact Int.toNat_of_nonneg this

/-- `negative(t, w)`: the sign bit. -/
theorem msb_iff {w : Nat} (x : BitVec w) : x.msb = true ↔ 2 ^ (w - 1) ≤ val x := by
  rw [BitVec.msb_eq_decide]
  simp only [decide_eq_true_eq, val]
  constructor
  · intro h; exact_mod_cast h
  · intro h; exact_mod_cast h

theorem two_pow_pred {w : Nat} (hw : 0 < w) : (2 : Int) ^ w = 2 * 2 ^ (w - 1) := by
  obtain ⟨v, rfl⟩ : ∃ v, w = v + 1 := ⟨w - 1, by omega⟩
  simp [Int.pow_succ, Int.mul_comm]

/-- `signed(t, w)`, the `cases` tagged `signed`: the signed value. -/
theorem toInt_eq {w : Nat} (x : BitVec w) (hw : 0 < w) :
    x.toInt = if 2 ^ (w - 1) ≤ val x then val x - 2 ^ w else val x := by
  rw [BitVec.toInt_eq_toNat_cond]
  have hp := two_pow_pred hw
  have h2 : ((2 ^ w : Nat) : Int) = 2 ^ w := by simp
  by_cases h : 2 ^ (w - 1) ≤ val x
  · have : ¬ 2 * x.toNat < 2 ^ w := by
      intro h'; have : (2 * x.toNat : Int) < (2 ^ w : Nat) := by exact_mod_cast h'
      simp only [val] at h; rw [h2] at this; omega
    rw [if_neg this, if_pos h, h2]; rfl
  · have : 2 * x.toNat < 2 ^ w := by
      have : (2 * x.toNat : Int) < (2 ^ w : Nat) := by simp only [val] at h; rw [h2]; omega
      exact_mod_cast this
    rw [if_pos this, if_neg h]; rfl

/-- The bounds of the `signed` cases rule. -/
theorem toInt_range {w : Nat} (x : BitVec w) (hw : 0 < w) :
    -2 ^ (w - 1) ≤ x.toInt ∧ x.toInt ≤ 2 ^ (w - 1) - 1 := by
  rw [toInt_eq x hw]
  have := val_range x; have := two_pow_pred hw; unfold Range at *
  split <;> omega

theorem toInt_neg_iff {w : Nat} (x : BitVec w) (hw : 0 < w) : x.toInt < 0 ↔ 2 ^ (w - 1) ≤ val x := by
  rw [toInt_eq x hw]
  have := val_range x; have := two_pow_pred hw; unfold Range at *
  split <;> omega

end Vik
