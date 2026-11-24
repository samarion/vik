import Vik.Values

/-!
# Bit-vector arithmetic

For each arithmetic operation, the term the lowering builds from the values of
the arguments is the value of the result. Where the term goes through a rule,
the lemma also discharges the bounds that rule's lemma assumes. A rule's symbol
is written as the value its lemma in `Rules` gives it, such as `v % 2^w` for the
remainder of `modulo`.
-/

namespace Vik

open BitVec

local macro "pow_facts" w:term : tactic =>
  `(tactic| (have := pow_pos' $w))

private theorem cast_pow (w : Nat) : ((2 ^ w : Nat) : Int) = 2 ^ w := by simp

/-! ## `bvadd`, `bvsub`, `bvneg`, `bvnot` -/

/-- `bvadd`: `modulo(a + b, w, 0, 1)`. -/
theorem add_val {w : Nat} (x y : BitVec w) :
    val (x + y) = (val x + val y) % 2 ^ w ∧
      0 * 2 ^ w ≤ val x + val y ∧ val x + val y < (1 + 1) * 2 ^ w := by
  have := val_range x; have := val_range y; unfold Range at *
  refine ⟨?_, by omega, by omega⟩
  simp only [val, BitVec.toNat_add, Int.natCast_emod, Int.natCast_add, cast_pow]

/-- `bvsub`: `modulo(a - b, w, -1, 0)`. -/
theorem sub_val {w : Nat} (x y : BitVec w) :
    val (x - y) = (val x - val y) % 2 ^ w ∧
      -1 * 2 ^ w ≤ val x - val y ∧ val x - val y < (0 + 1) * 2 ^ w := by
  have := val_range x; have := val_range y; unfold Range at *
  refine ⟨?_, by omega, by omega⟩
  simp only [val, BitVec.toNat_sub, Int.natCast_emod, cast_pow]
  have : y.toNat ≤ 2 ^ w := Nat.le_of_lt y.isLt
  rw [Int.natCast_add, Int.ofNat_sub this, cast_pow]
  have e : (2 ^ w - (y.toNat : Int) + x.toNat) = (x.toNat - y.toNat) + 1 * 2 ^ w := by omega
  rw [e, Int.add_mul_emod_self_right]

/-- `bvneg`: `modulo(-a, w, -1, 0)`. -/
theorem neg_val {w : Nat} (x : BitVec w) :
    val (-x) = (-val x) % 2 ^ w ∧ -1 * 2 ^ w ≤ -val x ∧ -val x < (0 + 1) * 2 ^ w := by
  have h := sub_val 0#w x
  simp only [BitVec.zero_sub] at h
  simpa [val] using h

/-- `bvnot`: `2^w - 1 - a`. -/
theorem not_val {w : Nat} (x : BitVec w) : val (~~~x) = 2 ^ w - 1 - val x := by
  have := x.isLt
  simp only [val, BitVec.toNat_not]
  have h1 : 1 ≤ 2 ^ w := Nat.one_le_two_pow
  rw [Int.ofNat_sub (by omega), Int.ofNat_sub h1, cast_pow]; rfl

/-! ## Multiplication by a constant, and shifts by a constant -/

/-- `times(t, c, w)` for `0 < c < 2^w`: `modulo(t * c, w, 0, c - 1)`. -/
theorem times_val {w : Nat} (x : BitVec w) (c : Nat) (hc : 0 < c) (hcw : c < 2 ^ w) :
    val (x * BitVec.ofNat w c) = (val x * c) % 2 ^ w ∧
      0 * 2 ^ w ≤ val x * c ∧ val x * c < ((c - 1 : Int) + 1) * 2 ^ w := by
  have := val_range x; unfold Range at *
  refine ⟨?_, by have := Int.mul_nonneg (val_nonneg x) (Int.natCast_nonneg c); omega, ?_⟩
  · simp only [val, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcw, Int.natCast_emod,
      Int.natCast_mul, cast_pow]
  · rw [Int.sub_add_cancel, Int.mul_comm (c : Int)]
    exact Int.mul_lt_mul_of_pos_right (val_lt x) (by omega)

/-- `bvmul` by a constant `c`: `times(t, c mod 2^w, w)`, or `0`. -/
theorem mul_const_val {w : Nat} (x : BitVec w) (c : Nat) :
    val (x * BitVec.ofNat w c) = (val x * (c % 2 ^ w : Nat)) % 2 ^ w := by
  simp only [val, BitVec.toNat_mul, BitVec.toNat_ofNat, Int.natCast_emod, Int.natCast_mul, cast_pow]

/-- `bvshl` by a constant `c`: `0` past the width, `times(t, 2^c, w)` otherwise. -/
theorem shl_const_val {w : Nat} (x : BitVec w) (c : Nat) :
    val (x <<< c) = if w ≤ c then 0 else (val x * (2 ^ c : Nat)) % 2 ^ w := by
  split
  · rename_i h
    simp [val, BitVec.shiftLeft_eq_zero h]
  · simp only [val, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Int.natCast_emod, Int.natCast_mul, cast_pow]

theorem shl_eq_times {w c : Nat} (x : BitVec w) (h : c < w) :
    x <<< c = x * BitVec.ofNat w (2 ^ c) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_mul, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) h)]

/-- `bvlshr` by a constant `c < w`: the quotient of `divide(t, 2^c, 2^w / 2^c - 1)`. -/
theorem lshr_const_val {w : Nat} (x : BitVec w) (c : Nat) (h : c < w) :
    val (x >>> c) = val x / 2 ^ c ∧ 0 ≤ val x ∧ val x ≤ (2 ^ w / 2 ^ c - 1) * 2 ^ c + 2 ^ c - 1 := by
  have hp : (2 : Int) ^ w = 2 ^ (w - c) * 2 ^ c := by
    rw [← Int.pow_add]; congr 1; omega
  have := val_range x; unfold Range at *
  refine ⟨?_, val_nonneg x, ?_⟩
  · simp only [val, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Int.natCast_ediv,
      Int.natCast_pow, Int.cast_ofNat_Int]
  · rw [hp, Int.mul_ediv_cancel _ (Int.ne_of_gt (pow_pos' c)), Int.sub_mul, Int.one_mul]
    omega

theorem lshr_const_far {w : Nat} (x : BitVec w) (c : Nat) (h : w ≤ c) : val (x >>> c) = 0 := by
  simp [val, BitVec.ushiftRight_eq_zero h]

/-! ## Unsigned division -/

/-- `bvudiv`, as SMT-LIB defines it: the quotient, or `2^w - 1` for a zero divisor. -/
theorem udiv_val {w : Nat} (x y : BitVec w) :
    val (x.smtUDiv y) = if val y = 0 then 2 ^ w - 1 else val x / val y := by
  rw [BitVec.smtUDiv_eq]
  by_cases h : y = 0#w
  · have : val y = 0 := by simp [h, val]
    simp only [h, if_true, val, BitVec.toNat_allOnes]
    rw [Int.ofNat_sub Nat.one_le_two_pow, cast_pow]; rfl
  · have : (y.toNat : Int) ≠ 0 := by
      intro h'; apply h; apply BitVec.eq_of_toNat_eq; simp; omega
    simp only [h, if_false, val, BitVec.toNat_udiv, Int.natCast_ediv]
    rw [if_neg this]

/-- `bvurem`: the remainder, or the dividend for a zero divisor. -/
theorem urem_val {w : Nat} (x y : BitVec w) :
    val (x % y) = if val y = 0 then val x else val x % val y := by
  simp only [val, BitVec.toNat_umod, Int.natCast_emod]
  split
  · rename_i h; have : y.toNat = 0 := by omega
    simp [this]
  · rfl

/-- The bounds `divide(t, c, (2^w - 1) / c)` assumes, for a constant divisor `c > 0`. -/
theorem udiv_const_bounds {w : Nat} (x : BitVec w) {c : Int} (hc : 0 < c) :
    0 ≤ val x ∧ val x ≤ ((2 ^ w - 1) / c) * c + c - 1 := by
  have := val_range x; unfold Range at *
  refine ⟨val_nonneg x, ?_⟩
  have := Int.emod_add_mul_ediv (2 ^ w - 1) c
  have := Int.emod_lt_of_pos (2 ^ w - 1) hc
  rw [Int.mul_comm ((2 ^ w - 1) / c)]
  omega

/-! ## Signed values and signed division -/

theorem val_eq_emod_of_toInt {w : Nat} {x : BitVec w} {i : Int} (h : x.toInt = i) : val x = i % 2 ^ w := by
  rw [val_eq_toInt_emod, h]

/-- `bvsrem` (Lean's `srem`): the truncated remainder of the signed values. -/
theorem srem_val {w : Nat} (x y : BitVec w) : val (x.srem y) = (x.toInt.tmod y.toInt) % 2 ^ w :=
  val_eq_emod_of_toInt (BitVec.toInt_srem x y)

/-- `bvsmod` (Lean's `smod`): the floored remainder of the signed values. -/
theorem smod_val {w : Nat} (x y : BitVec w) : val (x.smod y) = (x.toInt.fmod y.toInt) % 2 ^ w :=
  val_eq_emod_of_toInt BitVec.toInt_smod

/-- `bvsdiv` (Lean's `smtSDiv`) by a nonzero divisor: the truncated quotient. -/
theorem sdiv_val {w : Nat} (x y : BitVec w) (hy : y ≠ 0#w) :
    val (x.smtSDiv y) = (x.toInt.tdiv y.toInt) % 2 ^ w := by
  have : x.smtSDiv y = x.sdiv y := by
    have hn : -y ≠ 0#w := by intro h; apply hy; rw [← BitVec.neg_neg (x := y), h]; simp
    rw [BitVec.smtSDiv_eq, BitVec.sdiv_eq]
    cases x.msb <;> cases y.msb <;> simp [BitVec.smtUDiv_eq, hy, hn] <;> rfl
  rw [this, val_eq_toInt_emod, BitVec.toInt_sdiv]
  have := Int.bmod_emod (x := x.toInt.tdiv y.toInt) (m := 2 ^ w)
  simpa using this

/-- `bvsdiv` by zero: `1` for a negative dividend, `2^w - 1` otherwise (the
    `cases` tagged `sdiv0`). -/
theorem sdiv_zero_val {w : Nat} (x : BitVec w) (hw : 0 < w) :
    val (x.smtSDiv 0#w) = if 2 ^ (w - 1) ≤ val x then 1 else 2 ^ w - 1 := by
  have h1 : (2 : Int) ^ w = 2 * 2 ^ (w - 1) := two_pow_pred hw
  have hp := pow_pos' (w - 1)
  rw [BitVec.smtSDiv_eq]
  simp only [BitVec.msb_zero, BitVec.neg_zero, BitVec.smtUDiv_eq, if_true]
  by_cases h : 2 ^ (w - 1) ≤ val x
  · have hx : x.msb = true := (msb_iff x).mpr h
    rw [hx, if_pos h]
    dsimp only
    simp only [val, BitVec.toNat_neg, BitVec.toNat_allOnes]
    have h2 : 1 ≤ 2 ^ w := Nat.one_le_two_pow
    rw [Nat.sub_sub_self h2, Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))]; rfl
  · have hx : x.msb = false := by
      cases e : x.msb
      · rfl
      · exact absurd ((msb_iff x).mp e) h
    rw [hx, if_neg h]
    dsimp only
    simp only [val, BitVec.toNat_allOnes]
    rw [Int.ofNat_sub Nat.one_le_two_pow, cast_pow]; rfl

end Vik
