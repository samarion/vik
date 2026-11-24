import Vik.Arith

/-!
# Signed division

The lowering divides signed values through their magnitudes. These lemmas
relate its terms to `Int.tdiv`, `Int.tmod` and `Int.fmod`, which give the signed
values of `bvsdiv`, `bvsrem` and `bvsmod` (see `sdiv_val`, `srem_val`,
`smod_val`).
-/

namespace Vik

/-- The magnitude of an integer. -/
def mag (s : Int) : Int := if s < 0 then -s else s

theorem mag_nonneg (s : Int) : 0 ≤ mag s := by unfold mag; split <;> omega

theorem tdiv_mag (s t : Int) :
    s.tdiv t = (if (s < 0 ↔ t < 0) then 1 else -1) * (mag s / mag t) := by
  unfold mag
  by_cases hs : s < 0 <;> by_cases ht : t < 0
  · obtain ⟨A, rfl⟩ : ∃ A, s = -A := ⟨-s, by omega⟩
    obtain ⟨B, rfl⟩ : ∃ B, t = -B := ⟨-t, by omega⟩
    simp only [hs, ht, iff_self, if_true, Int.neg_neg, Int.one_mul, Int.neg_tdiv, Int.tdiv_neg]
    rw [Int.tdiv_eq_ediv_of_nonneg (by omega)]
  · obtain ⟨A, rfl⟩ : ∃ A, s = -A := ⟨-s, by omega⟩
    simp only [hs, ht, if_true, if_false, Int.neg_neg, Int.neg_tdiv, iff_false, not_true_eq_false]
    rw [Int.tdiv_eq_ediv_of_nonneg (by omega)]; omega
  · obtain ⟨B, rfl⟩ : ∃ B, t = -B := ⟨-t, by omega⟩
    simp only [hs, ht, if_true, if_false, Int.neg_neg, Int.tdiv_neg, false_iff, not_true_eq_false]
    rw [Int.tdiv_eq_ediv_of_nonneg (by omega)]; omega
  · simp only [hs, ht, iff_self, if_true, if_false, Int.one_mul]
    rw [Int.tdiv_eq_ediv_of_nonneg (by omega)]

theorem tmod_mag (s t : Int) : s.tmod t = (if s < 0 then -1 else 1) * (mag s % mag t) := by
  unfold mag
  have ht : s.tmod t = s.tmod (if t < 0 then -t else t) := by split <;> simp [Int.tmod_neg]
  have ht' : ∀ v : Int, v % t = v % (if t < 0 then -t else t) := by
    intro v; split <;> simp [Int.emod_neg]
  by_cases hs : s < 0
  · obtain ⟨A, rfl⟩ : ∃ A, s = -A := ⟨-s, by omega⟩
    simp only [hs, if_true, Int.neg_neg, Int.neg_tmod]
    rw [Int.tmod_eq_emod_of_nonneg (by omega), ht', Int.neg_one_mul]
  · simp only [hs, if_false, Int.one_mul]
    rw [Int.tmod_eq_emod_of_nonneg (by omega), ht']

theorem fmod_tmod (s t : Int) :
    s.fmod t = s.tmod t + (if ¬(s < 0 ↔ t < 0) ∧ s.tmod t ≠ 0 then t else 0) := by
  rw [Int.fmod_eq_tmod]
  congr 1
  by_cases hd : t ∣ s
  · have : s.tmod t = 0 := Int.dvd_iff_tmod_eq_zero.mp hd
    simp [hd, this]
  · have : s.tmod t ≠ 0 := fun h => hd (Int.dvd_iff_tmod_eq_zero.mpr h)
    simp only [hd, if_false, this, ne_eq, not_false_eq_true, and_true]
    by_cases hs : 0 ≤ s <;> by_cases ht' : 0 ≤ t
    · simp [hs, ht']; omega
    · simp [hs, ht']; omega
    · simp only [hs, ht', if_false, if_true]
      rw [Int.natAbs_of_nonneg ht']; simp; omega
    · simp only [hs, ht', if_false]
      have : t.toNat = 0 := by omega
      simp [this]; omega

/-! ## A constant divisor -/

/-- `bvsdiv` by a constant of signed value `t ≠ 0`: `modulo(±q, w, -1, 0)` for the
    truncated quotient `q` of `sdivide(a, w, |t|)`. -/
theorem sdiv_const_lowering (s t : Int) (ht : t ≠ 0) :
    (if 0 < t then s.tdiv (mag t) else -(s.tdiv (mag t))) = s.tdiv t := by
  unfold mag
  by_cases h : 0 < t
  · simp [h, show ¬t < 0 by omega]
  · simp only [h, if_false, show t < 0 by omega, if_true, Int.tdiv_neg, Int.neg_neg]

/-- `bvsrem` by a constant: `modulo(r, w, -1, 0)` for the remainder `r` of `sdivide`. -/
theorem srem_const_lowering (s t : Int) : s.tmod (mag t) = s.tmod t := by
  unfold mag; split <;> simp [Int.tmod_neg]

/-- `bvsmod` by a constant: `modulo(r + z * t, w, -1, 0)`, with `z` from `smodz`. -/
theorem smod_const_lowering (s t : Int) (ht : t ≠ 0) :
    let r := s.tmod (mag t)
    let differ := if 0 < t then s < 0 else ¬s < 0
    r + (if differ ∧ r ≠ 0 then 1 else 0) * t = s.fmod t := by
  intro r differ
  rw [fmod_tmod s t, ← srem_const_lowering s t]
  have hd : differ ↔ ¬(s < 0 ↔ t < 0) := by
    simp only [differ]; by_cases h : 0 < t
    · simp only [h, if_true]; constructor <;> intro <;> omega
    · simp only [h, if_false]; constructor <;> intro <;> omega
  by_cases hc : differ ∧ r ≠ 0
  · have : ¬(s < 0 ↔ t < 0) ∧ s.tmod (mag t) ≠ 0 := ⟨hd.mp hc.1, hc.2⟩
    simp only [r] at hc
    rw [if_pos hc, if_pos this, Int.one_mul]
  · have : ¬(¬(s < 0 ↔ t < 0) ∧ s.tmod (mag t) ≠ 0) := fun h => hc ⟨hd.mpr h.1, h.2⟩
    simp only [r] at hc
    rw [if_neg hc, if_neg this, Int.zero_mul]

/-- The bounds the `modulo` of these lowerings assumes: values in `[-2^w, 2^w - 1]`. -/
theorem signed_const_bounds (s t half : Int) (hs : -half ≤ s ∧ s ≤ half - 1) (ht : t ≠ 0)
    (ht' : mag t ≤ half) :
    (-(2 * half) ≤ s.tdiv t ∧ s.tdiv t ≤ 2 * half - 1) ∧
      (-(2 * half) ≤ s.tmod t ∧ s.tmod t ≤ 2 * half - 1) ∧
      (-(2 * half) ≤ s.fmod t ∧ s.fmod t ≤ 2 * half - 1) := by
  have hm : 0 < mag t := by unfold mag; split <;> omega
  have hq := Int.ediv_le_self (mag t) (mag_nonneg s)
  have hq0 := Int.ediv_nonneg (mag_nonneg s) (mag_nonneg t)
  have hr0 := Int.emod_nonneg (mag s) (Int.ne_of_gt hm)
  have hr1 := Int.emod_lt_of_pos (mag s) hm
  have hms : mag s ≤ half := by unfold mag; split <;> omega
  have ha : 1 ≤ half := by unfold mag at hm ht'; split at hm <;> omega
  have hd := tdiv_mag s t
  have hr := tmod_mag s t
  refine ⟨?_, ?_, ?_⟩
  · rw [hd]; split <;> omega
  · rw [hr]; split <;> omega
  · rw [fmod_tmod s t, hr]
    have : -half ≤ t ∧ t ≤ half := by unfold mag at ht'; split at ht' <;> omega
    have hmt : mag t = if t < 0 then -t else t := rfl
    by_cases h1 : s < 0 <;> by_cases h2 : t < 0 <;>
      simp only [h1, h2, if_true, if_false, iff_self, iff_true, iff_false,
        not_true_eq_false, not_false_eq_true, true_and, false_and] at hmt ⊢ <;> (try split) <;> omega

/-! ## An unknown divisor -/

/-- The `cases` tagged `abs`: the magnitude of the signed value. -/
theorem abs_lowering {w : Nat} (x : BitVec w) (hw : 0 < w) :
    (if 2 ^ (w - 1) ≤ val x then 2 ^ w - val x else val x) = mag x.toInt ∧
      0 ≤ mag x.toInt ∧ mag x.toInt ≤ 2 ^ (w - 1) := by
  have := toInt_eq x hw
  have := val_range x; have := two_pow_pred hw; unfold Range mag at *
  split <;> split <;> omega

private theorem sign_iff {w : Nat} (x : BitVec w) (hw : 0 < w) :
    x.toInt < 0 ↔ 2 ^ (w - 1) ≤ val x := toInt_neg_iff x hw

/-- `bvsdiv` by an unknown divisor: the quotient `q` of the magnitudes, negated
    (`sdivq`) when the signs differ, and `sdiv0` for a zero divisor. -/
theorem sdiv_lowering {w : Nat} (x y : BitVec w) (hw : 0 < w) :
    let na := 2 ^ (w - 1) ≤ val x
    let nb := 2 ^ (w - 1) ≤ val y
    let q := mag x.toInt / mag y.toInt
    val (x.smtSDiv y) =
      if val y = 0 then (if na then 1 else 2 ^ w - 1)
      else if ¬(na ↔ nb) ∧ 1 ≤ q then 2 ^ w - q else q := by
  intro na nb q
  by_cases hy : val y = 0
  · have : y = 0#w := by apply BitVec.eq_of_toNat_eq; simp only [val] at hy; simp; omega
    rw [if_pos hy, this, sdiv_zero_val x hw]
  · have hy' : y ≠ 0#w := by intro h; apply hy; simp [h, val]
    rw [if_neg hy, sdiv_val x y hy', tdiv_mag]
    simp only [sign_iff x hw, sign_iff y hw]
    have ⟨_, hA0, hA1⟩ := abs_lowering x hw
    have ⟨_, hB0, hB1⟩ := abs_lowering y hw
    have hq0 : 0 ≤ q := Int.ediv_nonneg hA0 hB0
    have hq1 : q ≤ mag x.toInt := Int.ediv_le_self _ hA0
    have h2 := two_pow_pred hw
    have hp := pow_pos' (w - 1)
    by_cases hs : (na ↔ nb)
    · simp only [na, nb] at hs
      rw [if_pos hs, if_neg (fun h => h.1 hs), Int.one_mul, Int.emod_eq_of_lt hq0 (by omega)]
    · simp only [na, nb] at hs
      rw [if_neg hs, Int.neg_one_mul]
      by_cases hq : 1 ≤ q
      · rw [if_pos ⟨hs, hq⟩]
        have : -q = (2 ^ w - q) + (-1) * 2 ^ w := by omega
        rw [this, Int.add_mul_emod_self_right, Int.emod_eq_of_lt (by omega) (by omega)]
      · rw [if_neg (fun h => hq h.2)]
        have : mag x.toInt / mag y.toInt = 0 := by simp only [q] at hq; omega
        simp [this, q]

/-- `bvsrem` by an unknown divisor: the remainder `r` of the magnitudes, negated
    (`sremr`) for a negative dividend, and the dividend (`srem0`) for a zero divisor. -/
theorem srem_lowering {w : Nat} (x y : BitVec w) (hw : 0 < w) :
    let na := 2 ^ (w - 1) ≤ val x
    let r := mag x.toInt % mag y.toInt
    val (x.srem y) =
      if val y = 0 then val x
      else if na ∧ 1 ≤ r then 2 ^ w - r else r := by
  intro na r
  rw [srem_val]
  by_cases hy : val y = 0
  · have : y.toInt = 0 := by
      rw [toInt_eq y hw, hy]; have := pow_pos' (w - 1); simp; omega
    rw [if_pos hy, this, Int.tmod_zero, ← val_eq_toInt_emod]
  · rw [if_neg hy, tmod_mag]
    simp only [sign_iff x hw]
    have ⟨_, hA0, hA1⟩ := abs_lowering x hw
    have ⟨hB, hB0, hB1⟩ := abs_lowering y hw
    have hBpos : 0 < mag y.toInt := by
      rw [← hB]; have := val_range y; unfold Range at this; split <;> omega
    have hr0 : 0 ≤ r := Int.emod_nonneg _ (Int.ne_of_gt hBpos)
    have hr1 : r < mag y.toInt := Int.emod_lt_of_pos _ hBpos
    have h2 := two_pow_pred hw
    have hp := pow_pos' (w - 1)
    by_cases hs : na
    · simp only [na] at hs
      rw [if_pos hs, Int.neg_one_mul]
      by_cases hr : 1 ≤ r
      · rw [if_pos ⟨hs, hr⟩]
        have : -r = (2 ^ w - r) + (-1) * 2 ^ w := by omega
        rw [this, Int.add_mul_emod_self_right, Int.emod_eq_of_lt (by omega) (by omega)]
      · rw [if_neg (fun h => hr h.2)]
        have : mag x.toInt % mag y.toInt = 0 := by simp only [r] at hr; omega
        simp [this, r]
    · simp only [na] at hs
      rw [if_neg hs, if_neg (fun h => hs h.1), Int.one_mul, Int.emod_eq_of_lt hr0 (by omega)]

/-- `bvsmod` by an unknown divisor: the remainder `rem` of `srem`, plus the
    divisor (`smodr`, through `modulo(rem + b, w, 0, 1)`) when the signs differ
    and `r ≠ 0`, and the dividend (`srem0`) for a zero divisor. -/
theorem smod_lowering {w : Nat} (x y : BitVec w) (hw : 0 < w) :
    let na := 2 ^ (w - 1) ≤ val x
    let nb := 2 ^ (w - 1) ≤ val y
    let r := mag x.toInt % mag y.toInt
    let rem := if na ∧ 1 ≤ r then 2 ^ w - r else r
    val (x.smod y) =
      if val y = 0 then val x
      else if ¬(na ↔ nb) ∧ r ≠ 0 then (rem + val y) % 2 ^ w else rem := by
  intro na nb r rem
  have hsrem := srem_lowering x y hw
  simp only at hsrem
  rw [smod_val]
  by_cases hy : val y = 0
  · have : y.toInt = 0 := by
      rw [toInt_eq y hw, hy]; have := pow_pos' (w - 1); simp; omega
    rw [if_pos hy, this, Int.fmod_zero, ← val_eq_toInt_emod]
  · have hy0 : y.toInt ≠ 0 := by
      intro h; apply hy; rw [val_eq_toInt_emod, h]; rfl
    rw [if_neg hy] at hsrem ⊢
    rw [srem_val] at hsrem
    rw [fmod_tmod _ _]
    simp only [sign_iff x hw, sign_iff y hw]
    have ht : x.toInt.tmod y.toInt = 0 ↔ r = 0 := by
      rw [tmod_mag]; simp only [r]; split <;> omega
    have hrem : rem = x.toInt.tmod y.toInt % 2 ^ w := hsrem.symm
    by_cases hc : ¬(na ↔ nb) ∧ r ≠ 0
    · have hc' : ¬(2 ^ (w - 1) ≤ val x ↔ 2 ^ (w - 1) ≤ val y) ∧ x.toInt.tmod y.toInt ≠ 0 :=
        ⟨hc.1, fun h => hc.2 (ht.mp h)⟩
      rw [if_pos hc', if_pos hc, hrem, val_eq_toInt_emod y, Int.emod_add_emod, Int.add_emod_emod]
    · have hc' : ¬(¬(2 ^ (w - 1) ≤ val x ↔ 2 ^ (w - 1) ≤ val y) ∧ x.toInt.tmod y.toInt ≠ 0) :=
        fun h => hc ⟨h.1, fun h' => h.2 (ht.mpr h')⟩
      rw [if_neg hc', if_neg hc, hrem, Int.add_zero]

end Vik
