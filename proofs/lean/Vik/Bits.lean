import Vik.Arith

/-!
# Bits

The lowering decomposes a value into bits with the `bits` rule, rebuilds values
from bits, and computes products as sums of shifted partial products. This file
relates those terms to the bit-vector operations: bitwise operations, products,
`extract`, `concat`, `repeat`, rotations, extensions, comparisons and equality.
-/

namespace Vik

private theorem cast_pow (w : Nat) : ((2 ^ w : Nat) : Int) = 2 ^ w := by simp

theorem bitSum_congr {n : Nat} {f g : Nat → Int} (h : ∀ i, i < n → f i = g i) : bitSum n f = bitSum n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [bitSum]
    rw [ih (fun i hi => h i (by omega)), h n (by omega)]

/-- The `i`-th bit of a value, through the `bits` rule, is the bit of the vector. -/
theorem bit_val {w : Nat} (x : BitVec w) (i : Nat) : bit (val x) i = if x.getLsbD i then 1 else 0 := by
  rw [← BitVec.testBit_toNat, Nat.testBit_eq_decide_div_mod_eq]
  simp only [bit, val]
  have h : (x.toNat : Int) / 2 ^ i % 2 = ((x.toNat / 2 ^ i % 2 : Nat) : Int) := by
    simp [Int.natCast_ediv, Int.natCast_emod]
  rw [h]
  rcases Nat.mod_two_eq_zero_or_one (x.toNat / 2 ^ i) with e | e <;> simp [e]

/-- A value is the sum of its bits. -/
theorem val_bits {w : Nat} (x : BitVec w) : val x = bitSum w (fun i => if x.getLsbD i then 1 else 0) := by
  rw [(bits_facts (val_range x)).2]
  exact bitSum_congr (fun i _ => bit_val x i)

/-- The atoms of the bits of `t` (`b_i ≥ 1`) are the bits of the vector. -/
theorem bit_atom {w : Nat} (x : BitVec w) (i : Nat) : bit (val x) i ≥ 1 ↔ x.getLsbD i = true := by
  rw [bit_val]; split <;> simp_all

/-- The bits of `2^w - 1 - t` (`bvnot`) are the negated bits of `t`. -/
theorem not_bits {w : Nat} (x : BitVec w) (i : Nat) (hi : i < w) : (~~~x).getLsbD i = !x.getLsbD i := by
  simp [hi]

/-- `bitConstant`: a bit as `0` or `1`. -/
def bitValue (b : Bool) : Int := if b then 1 else 0

/-- `fromBits`: `bvand`, `bvor` and `bvxor` of decomposed values are the sums
    of the gates of their bits. -/
theorem and_val {w : Nat} (x y : BitVec w) :
    val (x &&& y) = bitSum w (fun i => bitValue (x.getLsbD i && y.getLsbD i)) := by
  rw [val_bits]; exact bitSum_congr (fun i _ => by simp [bitValue, BitVec.getLsbD_and])

theorem or_val {w : Nat} (x y : BitVec w) :
    val (x ||| y) = bitSum w (fun i => bitValue (x.getLsbD i || y.getLsbD i)) := by
  rw [val_bits]; exact bitSum_congr (fun i _ => by simp [bitValue, BitVec.getLsbD_or])

theorem xor_val {w : Nat} (x y : BitVec w) :
    val (x ^^^ y) = bitSum w (fun i => bitValue (x.getLsbD i ^^ y.getLsbD i)) := by
  rw [val_bits]; exact bitSum_congr (fun i _ => by simp [bitValue, BitVec.getLsbD_xor])

/-- `bitConstant(Not(g))`: `1 - b` for the constant `b` of `g`. -/
theorem bitValue_not (b : Bool) : bitValue (!b) = 1 - bitValue b := by
  cases b <;> rfl

/-! ## Masks -/

private theorem split_or_and (a b c d k : Nat) (hb : b < 2 ^ k) (hd : d < 2 ^ k) :
    (2 ^ k * a + b) &&& (2 ^ k * c + d) = 2 ^ k * (a &&& c) + (b &&& d) ∧
    (2 ^ k * a + b) ||| (2 ^ k * c + d) = 2 ^ k * (a ||| c) + (b ||| d) ∧
    (2 ^ k * a + b) ^^^ (2 ^ k * c + d) = 2 ^ k * (a ^^^ c) + (b ^^^ d) := by
  have hand : b &&& d < 2 ^ k := Nat.lt_of_le_of_lt Nat.and_le_left hb
  have hor : b ||| d < 2 ^ k := Nat.or_lt_two_pow hb hd
  have hxor : b ^^^ d < 2 ^ k := Nat.xor_lt_two_pow hb hd
  refine ⟨?_, ?_, ?_⟩ <;> apply Nat.eq_of_testBit_eq <;> intro j <;>
    simp only [Nat.testBit_two_pow_mul_add _ hb, Nat.testBit_two_pow_mul_add _ hd,
      Nat.testBit_two_pow_mul_add _ hand, Nat.testBit_two_pow_mul_add _ hor,
      Nat.testBit_two_pow_mul_add _ hxor, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor] <;>
    split <;> rfl

private theorem xor_ones (l k : Nat) (hl : l < 2 ^ k) : l ^^^ (2 ^ k - 1) = 2 ^ k - 1 - l := by
  have h := BitVec.toNat_not (x := BitVec.ofNat k l)
  have h2 : ~~~BitVec.ofNat k l = BitVec.ofNat k l ^^^ BitVec.allOnes k := by
    rw [BitVec.xor_allOnes]
  rw [h2, BitVec.toNat_xor, BitVec.toNat_allOnes, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl] at h
  exact h

/-- `masked`: `bvand`, `bvor` and `bvxor` with a mask of low ones `2^k - 1`,
    where `low = t mod 2^k` (the remainder of `divide(t, 2^k, ...)`) and
    `high = t - low`. -/
theorem masked_low {w k : Nat} (x : BitVec w) (hk : k ≤ w) :
    let low := val x % 2 ^ k
    let high := val x - low
    let mask : Int := 2 ^ k - 1
    val (x &&& BitVec.ofNat w (2 ^ k - 1)) = low ∧
    val (x ||| BitVec.ofNat w (2 ^ k - 1)) = high + mask ∧
    val (x ^^^ BitVec.ofNat w (2 ^ k - 1)) = high + (mask - low) := by
  intro low high mask
  have hkw : 2 ^ k ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hk
  have hpk : 0 < 2 ^ k := Nat.two_pow_pos k
  have hmask : (BitVec.ofNat w (2 ^ k - 1)).toNat = 2 ^ k * 0 + (2 ^ k - 1) := by
    simp only [BitVec.toNat_ofNat, Nat.mul_zero, Nat.zero_add]; exact Nat.mod_eq_of_lt (by omega)
  have hx : x.toNat = 2 ^ k * (x.toNat / 2 ^ k) + x.toNat % 2 ^ k := (Nat.div_add_mod _ _).symm
  have hl := Nat.mod_lt x.toNat hpk
  have ⟨ha, ho, hxo⟩ := split_or_and (x.toNat / 2 ^ k) (x.toNat % 2 ^ k) 0 (2 ^ k - 1) k hl (by omega)
  have hlow : low = ((x.toNat % 2 ^ k : Nat) : Int) := by simp [low, val, Int.natCast_emod]
  have hhigh : high = ((2 ^ k * (x.toNat / 2 ^ k) : Nat) : Int) := by
    simp only [high, hlow, val]; omega
  have hmask' : mask = ((2 ^ k - 1 : Nat) : Int) := by
    simp only [mask]; rw [Int.ofNat_sub (by omega), cast_pow]; rfl
  simp only [val, BitVec.toNat_and, BitVec.toNat_or, BitVec.toNat_xor, hmask]
  rw [hx, ha, ho, hxo, Nat.and_zero, Nat.or_zero, Nat.xor_zero, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_eq_of_lt hl, xor_ones _ _ hl]
  have : x.toNat % 2 ^ k ||| 2 ^ k - 1 = 2 ^ k - 1 := by
    apply Nat.eq_of_testBit_eq; intro j
    simp only [Nat.testBit_or, Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow]
    by_cases h : j < k <;> simp [h]
  rw [this, hlow, hhigh, hmask']
  refine ⟨by simp, by omega, by omega⟩

/-- `masked` with a mask of high ones `2^w - 2^k`. -/
theorem masked_high {w k : Nat} (x : BitVec w) (hk : k ≤ w) :
    let low := val x % 2 ^ k
    let high := val x - low
    let mask : Int := 2 ^ w - 2 ^ k
    val (x &&& BitVec.ofNat w (2 ^ w - 2 ^ k)) = high ∧
    val (x ||| BitVec.ofNat w (2 ^ w - 2 ^ k)) = low + mask ∧
    val (x ^^^ BitVec.ofNat w (2 ^ w - 2 ^ k)) = low + (mask - high) := by
  intro low high mask
  have hkw : 2 ^ w = 2 ^ k * 2 ^ (w - k) := by rw [← Nat.pow_add]; congr 1; omega
  have hpk : 0 < 2 ^ k := Nat.two_pow_pos k
  have hpwk : 0 < 2 ^ (w - k) := Nat.two_pow_pos (w - k)
  have hpw : 0 < 2 ^ w := Nat.two_pow_pos w
  have hmask : (BitVec.ofNat w (2 ^ w - 2 ^ k)).toNat = 2 ^ k * (2 ^ (w - k) - 1) + 0 := by
    simp only [BitVec.toNat_ofNat, Nat.add_zero]
    rw [Nat.mod_eq_of_lt (by omega), hkw, Nat.mul_sub_one]
  have hx : x.toNat = 2 ^ k * (x.toNat / 2 ^ k) + x.toNat % 2 ^ k := (Nat.div_add_mod _ _).symm
  have hl := Nat.mod_lt x.toNat hpk
  have hh : x.toNat / 2 ^ k < 2 ^ (w - k) := by
    apply Nat.div_lt_of_lt_mul; rw [← hkw]; exact x.isLt
  have ⟨ha, ho, hxo⟩ := split_or_and (x.toNat / 2 ^ k) (x.toNat % 2 ^ k) (2 ^ (w - k) - 1) 0 k hl hpk
  have hlow : low = ((x.toNat % 2 ^ k : Nat) : Int) := by simp [low, val, Int.natCast_emod]
  have hhigh : high = ((2 ^ k * (x.toNat / 2 ^ k) : Nat) : Int) := by
    simp only [high, hlow, val]; omega
  have hmask' : mask = ((2 ^ k * (2 ^ (w - k) - 1) : Nat) : Int) := by
    simp only [mask]; rw [Nat.mul_sub_one, ← hkw, Int.ofNat_sub (Nat.pow_le_pow_right (by decide) hk)]
    simp
  simp only [val, BitVec.toNat_and, BitVec.toNat_or, BitVec.toNat_xor, hmask]
  rw [hx, ha, ho, hxo, Nat.and_zero, Nat.or_zero, Nat.xor_zero, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_eq_of_lt hh, xor_ones _ _ hh]
  have : x.toNat / 2 ^ k ||| 2 ^ (w - k) - 1 = 2 ^ (w - k) - 1 := by
    apply Nat.eq_of_testBit_eq; intro j
    simp only [Nat.testBit_or, Nat.testBit_two_pow_sub_one]
    by_cases h : j < w - k
    · simp [h]
    · simp only [h, decide_false, Bool.or_false]
      exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hh (Nat.pow_le_pow_right (by decide) (by omega)))
  rw [this, hlow, hhigh, hmask']
  have hle : 2 ^ k * (x.toNat / 2 ^ k) ≤ 2 ^ k * (2 ^ (w - k) - 1) := Nat.mul_le_mul_left _ (by omega)
  refine ⟨by simp, by omega, ?_⟩
  rw [Nat.mul_sub]
  omega

/-! ## Products -/

/-- The sum of the partial products of `a` by the bits of `b`: a partial
    product is the `cases` tagged `part`, `a * 2^i` if bit `i` of `b` is set. -/
def partials (a b : Int) : Nat → Int
  | 0 => 0
  | n + 1 => partials a b n + (if bit b n = 1 then a * 2 ^ n else 0)

theorem partials_eq (a b : Int) (n : Nat) : partials a b n = a * bitSum n (bit b) := by
  induction n with
  | zero => simp [partials, bitSum]
  | succ n ih =>
    simp only [partials, bitSum, ih, Int.mul_add]
    have := bit_range b n
    by_cases h : bit b n = 1
    · rw [if_pos h, h, Int.mul_one]
    · have : bit b n = 0 := by omega
      rw [if_neg h, this]; simp

/-- The bounds of the `part` cases rule: `0 ≤ partial ≤ 2^i * (2^w - 1)`. -/
theorem partial_bounds {w : Nat} {a : Int} (ha : Range w a) (b : Int) (i : Nat) :
    0 ≤ (if bit b i = 1 then a * 2 ^ i else 0) ∧ (if bit b i = 1 then a * 2 ^ i else 0) ≤ 2 ^ i * (2 ^ w - 1) := by
  have hp := pow_pos' i
  unfold Range at ha
  split
  · rw [Int.mul_comm]
    exact ⟨Int.mul_nonneg (Int.le_of_lt hp) ha.1, Int.mul_le_mul_of_nonneg_left ha.2 (Int.le_of_lt hp)⟩
  · exact ⟨Int.le_refl 0, Int.mul_nonneg (Int.le_of_lt hp) (by omega)⟩

/-- `exactProduct(a, b, w)`: the sum of the partial products is `a * b`. -/
theorem exactProduct_eq {w : Nat} {b : Int} (a : Int) (hb : Range w b) : partials a b w = a * b := by
  rw [partials_eq, ← (bits_facts hb).2]

/-- `bvmul` of two unknown values: `modulo(Σ partials, w, 0, 2^w - 2)`. -/
theorem mul_val {w : Nat} (x y : BitVec w) (hw : 0 < w) :
    val (x * y) = partials (val x) (val y) w % 2 ^ w ∧
      0 * 2 ^ w ≤ partials (val x) (val y) w ∧
      partials (val x) (val y) w < ((2 ^ w - 2) + 1) * 2 ^ w := by
  rw [exactProduct_eq _ (val_range y)]
  have hx := val_range x; have hy := val_range y; unfold Range at hx hy
  have h2 : (2 : Int) ≤ 2 ^ w := by
    have := two_pow_pred hw; have := pow_pos' (w - 1); omega
  refine ⟨?_, ?_, ?_⟩
  · simp only [val, BitVec.toNat_mul, Int.natCast_emod, Int.natCast_mul, cast_pow]
  · rw [Int.zero_mul]; exact Int.mul_nonneg hx.1 hy.1
  · have : val x * val y ≤ (2 ^ w - 1) * (2 ^ w - 1) :=
      Int.mul_le_mul hx.2 hy.2 hy.1 (by omega)
    have e : (2 ^ w - 2 + 1) * 2 ^ w = (2 ^ w - 1) * (2 ^ w - 1) + (2 ^ w - 1 : Int) := by
      simp only [Int.sub_mul, Int.mul_sub, Int.add_mul, Int.one_mul, Int.mul_one]; omega
    omega

/-! ## `extract`, `concat`, `repeat`, rotations, extensions -/

/-- `extract(i, j)`: the quotient of `divide(t, 2^j, 2^(w-j) - 1)`, then, below
    the top bit, the remainder of `divide(q, 2^(i-j+1), 2^(w-i-1) - 1)`. -/
theorem extract_val {w : Nat} (x : BitVec w) (i j : Nat) (hji : j ≤ i) (hi : i < w) :
    let q := val x / 2 ^ j
    val (BitVec.extractLsb i j x) = (if i = w - 1 then q else q % 2 ^ (i - j + 1)) ∧
      (0 ≤ val x ∧ val x ≤ (2 ^ (w - j) - 1) * 2 ^ j + 2 ^ j - 1) ∧
      (0 ≤ q ∧ q ≤ (2 ^ (w - i - 1) - 1) * 2 ^ (i - j + 1) + 2 ^ (i - j + 1) - 1) := by
  intro q
  have hwj : (2 : Int) ^ w = 2 ^ (w - j) * 2 ^ j := by rw [← Int.pow_add]; congr 1; omega
  have hwi : (2 : Int) ^ (w - j) = 2 ^ (w - i - 1) * 2 ^ (i - j + 1) := by
    rw [← Int.pow_add]; congr 1; omega
  have hx := val_range x; unfold Range at hx
  have hpj := pow_pos' j
  have hq0 : 0 ≤ q := Int.ediv_nonneg hx.1 (Int.le_of_lt hpj)
  have hq1 : q < 2 ^ (w - j) := by
    apply Int.ediv_lt_of_lt_mul hpj; rw [← hwj]; omega
  refine ⟨?_, ⟨hx.1, ?_⟩, ⟨hq0, ?_⟩⟩
  · have e : val (BitVec.extractLsb i j x) = q % 2 ^ (i - j + 1) := by
      simp only [val, BitVec.extractLsb_toNat, Nat.shiftRight_eq_div_pow, Int.natCast_emod,
        Int.natCast_ediv, cast_pow, q]
    rw [e]; split
    · rename_i h; apply Int.emod_eq_of_lt hq0
      have : i - j + 1 = w - j := by omega
      rw [this]; exact hq1
    · rfl
  · rw [Int.sub_mul, Int.one_mul, ← hwj]; omega
  · rw [Int.sub_mul, Int.one_mul, ← hwi]; omega

/-- `concat`: `hi * 2^wl + lo`. -/
theorem concat_val {wh wl : Nat} (x : BitVec wh) (y : BitVec wl) : val (x ++ y) = val x * 2 ^ wl + val y := by
  simp only [val, BitVec.toNat_append, Nat.shiftLeft_eq]
  rw [Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt y.isLt]
  push_cast; rw [Int.mul_comm]

/-- `repeat(k)`: `Σ j < k, 2^(j*w) * t`. -/
def repeatSum (w : Nat) (t : Int) : Nat → Int
  | 0 => 0
  | k + 1 => repeatSum w t k + 2 ^ (k * w) * t

theorem repeat_val {w : Nat} (x : BitVec w) (k : Nat) : val (BitVec.replicate k x) = repeatSum w (val x) k := by
  induction k with
  | zero => simp [val, repeatSum, BitVec.replicate]
  | succ k ih =>
    rw [BitVec.replicate_succ]
    simp only [val, BitVec.toNat_cast] at ih ⊢
    have := concat_val x (BitVec.replicate k x)
    simp only [val] at this
    rw [this, ih, repeatSum, Nat.mul_comm w k, Int.add_comm, Int.mul_comm]

/-- `rotate_left(k)`, for `s = k mod w > 0` (the lowering keeps `t` when `s = 0`):
    `2^s * r + q` from `divide(t, 2^(w-s), 2^s - 1)`. -/
theorem rotateLeft_val {w : Nat} (x : BitVec w) (k : Nat) (hw : 0 < w) :
    val (x.rotateLeft k) = 2 ^ (k % w) * (val x % 2 ^ (w - k % w)) + val x / 2 ^ (w - k % w) ∧
      0 ≤ val x ∧ val x ≤ (2 ^ (k % w) - 1) * 2 ^ (w - k % w) + 2 ^ (w - k % w) - 1 := by
  generalize hsdef : k % w = s at *
  have hsw : s < w := by rw [← hsdef]; exact Nat.mod_lt _ hw
  have hwn : 2 ^ w = 2 ^ s * 2 ^ (w - s) := by rw [← Nat.pow_add]; congr 1; omega
  have hwi : (2 : Int) ^ w = 2 ^ s * 2 ^ (w - s) := by rw [← Int.pow_add]; congr 1; omega
  have hx := val_range x; unfold Range at hx
  refine ⟨?_, hx.1, ?_⟩
  · simp only [val, BitVec.toNat_rotateLeft, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, hsdef]
    have h1 : x.toNat * 2 ^ s % 2 ^ w = 2 ^ s * (x.toNat % 2 ^ (w - s)) := by
      rw [hwn, Nat.mul_comm, Nat.mul_mod_mul_left]
    have h2 : x.toNat / 2 ^ (w - s) < 2 ^ s := by
      apply Nat.div_lt_of_lt_mul; rw [Nat.mul_comm, ← hwn]; exact x.isLt
    rw [h1, ← Nat.two_pow_add_eq_or_of_lt h2]
    push_cast; rfl
  · rw [Int.sub_mul, Int.one_mul, ← hwi]; omega

/-- `rotate_right(k)` is `rotate_left(w - k mod w)`. -/
theorem rotateRight_val {w : Nat} (x : BitVec w) (k : Nat) (hw : 0 < w) (hs : 0 < k % w) :
    val (x.rotateRight k) = val (x.rotateLeft (w - k % w)) := by
  have hj : k % w < w := Nat.mod_lt _ hw
  have hm : (w - k % w) % w = w - k % w := Nat.mod_eq_of_lt (by omega)
  simp only [val, BitVec.toNat_rotateRight, BitVec.toNat_rotateLeft, hm]
  rw [Nat.sub_sub_self (Nat.le_of_lt hj), Nat.or_comm]

/-- `zero_extend`: the same value. -/
theorem zeroExtend_val {w : Nat} (x : BitVec w) (k : Nat) : val (BitVec.setWidth (w + k) x) = val x := by
  simp only [val, BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) (by omega)))]

/-- `sign_extend(k)`: the `cases` tagged `ext`, `t + 2^(w+k) - 2^w` if negative. -/
theorem signExtend_val {w : Nat} (x : BitVec w) (k : Nat) :
    val (BitVec.signExtend (w + k) x) = if 2 ^ (w - 1) ≤ val x then val x + (2 ^ (w + k) - 2 ^ w) else val x := by
  have h := BitVec.toNat_signExtend x (v := w + k)
  have hz := zeroExtend_val x k
  simp only [val] at hz ⊢
  rw [h]; push_cast; rw [hz]
  have hle : 2 ^ w ≤ 2 ^ (w + k) := Nat.pow_le_pow_right (by decide) (by omega)
  by_cases hm : x.msb = true
  · have := (msb_iff x).mp hm
    simp only [val] at this
    rw [if_pos hm, if_pos this, Int.ofNat_sub hle, cast_pow, cast_pow]
  · have : ¬ 2 ^ (w - 1) ≤ (x.toNat : Int) := fun h' => hm ((msb_iff x).mpr h')
    rw [if_neg hm, if_neg this]; simp

/-! ## Comparisons and equality -/

theorem ult_iff {w : Nat} (x y : BitVec w) : x.ult y = true ↔ val x < val y := by
  rw [BitVec.ult_iff_lt, BitVec.lt_def]; simp [val]

theorem ule_iff {w : Nat} (x y : BitVec w) : x.ule y = true ↔ val x ≤ val y := by
  rw [BitVec.ule_iff_le, BitVec.le_def]; simp [val]

/-- `bvslt`: `(nl ∧ ¬nr) ∨ ((nl ↔ nr) ∧ l < r)`. -/
theorem slt_iff {w : Nat} (x y : BitVec w) (hw : 0 < w) :
    x.slt y = true ↔
      ((2 ^ (w - 1) ≤ val x ∧ ¬2 ^ (w - 1) ≤ val y) ∨
        ((2 ^ (w - 1) ≤ val x ↔ 2 ^ (w - 1) ≤ val y) ∧ val x < val y)) := by
  rw [BitVec.slt_iff_toInt_lt, toInt_eq x hw, toInt_eq y hw]
  have := val_range x; have := val_range y; have := two_pow_pred hw; unfold Range at *
  split <;> split <;> omega

/-- `bvsle`: `(nl ∧ ¬nr) ∨ ((nl ↔ nr) ∧ l ≤ r)`. -/
theorem sle_iff {w : Nat} (x y : BitVec w) (hw : 0 < w) :
    x.sle y = true ↔
      ((2 ^ (w - 1) ≤ val x ∧ ¬2 ^ (w - 1) ≤ val y) ∨
        ((2 ^ (w - 1) ≤ val x ↔ 2 ^ (w - 1) ≤ val y) ∧ val x ≤ val y)) := by
  rw [BitVec.sle_iff_toInt_le, toInt_eq x hw, toInt_eq y hw]
  have := val_range x; have := val_range y; have := two_pow_pred hw; unfold Range at *
  split <;> split <;> omega

/-- Equality of bit-vectors is equality of values. -/
theorem eq_iff {w : Nat} (x y : BitVec w) : x = y ↔ val x = val y := val_inj.symm

/-- Equality bit by bit, once both sides are decomposed. -/
theorem eq_iff_bits {w : Nat} (x y : BitVec w) : x = y ↔ ∀ i, i < w → (x.getLsbD i ↔ y.getLsbD i) := by
  constructor
  · intro h i _; rw [h]
  · intro h; apply BitVec.eq_of_getLsbD_eq; intro i hi
    have := h i hi
    revert this; cases x.getLsbD i <;> cases y.getLsbD i <;> simp

/-- `bvcomp`: the `cases` tagged `comp`, `1` if the values are equal. -/
theorem comp_val {w : Nat} (x y : BitVec w) :
    (if x = y then (1 : Int) else 0) = if val x = val y then 1 else 0 := by
  simp only [eq_iff]

end Vik
