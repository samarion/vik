/-!
# The rules of the lowering

Each rule of `LoweringCheck.check` introduces fresh symbols and asserts facts
about them. Here, for each rule, the values the symbols stand for are named, and
those values are shown to satisfy the facts, under the bounds the replay
guarantees for the rule's arguments. With these, a model of the surface script
extends to a model of the lowered script, so a refutation of the lowered script
refutes the surface script.

Integers stand for lowered terms. A bit-vector of width `w` lowers to its
unsigned value, an integer in `[0, 2^w - 1]`.
-/

namespace Vik

/-- The facts of `range`: `t` is the value of a bit-vector of width `w`. -/
def Range (w : Nat) (t : Int) : Prop := 0 ≤ t ∧ t ≤ 2 ^ w - 1

theorem pow_pos' (w : Nat) : (0 : Int) < 2 ^ w := Int.pow_pos (by decide)

/-! ## `range` -/

theorem range_toNat {w : Nat} (x : BitVec w) : Range w x.toNat := by
  have h := x.isLt
  have : ((x.toNat : Nat) : Int) < ((2 ^ w : Nat) : Int) := Int.ofNat_lt.mpr h
  simp only [Int.natCast_pow, Int.cast_ofNat_Int] at this
  constructor <;> omega

/-! ## `ite` -/

theorem ite_facts {α : Type} (c : Prop) [Decidable c] (t e : α) :
    (c → (if c then t else e) = t) ∧ (¬c → (if c then t else e) = e) := by
  constructor <;> intro h <;> simp only [h, if_true, if_false]

theorem ite_range {w : Nat} (c : Prop) [Decidable c] {t e : Int} (ht : Range w t) (he : Range w e) :
    Range w (if c then t else e) := by
  split <;> assumption

/-! ## `cases` -/

/-- `cases(tag, c, thn, els, lo, hi)`: the symbol is `thn` if `c`, `els` otherwise,
    and lies in `[lo, hi]`. -/
theorem cases_facts (c : Prop) [Decidable c] {thn els lo hi : Int}
    (ht : c → lo ≤ thn ∧ thn ≤ hi) (he : ¬c → lo ≤ els ∧ els ≤ hi) :
    let k := if c then thn else els
    (lo ≤ k ∧ k ≤ hi) ∧ (c → k = thn) ∧ (¬c → k = els) := by
  by_cases h : c <;> simp [h, ht, he]

/-! ## `modulo` -/

/-- `modulo(v, w, lo, hi)`: the remainder of `v` by `m = 2^w`, and the quotient,
    in `[lo, hi]` when `lo * m ≤ v < (hi + 1) * m`. -/
theorem modulo_facts {v m lo hi : Int} (hm : 0 < m) (h1 : lo * m ≤ v) (h2 : v < (hi + 1) * m) :
    let r := v % m
    let k := v / m
    (0 ≤ r ∧ r ≤ m - 1) ∧ (lo ≤ k ∧ k ≤ hi) ∧ v = r + k * m := by
  intro r k
  have e := Int.emod_add_mul_ediv v m
  have r0 := Int.emod_nonneg v (Int.ne_of_gt hm)
  have r1 := Int.emod_lt_of_pos v hm
  have k0 : lo ≤ k := (Int.le_ediv_iff_mul_le hm).mpr h1
  have k1 : k < hi + 1 := (Int.ediv_lt_iff_lt_mul hm).mpr h2
  refine ⟨⟨r0, by omega⟩, ⟨k0, by omega⟩, ?_⟩
  simp only [r, k]
  rw [Int.mul_comm]; omega

/-- With few quotients, `modulo` asserts the disjunction over them instead of a
    second symbol: one disjunct holds. -/
theorem modulo_facts_small {v m lo hi : Int} (hm : 0 < m) (h1 : lo * m ≤ v) (h2 : v < (hi + 1) * m) :
    let r := v % m
    (0 ≤ r ∧ r ≤ m - 1) ∧ ∃ k, lo ≤ k ∧ k ≤ hi ∧ v = r + k * m := by
  have ⟨hr, hk, he⟩ := modulo_facts hm h1 h2
  exact ⟨hr, _, hk.1, hk.2, he⟩

/-! ## `divide` -/

/-- `divide(v, d, qmax)`: quotient and remainder of `v ∈ [0, qmax * d + d - 1]` by `d > 0`. -/
theorem divide_facts {v d qmax : Int} (hd : 0 < d) (h0 : 0 ≤ v) (h1 : v ≤ qmax * d + d - 1) :
    let q := v / d
    let r := v % d
    (0 ≤ q ∧ q ≤ qmax) ∧ (0 ≤ r ∧ r ≤ d - 1) ∧ v = q * d + r := by
  have ⟨hr, hk, he⟩ := modulo_facts (v := v) (lo := 0) (hi := qmax) hd (by omega)
    (by rw [Int.add_mul]; omega)
  exact ⟨hk, hr, by rw [Int.add_comm] at he; exact he⟩

/-! ## `udiv` -/

/-- `udiv`, for `a, b ∈ [0, m - 1]`: the quotient and remainder of SMT-LIB's
    `bvudiv` and `bvurem`, where division by zero gives `m - 1` and `a`. The
    product `b * q` is asserted through the bits of `q` (see `exactProduct`). -/
theorem udiv_facts {a b m : Int} (ha : 0 ≤ a ∧ a ≤ m - 1) (hb : 0 ≤ b ∧ b ≤ m - 1) :
    let q := if b = 0 then m - 1 else a / b
    let r := if b = 0 then a else a % b
    (0 ≤ q ∧ q ≤ m - 1) ∧ (0 ≤ r ∧ r ≤ m - 1) ∧
      (b = 0 → q = m - 1 ∧ r = a) ∧ (b ≠ 0 → a = b * q + r ∧ r < b) := by
  intro q r
  by_cases h : b = 0
  · simp only [q, r, h, if_true]
    exact ⟨⟨by omega, by omega⟩, ha, by simp, by simp⟩
  · have hb' : 0 < b := by omega
    have e := Int.mul_ediv_add_emod a b
    have r0 := Int.emod_nonneg a h
    have r1 := Int.emod_lt_of_pos a hb'
    have q0 : 0 ≤ a / b := Int.ediv_nonneg ha.1 hb.1
    have q1 : a / b ≤ a := Int.ediv_le_self b ha.1
    simp only [q, r, h, if_false]
    refine ⟨⟨q0, by omega⟩, ⟨r0, by omega⟩, by simp, fun _ => ⟨e.symm, r1⟩⟩

/-! ## `sdivide` -/

/-- `sdivide(t, w, d, floor = true)`: the floor quotient and remainder of the
    signed value `s ∈ [-half, half - 1]` by `d > 0`. -/
theorem sdivide_floor_facts {s half d : Int} (hd : 0 < d) (hs : -half ≤ s ∧ s ≤ half - 1) :
    let q := s / d
    let r := s % d
    (-(half / d) - 1 ≤ q ∧ q ≤ (half - 1) / d) ∧ (0 ≤ r ∧ r ≤ d - 1) ∧ s = q * d + r := by
  intro q r
  have e := Int.mul_ediv_add_emod s d
  have r0 := Int.emod_nonneg s (Int.ne_of_gt hd)
  have r1 := Int.emod_lt_of_pos s hd
  have q1 : q ≤ (half - 1) / d := Int.ediv_le_ediv hd hs.2
  have q0 : -half / d ≤ q := Int.ediv_le_ediv hd hs.1
  have : -(half / d) - 1 ≤ -half / d := by
    have := Int.mul_ediv_add_emod half d
    have := Int.mul_ediv_add_emod (-half) d
    have := Int.emod_nonneg half (Int.ne_of_gt hd)
    have := Int.emod_lt_of_pos half hd
    have := Int.emod_nonneg (-half) (Int.ne_of_gt hd)
    have := Int.emod_lt_of_pos (-half) hd
    have h3 : d * (-half / d) > d * (-(half / d) - 1 - 1) := by
      rw [Int.mul_sub, Int.mul_sub, Int.mul_neg]; omega
    have := Int.lt_of_mul_lt_mul_left h3 (Int.le_of_lt hd)
    omega
  refine ⟨⟨by omega, q1⟩, ⟨r0, by omega⟩, ?_⟩
  rw [Int.mul_comm]; exact e.symm

/-- `sdivide(t, w, d, floor = false)`: the truncating quotient and remainder,
    as `bvsdiv` and `bvsrem` round. -/
theorem sdivide_trunc_facts {s half d : Int} (hd : 0 < d) (hs : -half ≤ s ∧ s ≤ half - 1) :
    let q := s.tdiv d
    let r := s.tmod d
    (-(half / d) - 1 ≤ q ∧ q ≤ (half - 1) / d) ∧ (-(d - 1) ≤ r ∧ r ≤ d - 1) ∧ s = q * d + r ∧
      (s < 0 → r ≤ 0) ∧ (¬s < 0 → 0 ≤ r) := by
  intro q r
  have e := Int.mul_tdiv_add_tmod s d
  by_cases hneg : s < 0
  · -- tdiv s d = -((-s) / d), tmod s d = -((-s) % d)
    have hq : q = -((-s) / d) := by
      simp only [q]; rw [← Int.neg_neg s, Int.neg_tdiv, Int.neg_neg,
        Int.tdiv_eq_ediv_of_nonneg (by omega)]
    have hr : r = -((-s) % d) := by
      simp only [r]; rw [← Int.neg_neg s, Int.neg_tmod, Int.neg_neg,
        Int.tmod_eq_emod_of_nonneg (by omega)]
    have r0 := Int.emod_nonneg (-s) (Int.ne_of_gt hd)
    have r1 := Int.emod_lt_of_pos (-s) hd
    have q0 : 0 ≤ (-s) / d := Int.ediv_nonneg (by omega) (by omega)
    have q1 : (-s) / d ≤ half / d := Int.ediv_le_ediv hd (by omega)
    have q2 : 0 ≤ half / d := Int.ediv_nonneg (by omega) (by omega)
    have q3 : 0 ≤ (half - 1) / d := Int.ediv_nonneg (by omega) (by omega)
    refine ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ?_, fun _ => by omega, fun h => absurd hneg h⟩
    rw [Int.mul_comm]; exact e.symm
  · have hq : q = s / d := by simp only [q]; rw [Int.tdiv_eq_ediv_of_nonneg (by omega)]
    have hr : r = s % d := by simp only [r]; rw [Int.tmod_eq_emod_of_nonneg (by omega)]
    have r0 := Int.emod_nonneg s (Int.ne_of_gt hd)
    have r1 := Int.emod_lt_of_pos s hd
    have q0 : 0 ≤ s / d := Int.ediv_nonneg (by omega) (by omega)
    have q1 : s / d ≤ (half - 1) / d := Int.ediv_le_ediv hd hs.2
    have q2 : 0 ≤ half / d := Int.ediv_nonneg (by omega) (by omega)
    refine ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ?_, fun h => absurd h hneg, fun _ => by omega⟩
    rw [Int.mul_comm]; exact e.symm

/-! ## `bits` -/

/-- `Σ i < n, 2^i * b i`. -/
def bitSum : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | n + 1, b => bitSum n b + 2 ^ n * b n

/-- The `i`-th bit of `t`, as `0` or `1`. -/
def bit (t : Int) (i : Nat) : Int := t / 2 ^ i % 2

theorem bit_range (t : Int) (i : Nat) : 0 ≤ bit t i ∧ bit t i ≤ 1 := by
  have := Int.emod_nonneg (t / 2 ^ i) (b := 2) (by decide)
  have := Int.emod_lt_of_pos (t / 2 ^ i) (b := 2) (by decide)
  unfold bit; omega

theorem bitSum_bit (t : Int) (n : Nat) : bitSum n (bit t) = t % 2 ^ n := by
  induction n with
  | zero => simp [bitSum]
  | succ n ih =>
    simp only [bitSum, ih, bit]
    have hp := pow_pos' n
    -- t % 2^(n+1) = t % 2^n + 2^n * (t / 2^n % 2)
    have e1 := Int.mul_ediv_add_emod t (2 ^ n)
    have e2 := Int.mul_ediv_add_emod (t / 2 ^ n) 2
    have e3 := Int.mul_ediv_add_emod t (2 ^ (n + 1))
    have hd : t / 2 ^ (n + 1) = t / 2 ^ n / 2 := by
      rw [Int.pow_succ, Int.ediv_ediv (Int.le_of_lt hp)]
    rw [hd, Int.pow_succ] at e3
    rw [Int.pow_succ]
    rw [Int.mul_assoc] at e3
    have := Int.emod_nonneg t (Int.ne_of_gt hp)
    have := Int.emod_lt_of_pos t hp
    -- both sides are t - 2^n * 2 * (t / 2^n / 2)
    have h2 : t % (2 ^ n * 2) = t - 2 ^ n * (2 * (t / 2 ^ n / 2)) := by omega
    rw [h2]
    have : 2 ^ n * (t / 2 ^ n % 2) = 2 ^ n * (t / 2 ^ n) - 2 ^ n * (2 * (t / 2 ^ n / 2)) := by
      rw [← Int.mul_sub]; congr 1; omega
    omega

/-- `bits(t, w)`: for `t ∈ [0, 2^w - 1]`, the bits of `t` are in `{0, 1}` and sum to `t`. -/
theorem bits_facts {t : Int} {w : Nat} (h : Range w t) :
    (∀ i, 0 ≤ bit t i ∧ bit t i ≤ 1) ∧ t = bitSum w (bit t) := by
  refine ⟨bit_range t, ?_⟩
  rw [bitSum_bit, Int.emod_eq_of_lt h.1 (by have := h.2; omega)]

/-! ## `int2bv` -/

/-- `int2bv(t, w)`: the remainder and quotient of `t` by `2^w`. -/
theorem int2bv_facts (t : Int) (w : Nat) :
    let k0 := t % 2 ^ w
    let k1 := t / 2 ^ w
    (0 ≤ k0 ∧ k0 ≤ 2 ^ w - 1) ∧ t = k0 + k1 * 2 ^ w := by
  have hp := pow_pos' w
  have := Int.emod_nonneg t (Int.ne_of_gt hp)
  have := Int.emod_lt_of_pos t hp
  have := Int.emod_add_mul_ediv t (2 ^ w)
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  rw [Int.mul_comm]; omega

/-! ## `smodz` -/

/-- `smodz`: whether `bvsmod` corrects the truncated remainder `r`, that is when
    the signs differ and `r ≠ 0`. -/
theorem smodz_facts (differ : Prop) [Decidable differ] (r : Int) :
    let z : Int := if differ ∧ r ≠ 0 then 1 else 0
    (0 ≤ z ∧ z ≤ 1) ∧ (¬differ → z = 0) ∧ (r = 0 → z = 0) ∧ (differ ∧ r ≠ 0 → z = 1) := by
  intro z
  by_cases h : differ ∧ r ≠ 0
  · simp only [z, h]; simp_all
  · simp only [z, h, if_false]; simp_all

/-! ## `store` -/

/-- `store`: the store symbol of an array sort is the update of a function at
    one index. It has no defining facts: the lowered script only applies it, and
    these are the facts the array reasoning uses. -/
def store {α β : Type} [DecidableEq α] (a : α → β) (i : α) (v : β) : α → β :=
  fun j => if j = i then v else a j

theorem store_same {α β : Type} [DecidableEq α] (a : α → β) (i : α) (v : β) : store a i v i = v := by
  simp [store]

theorem store_other {α β : Type} [DecidableEq α] (a : α → β) {i j : α} (v : β) (h : j ≠ i) :
    store a i v j = a j := by
  simp [store, h]

end Vik
