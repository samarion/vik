/-!
# Real arithmetic

The rules on reals, over any ordered field of characteristic zero (in Mathlib,
`ℝ` is one, through the instances `grind` uses). `to_int` and `is_int` go
through `floor`: the greatest integer below `r`, which exists in the reals.
-/

set_option linter.unusedSectionVars false

namespace Vik.Real

open Lean.Grind

variable {R : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R]
  [OrderedRing R] [IsCharP R 0]

attribute [local instance] Lean.Grind.Ring.intCast

theorem cast_ne_zero {q : Int} (hq : q ≠ 0) : (q : R) ≠ 0 := by
  intro h
  have := (IsCharP.intCast_eq_zero_iff (α := R) 0 q).mp h
  simp at this; exact hq this

/-- `rat(p, q)`: the symbol is `p / q`, asserted as `q * k = p`. -/
theorem rat_facts (p q : Int) (hq : q ≠ 0) : (q : R) * ((p : R) / (q : R)) = p := by
  have := cast_ne_zero (R := R) hq
  grind

/-- `ratmul(p, q, t)`: the symbol is `p / q * t`, asserted as `q * k = p * t`. -/
theorem ratmul_facts (p q : Int) (t : R) (hq : q ≠ 0) : (q : R) * ((p : R) / (q : R) * t) = p * t := by
  have := cast_ne_zero (R := R) hq
  grind

theorem cast_nat_nonneg (n : Nat) : (0 : R) ≤ ((n : Int) : R) := by
  induction n with
  | zero => grind
  | succ n ih =>
    have : (((n + 1 : Nat) : Int) : R) = ((n : Int) : R) + 1 := by grind
    have := OrderedRing.zero_lt_one (R := R)
    grind

theorem cast_le {a b : Int} (h : a ≤ b) : (a : R) ≤ (b : R) := by
  obtain ⟨n, rfl⟩ : ∃ n : Nat, b = a + n := ⟨(b - a).toNat, by omega⟩
  have := cast_nat_nonneg (R := R) n
  grind

/-- A floor of `r`: an integer `k` with `k ≤ r < k + 1`. -/
def IsFloor (r : R) (k : Int) : Prop := (k : R) ≤ r ∧ r < (k : R) + 1

/-- `floor(r)`: the facts `k ≤ r` and `r < k + 1` are those of a floor, and pin `k`
    down, so `to_int` and the `floor` in `is_int` are the floor of `r`. -/
theorem floor_unique {r : R} {k j : Int} (hk : IsFloor r k) (hj : IsFloor r j) : k = j := by
  unfold IsFloor at hk hj
  apply Classical.byContradiction; intro h
  rcases Int.lt_or_gt_of_ne h with h | h
  · have := cast_le (R := R) (show k + 1 ≤ j by omega)
    grind
  · have := cast_le (R := R) (show j + 1 ≤ k by omega)
    grind

/-- `is_int(r)`: `r = floor(r)`. -/
theorem isInt_iff {r : R} {k : Int} (hk : IsFloor r k) : (∃ n : Int, r = n) ↔ r = k := by
  constructor
  · rintro ⟨n, rfl⟩
    have : IsFloor (n : R) n := ⟨Std.le_refl _, by grind⟩
    rw [floor_unique hk this]
  · intro h; exact ⟨k, h⟩

end Vik.Real
