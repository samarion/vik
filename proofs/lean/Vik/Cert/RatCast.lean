import Vik.Real

/-!
# Rationals in an ordered field

The certificates of linear arithmetic carry rational numbers; their meaning in
an ordered field of characteristic zero is `num / den`.
-/

set_option linter.unusedSectionVars false

namespace Vik.Real

open Lean.Grind

variable {R : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R]
  [OrderedRing R] [IsCharP R 0]

attribute [local instance low] Lean.Grind.Ring.intCast

/-- The rational `q` in `R`. -/
def rat (q : Rat) : R := (q.num : R) / ((q.den : Int) : R)

theorem den_ne_zero (q : Rat) : ((q.den : Int) : R) ≠ 0 :=
  cast_ne_zero (by have := q.den_pos; omega)

theorem mul_den (q : Rat) : q * ((q.den : Int) : Rat) = q.num := by
  have h := Rat.num_divInt_den q
  rw [Rat.divInt_eq_div] at h
  have : ((q.den : Int) : Rat) ≠ 0 := by
    rw [Ne, ← Rat.intCast_zero, Rat.intCast_inj]; have := q.den_pos; omega
  have e : ((q.den : Int) : Rat) = (q.den : Rat) := Rat.intCast_natCast _
  rw [e] at this ⊢
  conv => lhs; rw [← h]
  grind

theorem cast_lt {a b : Int} (h : a < b) : (a : R) < (b : R) := by
  have := cast_le (R := R) (show a + 1 ≤ b by omega)
  have := OrderedRing.zero_lt_one (R := R)
  grind

theorem cast_inj {a b : Int} (h : (a : R) = (b : R)) : a = b := by
  apply Classical.byContradiction; intro hne
  rcases Int.lt_or_gt_of_ne hne with h' | h'
  · have := cast_lt (R := R) h'; grind
  · have := cast_lt (R := R) h'; grind

/-- `rat q` is `n / d` whenever `q·d = n`. -/
theorem rat_eq {q : Rat} {n d : Int} (hd : d ≠ 0) (h : q * d = n) : rat q = (n : R) / (d : R) := by
  have hq : q * (q.den : Int) = q.num := mul_den q
  have : (q.num * d : Int) = n * q.den := by
    have h1 : ((q.num * d : Int) : Rat) = ((n * (q.den : Int) : Int) : Rat) := by
      rw [Rat.intCast_mul, Rat.intCast_mul, ← hq, ← h]; grind
    exact Rat.intCast_inj.mp h1
  have e := congrArg (fun z : Int => (z : R)) this
  simp only [Ring.intCast_mul] at e
  have := cast_ne_zero (R := R) hd
  have := den_ne_zero (R := R) q
  unfold rat
  grind

theorem rat_ofInt (n : Int) : rat (n : Rat) = (n : R) := by
  rw [rat_eq (n := n) (d := 1) (by decide) (by grind)]; grind

theorem rat_add (a b : Rat) : rat (a + b) = (rat a + rat b : R) := by
  have ha : a * (a.den : Int) = a.num := mul_den a
  have hb : b * (b.den : Int) = b.num := mul_den b
  have hd : (a.den * b.den : Int) ≠ 0 := by
    have := a.den_pos; have := b.den_pos
    exact Int.mul_ne_zero (by omega) (by omega)
  rw [rat_eq (n := a.num * b.den + b.num * a.den) hd (by simp only [Rat.intCast_mul, Rat.intCast_add]; grind)]
  have := den_ne_zero (R := R) a; have := den_ne_zero (R := R) b
  unfold rat; simp only [Ring.intCast_mul, Ring.intCast_add]; grind

theorem rat_mul (a b : Rat) : rat (a * b) = (rat a * rat b : R) := by
  have ha : a * (a.den : Int) = a.num := mul_den a
  have hb : b * (b.den : Int) = b.num := mul_den b
  have hd : (a.den * b.den : Int) ≠ 0 := by
    have := a.den_pos; have := b.den_pos
    exact Int.mul_ne_zero (by omega) (by omega)
  rw [rat_eq (n := a.num * b.num) hd (by simp only [Rat.intCast_mul]; grind)]
  have := den_ne_zero (R := R) a; have := den_ne_zero (R := R) b
  unfold rat; simp only [Ring.intCast_mul]; grind

theorem rat_zero : rat (0 : Rat) = (0 : R) := by
  have := rat_ofInt (R := R) 0
  rw [Rat.intCast_zero, Ring.intCast_zero] at this; exact this

theorem rat_neg (a : Rat) : rat (-a) = (-rat a : R) := by
  have := rat_add (R := R) a (-a)
  rw [Rat.add_neg_cancel, rat_zero] at this
  grind

theorem rat_pos {a : Rat} (h : 0 < a) : (0 : R) < rat a := by
  have hn : 0 < a.num := by have := (Rat.lt_iff 0 a).mp h; simp at this; omega
  have h1 := cast_lt (R := R) hn
  have h2 := cast_lt (R := R) (show (0 : Int) < a.den by have := a.den_pos; omega)
  rw [Ring.intCast_zero] at h1 h2
  have hne : ((a.den : Int) : R) ≠ 0 := den_ne_zero a
  have hinv : (0 : R) < (((a.den : Int) : R))⁻¹ := by
    apply Classical.byContradiction; intro hc
    have h3 : (((a.den : Int) : R))⁻¹ ≤ 0 := by grind
    have := OrderedRing.mul_nonpos_of_nonneg_of_nonpos (Std.le_of_lt h2) h3
    rw [Field.mul_inv_cancel hne] at this
    have := OrderedRing.zero_lt_one (R := R); grind
  unfold rat
  rw [Field.div_eq_mul_inv]
  exact OrderedRing.mul_pos h1 hinv

theorem rat_lt {a b : Rat} (h : a < b) : (rat a : R) < rat b := by
  have := rat_pos (R := R) (show 0 < b - a by grind)
  rw [Rat.sub_eq_add_neg, rat_add, rat_neg] at this
  grind

theorem rat_le {a b : Rat} (h : a ≤ b) : (rat a : R) ≤ rat b := by
  by_cases h' : a = b
  · subst h'; exact Std.le_refl _
  · exact Std.le_of_lt (rat_lt (by grind))

theorem rat_inj {a b : Rat} (h : (rat a : R) = rat b) : a = b := by
  apply Classical.byContradiction; intro hne
  by_cases h' : a < b
  · have := rat_lt (R := R) h'; grind
  · have := rat_lt (R := R) (show b < a by grind); grind

end Vik.Real
