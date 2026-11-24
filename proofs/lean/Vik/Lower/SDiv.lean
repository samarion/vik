import Vik.Lower.BitOps
import Vik.Signed

/-!
# Signed division by an unknown

`bvsdiv`, `bvsrem` and `bvsmod` by an unknown divide the magnitudes of their
operands (the `cases` tagged `abs`) with `udiv`, then give the quotient or the
remainder the sign SMT-LIB asks for, and answer a zero divisor as for a
constant. `Trace.sdivUnknownOk` checks that, and `sdivUnknownOk_sound` proves
that the lowered node takes the value of the operation.
-/

set_option linter.unusedSectionVars false

namespace Vik.Lower

open Lean.Grind Vik.Real Vik.Low Vik.Surf

variable {R U : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R]
  [OrderedRing R] [IsCharP R 0]

attribute [local instance low] Lean.Grind.Ring.intCast

/-- The magnitude of the value `X` of width `w`, as the lowering computes it. -/
def magV (w : Nat) (X : Int) : Int := if 2 ^ (w - 1) ≤ X then 2 ^ w - X else X

section generic
variable {V : Type} (I : Low.Interp R V) (ρ' : Nat → Val R V)

theorem shape_and2 (a b : Shape) :
    ((Shape.and [a, b]).ev I ρ').truth = ((a.ev I ρ').truth && (b.ev I ρ').truth) := by
  simp only [Shape.ev, Shape.allTrue, truth_bool, Bool.and_true]

theorem shape_not (a : Shape) : ((Shape.not a).ev I ρ').truth = !(a.ev I ρ').truth := by
  simp only [Shape.ev, truth_bool]

theorem shape_iff (a b : Shape) :
    ((Shape.iff a b).ev I ρ').truth = ((a.ev I ρ').truth == (b.ev I ρ').truth) := by
  simp only [Shape.ev, truth_bool]

theorem shape_le {a b : Shape} {A B : Int} (ha : (a.ev I ρ').toR = (A : R)) (hb : (b.ev I ρ').toR = (B : R)) :
    ((Shape.le a b).ev I ρ').truth = decide (A ≤ B) := by
  simp only [Shape.ev, truth_bool]
  rw [ha, hb]
  exact Bool.eq_iff_iff.mpr (by simp only [decide_eq_true_eq]; exact cast_le_iff (R := R))

theorem evf_negsym {x : Nat} {X : Int} (hx : ρ' x = .num (X : R)) (c : Int) :
    evf ρ' ([(x, -1)], c) = ((c - X : Int) : R) := by
  have := evf_sym ρ' hx (-1)
  have e : evf ρ' ([(x, -1)], c) = evf ρ' ([(x, ((-1 : Int) : Rat))], 0) + (c : R) := by
    unfold evf; simp only [Lia.eval]; grind
  rw [e, this, Ring.intCast_sub, Ring.intCast_mul, Ring.intCast_neg]; grind

end generic

theorem magV_eq {w : Nat} (x : BitVec w) (hw : 0 < w) :
    magV w (Vik.val x) = Vik.mag x.toInt ∧ 0 ≤ magV w (Vik.val x) ∧ magV w (Vik.val x) ≤ 2 ^ (w - 1) := by
  have := Vik.abs_lowering x hw
  unfold magV; exact ⟨this.1, this.1 ▸ this.2⟩

theorem magV_zero {w : Nat} (x : BitVec w) : magV w (Vik.val x) = 0 ↔ Vik.val x = 0 := by
  have := Vik.val_nonneg x; have := Vik.val_lt x; have := two_pow_pos (w - 1)
  unfold magV; split <;> omega

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

include hwP htP hG hML hrng in
/-- The magnitude of `t`. -/
theorem absOk_sound {t w x : Nat} {X : BitVec w} (h : tr.absOk SP P t w x = true)
    (ht : ρ t = .num ((Vik.val X : Int) : R)) : ρ x = .num ((magV w (Vik.val X) : Int) : R) := by
  have lt : evf ρ (lin P.nodes t) = ((Vik.val X : Int) : R) := by
    have := lin_val hwP (tr := tr) (Ms := Ms) (SP := SP) t; rw [ht, toR_num] at this; exact this.symm
  unfold Trace.absOk at h
  try simp only [Tab.at_eq] at h
  split at h
  · rename_i c th el lo hi hs
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨hc, hth⟩, hel⟩ := h
    have args := (symAt_args hG hs).2
    have eth : evf ρ (Lia.neg (lin P.nodes t).1, -(lin P.nodes t).2 + 2 ^ w) = ((2 ^ w - Vik.val X : Int) : R) := by
      have := evf_shift ρ (Lia.neg (lin P.nodes t).1, -(lin P.nodes t).2) (2 ^ w)
      rw [evf_neg, lt] at this
      exact this.trans (by rw [Ring.intCast_sub]; grind)
    rw [sym_val hwP hG hs]
    simp only [Rule.ival]
    rw [fits_sound hML hwP htP hrng c (args c (by simp [Rule.args])) _ hc, negS_int MI ρ hwP rfl ht,
      fits_num hwP htP hML hrng hth (args th (by simp [Rule.args])) eth,
      fits_num hwP htP hML hrng hel (args el (by simp [Rule.args])) lt]
    simp only [intOf_num, decide_eq_true_eq, magV]
  · cases h

include hwP htP hG hML hrng in
/-- The `udiv` of the magnitudes. -/
theorem magDivOk_sound {ta tb w k j : Nat} {x y : BitVec w} (h : tr.magDivOk SP P ta tb w k j = true)
    (ea : ρ ta = .num ((Vik.val x : Int) : R)) (eb : ρ tb = .num ((Vik.val y : Int) : R)) :
    ρ k = .num (((if j = 0 then (if magV w (Vik.val y) = 0 then 2 ^ w - 1 else magV w (Vik.val x) / magV w (Vik.val y))
      else (if magV w (Vik.val y) = 0 then magV w (Vik.val x) else magV w (Vik.val x) % magV w (Vik.val y))) % 2 ^ w
        : Int) : R) := by
  unfold Trace.magDivOk at h
  try simp only [Tab.at_eq] at h
  split at h
  · rename_i xa xb w' j' hs
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨rfl, rfl⟩, ha⟩, hb⟩ := h
    rw [sym_val hwP hG hs]
    have e1 := absOk_sound hwP htP hG hML hrng ha ea
    have e2 := absOk_sound hwP htP hG hML hrng hb eb
    cases j' <;> simp only [Rule.ival, e1, e2, intOf_num] <;> simp
  · cases h

include hwP htP hG hML hrng in
/-- The remainder of the sign of the dividend. -/
theorem sremOf_sound {ta tb w rm r : Nat} {x y : BitVec w} (h : tr.sremOf SP P ta tb w rm = some r)
    (ea : ρ ta = .num ((Vik.val x : Int) : R)) (eb : ρ tb = .num ((Vik.val y : Int) : R)) :
    let Rm := (if magV w (Vik.val y) = 0 then magV w (Vik.val x) else magV w (Vik.val x) % magV w (Vik.val y)) % 2 ^ w
    ρ r = .num ((Rm : Int) : R) ∧
      ρ rm = .num (((if 2 ^ (w - 1) ≤ Vik.val x ∧ 1 ≤ Rm then 2 ^ w - Rm else Rm : Int)) : R) := by
  intro Rm
  unfold Trace.sremOf at h
  try simp only [Tab.at_eq] at h
  split at h
  · rename_i c th r' lo hi hs
    split at h
    · rename_i hc
      simp only [Option.some.injEq] at h; subst r'
      simp only [Bool.and_eq_true] at hc
      obtain ⟨⟨hd, hcf⟩, hth⟩ := hc
      have er := magDivOk_sound hwP htP hG hML hrng hd ea eb
      simp only [Nat.one_ne_zero, if_false] at er
      refine ⟨er, ?_⟩
      have args := (symAt_args hG hs).2
      rw [sym_val hwP hG hs]
      simp only [Rule.ival]
      rw [fits_sound hML hwP htP hrng c (args c (by simp [Rule.args])) _ hcf, shape_and2,
        negS_int MI ρ hwP rfl ea, shape_le MI ρ (ev_num0 MI ρ 1) (ev_same_num MI ρ er),
        fits_num hwP htP hML hrng (f := ([(r, -1)], 2 ^ w)) hth (args th (by simp [Rule.args]))
          (evf_negsym ρ er _), er]
      simp only [intOf_num, Bool.and_eq_true, decide_eq_true_eq]
      rfl
    · cases h
  · cases h

include hwP htP hG hML hrng in
/-- `bvsdiv`, `bvsrem` and `bvsmod` of two unknowns. -/
theorem sdivUnknownOk_sound {op : BvBin} {w l ta tb : Nat} {x y : BitVec w}
    (hop : op = .sdiv ∨ op = .srem ∨ op = .smod) (h : tr.sdivUnknownOk SP P op w l ta tb = true)
    (ea : ρ ta = .num ((Vik.val x : Int) : R)) (eb : ρ tb = .num ((Vik.val y : Int) : R)) :
    ρ l = .num ((Vik.val (op.apply x y) : Int) : R) := by
  have la : evf ρ (lin P.nodes ta) = ((Vik.val x : Int) : R) := by
    have := lin_val hwP (tr := tr) (Ms := Ms) (SP := SP) ta; rw [ea, toR_num] at this; exact this.symm
  have lb : evf ρ (lin P.nodes tb) = ((Vik.val y : Int) : R) := by
    have := lin_val hwP (tr := tr) (Ms := Ms) (SP := SP) tb; rw [eb, toR_num] at this; exact this.symm
  have hx0 := Vik.val_nonneg x; have hx1 := Vik.val_lt x
  have hy0 := Vik.val_nonneg y; have hy1 := Vik.val_lt y
  unfold Trace.sdivUnknownOk at h
  try simp only [Tab.at_eq] at h
  split at h
  · rename_i c0 t0 e0 lo0 hi0 hs0
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hw0, hc0⟩, h⟩ := h
    have args0 := (symAt_args hG hs0).2
    obtain ⟨mx, mx0, mx1⟩ := magV_eq x hw0
    obtain ⟨my, my0, my1⟩ := magV_eq y hw0
    have hmy := magV_zero y
    have hp := two_pow_pred hw0
    rw [sym_val hwP hG hs0]
    simp only [Rule.ival]
    rw [fits_sound hML hwP htP hrng c0 (args0 c0 (by simp [Rule.args])) _ hc0,
      eqI_int MI ρ (ev_same_num MI ρ eb) (ev_num0 MI ρ 0)]
    rcases hop with rfl | rfl | rfl
    · simp only [Bool.and_eq_true] at h
      obtain ⟨h1, h2⟩ := h
      split at h1
      · rename_i cn tn en lon hin hsn
        simp only [Bool.and_eq_true] at h1
        obtain ⟨⟨hcn, htn⟩, hen⟩ := h1
        have argsn := (symAt_args hG hsn).2
        split at h2
        · rename_i cq tq q loq hiq hsq
          simp only [Bool.and_eq_true] at h2
          obtain ⟨⟨hq, hcq⟩, htq⟩ := h2
          have argsq := (symAt_args hG hsq).2
          have eq := magDivOk_sound hwP htP hG hML hrng hq ea eb
          simp only [if_true] at eq
          rw [sym_val hwP hG hsn, sym_val hwP hG hsq]
          simp only [Rule.ival]
          rw [fits_sound hML hwP htP hrng cn (argsn cn (by simp [Rule.args])) _ hcn, negS_int MI ρ hwP rfl ea,
            fits_num hwP htP hML hrng (f := ([], 1)) htn (argsn tn (by simp [Rule.args])) (evf_const ρ 1),
            fits_num hwP htP hML hrng (f := ([], 2 ^ w - 1)) hen (argsn en (by simp [Rule.args])) (evf_const ρ _),
            fits_sound hML hwP htP hrng cq (argsq cq (by simp [Rule.args])) _ hcq, shape_and2, shape_not,
            shape_iff, negS_int MI ρ hwP rfl ea, negS_int MI ρ hwP rfl eb,
            shape_le MI ρ (ev_num0 MI ρ 1) (ev_same_num MI ρ eq),
            fits_num hwP htP hML hrng (f := ([(q, -1)], 2 ^ w)) htq (argsq tq (by simp [Rule.args]))
              (evf_negsym ρ eq _), eq]
          simp only [intOf_num, BvBin.apply]
          rw [Vik.sdiv_lowering x y hw0]
          simp only [← mx, ← my]
          by_cases hy : Vik.val y = 0
          · simp [hy]
          · have hm : magV w (Vik.val y) ≠ 0 := fun e => hy (hmy.mp e)
            have hq0 : 0 ≤ magV w (Vik.val x) / magV w (Vik.val y) := Int.ediv_nonneg mx0 my0
            have hq1 : magV w (Vik.val x) / magV w (Vik.val y) ≤ magV w (Vik.val x) := Int.ediv_le_self _ mx0
            rw [if_neg hm, Int.emod_eq_of_lt hq0 (by omega)]
            by_cases hna : 2 ^ (w - 1) ≤ Vik.val x <;> by_cases hnb : 2 ^ (w - 1) ≤ Vik.val y <;>
              by_cases h1 : 1 ≤ magV w (Vik.val x) / magV w (Vik.val y) <;> simp [hna, hnb, h1, hy]
        · simp at h2
      · simp at h1
    · simp only [Bool.and_eq_true] at h
      obtain ⟨h1, h2⟩ := h
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp h2
      obtain ⟨er, erm⟩ := sremOf_sound hwP htP hG hML hrng hr ea eb
      rw [fits_num hwP htP hML hrng h1 (args0 t0 (by simp [Rule.args])) la, erm]
      simp only [intOf_num, BvBin.apply]
      rw [Vik.srem_lowering x y hw0]
      simp only [← mx, ← my]
      by_cases hy : Vik.val y = 0
      · simp [hy]
      · have hm : magV w (Vik.val y) ≠ 0 := fun e => hy (hmy.mp e)
        have := Int.emod_lt_of_pos (magV w (Vik.val x)) (show 0 < magV w (Vik.val y) by omega)
        rw [if_neg hm, Int.emod_eq_of_lt (Int.emod_nonneg _ hm) (by omega)]
        simp [hy]
    · simp only [Bool.and_eq_true] at h
      obtain ⟨h1, h2⟩ := h
      split at h2
      · rename_i cd td rm lod hid hsd
        split at h2
        · rename_i r v w' lo hi hr hsv
          simp only [Bool.and_eq_true, beq_iff_eq] at h2
          obtain ⟨⟨hw', hcd⟩, hv⟩ := h2
          subst w'
          obtain ⟨er, erm⟩ := sremOf_sound hwP htP hG hML hrng hr ea eb
          have argsd := (symAt_args hG hsd).2
          have argsv := (symAt_args hG hsv).2
          rw [fits_num hwP htP hML hrng h1 (args0 t0 (by simp [Rule.args])) la, sym_val hwP hG hsd]
          simp only [Rule.ival]
          rw [fits_sound hML hwP htP hrng cd (argsd cd (by simp [Rule.args])) _ hcd, shape_and2, shape_not,
            shape_iff, shape_not, negS_int MI ρ hwP rfl ea, negS_int MI ρ hwP rfl eb,
            eqI_int MI ρ (ev_same_num MI ρ er) (ev_num0 MI ρ 0), sym_val hwP hG hsv, erm]
          simp only [Rule.ival]
          rw [fits_num hwP htP hML hrng (f := ([(rm, 1)] ++ (lin P.nodes tb).1, 0 + (lin P.nodes tb).2)) hv
            (argsv v (by simp [Rule.args]))
            (by have := evf_add ρ ([(rm, 1)], 0) (lin P.nodes tb)
                rw [evf_sym1 ρ erm, lb] at this
                exact this.trans (Ring.intCast_add _ _).symm)]
          simp only [intOf_num, BvBin.apply]
          rw [Vik.smod_lowering x y hw0]
          simp only [← mx, ← my]
          by_cases hy : Vik.val y = 0
          · simp [hy]
          · have hm : magV w (Vik.val y) ≠ 0 := fun e => hy (hmy.mp e)
            have := Int.emod_lt_of_pos (magV w (Vik.val x)) (show 0 < magV w (Vik.val y) by omega)
            rw [if_neg hm, Int.emod_eq_of_lt (Int.emod_nonneg _ hm) (by omega)]
            by_cases hna : 2 ^ (w - 1) ≤ Vik.val x <;> by_cases hnb : 2 ^ (w - 1) ≤ Vik.val y <;>
              by_cases h1 : 1 ≤ magV w (Vik.val x) % magV w (Vik.val y) <;>
              by_cases h0 : magV w (Vik.val x) % magV w (Vik.val y) = 0 <;> simp [hna, hnb, h1, h0, hy]
        · simp at h2
      · simp at h2
  · cases h

end

end Vik.Lower
