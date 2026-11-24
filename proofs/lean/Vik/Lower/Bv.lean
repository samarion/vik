import Vik.Lower.Corr
import Vik.Bits

/-!
# Bit-vector operations and their lowering

A bit-vector of width `w` takes the integer it stands for, `ofBv x`, and its
lowering the same integer. Here, for each operation that lowers to a linear
term or a comparison of values, the shape `expect` gives it takes the value
of the operation (`Vik/Arith.lean`, `Vik/Bits.lean`).
-/

set_option linter.unusedSectionVars false

namespace Vik.Lower

open Lean.Grind Vik.Real Vik.Low Vik.Surf

variable {R U : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R]
  [OrderedRing R] [IsCharP R 0]

attribute [local instance low] Lean.Grind.Ring.intCast

theorem ofBv_num {w : Nat} (x : BitVec w) : (ofBv x : Val R U) = .num ((Vik.val x : Int) : R) := rfl

theorem bvOf_ofBv {w : Nat} (x : BitVec w) : bvOf w (ofBv x : Val R U) = x := by
  unfold bvOf
  rw [ofBv_num, intOf_num, ← Vik.val_inj, Vik.val_ofInt]
  have := Vik.val_range x; unfold Range at this
  exact Int.emod_eq_of_lt this.1 (by omega)

theorem dom_bv_iff {sig : SSig} {M : Surf.Model R U} (hM : M.Sound sig) {s w : Nat}
    (hs : sig.sorts[s]? = some (.bv w)) {v : Val R U} : M.dom s v ↔ ∃ x : BitVec w, v = ofBv x := by
  rw [hM.bv s w v hs]
  constructor
  · rintro ⟨k, rfl, h0, h1⟩
    refine ⟨BitVec.ofInt w k, ?_⟩
    rw [ofBv_num, Vik.val_ofInt, Int.emod_eq_of_lt h0 h1]
  · rintro ⟨x, rfl⟩
    exact ⟨Vik.val x, rfl, Vik.val_nonneg x, Vik.val_lt x⟩

theorem rotateLeft_of_mod {w k : Nat} (x : BitVec w) (h : k % w = 0) : x.rotateLeft k = x := by
  rw [← BitVec.rotateLeft_mod_eq_rotateLeft, h]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_rotateLeft, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt x.isLt]

theorem rotateRight_of_mod {w k : Nat} (x : BitVec w) (h : k % w = 0) : x.rotateRight k = x := by
  rw [← BitVec.rotateRight_mod_eq_rotateRight, h]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_rotateRight, Nat.shiftLeft_eq]

theorem val_extract_all {w i : Nat} (x : BitVec w) (hi : i + 1 = w) : Vik.val (x.extractLsb i 0) = Vik.val x := by
  simp only [Vik.val, BitVec.extractLsb_toNat, Nat.shiftRight_zero, Nat.sub_zero, hi, Nat.mod_eq_of_lt x.isLt]

theorem val_signExtend_zero {w : Nat} (x : BitVec w) : Vik.val (x.signExtend (w + 0)) = Vik.val x := by
  rw [signExtend_val]; split <;> simp

theorem alg_not (E M c : R) : -E + ((M : R) - 1 - c) = M - 1 - (E + c) := by grind

theorem repeatForm_eval (ρ : Nat → R) (w : Nat) (p : Lia.Form × Int) (X : Int)
    (hp : Lia.eval ρ p.1 + (p.2 : R) = (X : R)) :
    ∀ k, Lia.eval ρ (repeatForm w p k).1 + ((repeatForm w p k).2 : R) = (repeatSum w X k : R)
  | 0 => by simp only [repeatForm, repeatSum, Lia.eval, Ring.intCast_zero]; grind
  | k + 1 => by
    have ih := repeatForm_eval ρ w p X hp k
    simp only [repeatForm, repeatSum]
    rw [eval_append, Lia.eval_scale, Lia.rat_intCast, Ring.intCast_add, Ring.intCast_add, Ring.intCast_mul,
      Ring.intCast_mul, ← ih, ← hp]
    grind

section
variable {SP : SProblem} {P : Problem} {tr : Trace} {Ms : Surf.Model R U}
  (hM : Ms.Sound SP.sig) (hw : Surf.wellFormed SP.nodes = true) (ht : Surf.typed SP.sig SP.nodes SP.sortOf = true)

set_option quotPrecheck false in
local notation "ρ" => Low.val (lowModel SP P tr Ms).toInterp P.nodes
local notation "vs" => Surf.val Ms.toInterp SP.nodes
set_option quotPrecheck false in
local notation "MI" => (lowModel SP P tr Ms).toInterp

include hM hw ht

theorem v_bv {a w : Nat} (ha : a < SP.nodes.length) (hs : SP.sig.is (SP.sort a) (.bv w) = true) :
    ∃ x : BitVec w, vs a = ofBv x := by
  simp only [SSig.is, beq_iff_eq] at hs
  exact (dom_bv_iff hM hs).mp (dom_at hM hw ht ha)

theorem v_width {a w : Nat} (ha : a < SP.nodes.length) (hs : SP.width a = some w) :
    ∃ x : BitVec w, vs a = ofBv x :=
  v_bv hM hw ht ha (by simp only [SSig.is, beq_iff_eq]; exact sortWidth_eq.mp hs)

theorem v_arith {a : Nat} (ha : a < SP.nodes.length) (h : SP.isArith a = true) : ∃ r, vs a = .num r := by
  simp only [SProblem.isArith, Bool.or_eq_true] at h
  rcases h with h | h
  · exact v_num hM hw ht ha h
  · simp only [SProblem.isBv, Option.isSome_iff_exists] at h
    obtain ⟨w, hw'⟩ := h
    obtain ⟨x, hx⟩ := v_width hM hw ht ha hw'
    exact ⟨_, hx⟩

theorem v_intLike {a : Nat} (ha : a < SP.nodes.length) (h : SP.isIntLike a = true) :
    ∃ k : Int, vs a = .num (k : R) := by
  simp only [SProblem.isIntLike, Bool.or_eq_true] at h
  rcases h with h | h
  · exact v_int hM hw ht ha h
  · simp only [SProblem.isBv, Option.isSome_iff_exists] at h
    obtain ⟨w, hw'⟩ := h
    obtain ⟨x, hx⟩ := v_width hM hw ht ha hw'
    exact ⟨_, hx⟩

omit hM hw ht in
open Classical in
/-- `negative(t, w)`: the sign bit of the value. -/
theorem negS_ev (hwP : Low.wellFormed P.nodes = true) {l w : Nat} {x : BitVec w}
    (e : ρ (tr.at l) = enc (vs l)) (hx : vs l = ofBv x) :
    (negS P (tr.at l) w).ev MI ρ = .bool (decide (2 ^ (w - 1) ≤ Vik.val x)) := by
  unfold negS
  split
  · rename_i v hv
    have hval := Low.val_num (I := MI) hwP ((Tab.at_eq _ _).symm.trans hv)
    rw [e, hx, ofBv_num, enc_num] at hval
    have hv' : Vik.val x = v := (num_int_eq_iff (U := U ⊕ Nat)).mp hval
    rw [hv']
    split
    · rename_i hle; simp [Shape.ev, hle]
    · rename_i hle; simp [Shape.ev, hle]
  · simp only [Shape.ev, Lia.eval, e, hx, ofBv_num, enc_num, toR_num]
    congr 1
    have : (0 : R) + ((2 ^ (w - 1) : Int) : R) = ((2 ^ (w - 1) : Int) : R) := by grind
    rw [this]
    exact decide_eq_decide.mpr cast_le_iff

theorem bvlit_sound {i w v : Nat} {s : Shape} (hn : SP.nodes[i]? = some (.bvlit w v))
    (h : expect SP P tr i = some s) : s.ev MI ρ = enc (vs i) := by
  simp only [Tab.at_eq, expect, hn] at h
  split at h
  · rename_i hv
    cases h
    rw [Surf.val_node hw hn]
    simp only [Surf.evalNode, Shape.ev, Lia.eval, ofBv_num, enc_num]
    have : Vik.val (BitVec.ofNat w v) = v := by
      simp only [Vik.val, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]
    rw [this]
    congr 1; grind
  · cases h

theorem bvun_sound (hwP : Low.wellFormed P.nodes = true) {i w a : Nat} {op : BvUn} {s : Shape}
    (hn : SP.nodes[i]? = some (.bvun op w a)) (h : expect SP P tr i = some s)
    (ih : ∀ c < i, ρ (tr.at c) = enc (vs c)) : s.ev MI ρ = enc (vs i) := by
  have hai := children_lt hw hn a (by simp [SNode.children])
  have hal : a < SP.nodes.length := by have := lt_of_get hn; omega
  have hty := typed_at hM hw ht hn
  simp only [Tab.at_eq, Tab.at_eq, Surf.nodeTyped, Bool.and_eq_true] at hty
  obtain ⟨x, hx⟩ := v_bv hM hw ht hal hty.1
  have ea := ih a hai
  have hv := Surf.val_node (I := Ms.toInterp) hw hn
  simp only [Surf.evalNode, surf_get_values, hx, bvOf_ofBv] at hv
  rw [hv]
  have la := lin_ev hwP ea
  rw [hx, ofBv_num, toR_num] at la
  simp only [Tab.at_eq, expect, hn] at h
  cases op <;> simp only at h
  case neg => cases h
  case not =>
    cases h
    simp only [BvUn.apply, Shape.ev, ofBv_num, enc_num, Lia.eval_neg, not_val]
    congr 1
    simp only [BvUn.width]
    generalize (2 : Int) ^ w = M at *
    simp only [Ring.intCast_sub, Ring.intCast_one]
    rw [← la]
    exact alg_not (R := R) _ _ _
  case zeroExtend k =>
    cases h
    simp only [BvUn.apply, Shape.ev, ea, hx, ofBv_num, BvUn.width]
    rw [zeroExtend_val]
  case «repeat» k =>
    cases h
    simp only [BvUn.apply, Shape.ev, ofBv_num, enc_num, repeat_val]
    congr 1
    exact repeatForm_eval _ w _ _ la k
  case rotateLeft k =>
    split at h
    · rename_i hk; cases h
      simp only [BvUn.apply, Shape.ev, ea, hx, rotateLeft_of_mod x hk]
    · cases h
  case rotateRight k =>
    split at h
    · rename_i hk; cases h
      simp only [BvUn.apply, Shape.ev, ea, hx, rotateRight_of_mod x hk]
    · cases h
  case extract hi lo =>
    split at h
    · rename_i hk
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
      obtain ⟨rfl, hk⟩ := hk
      cases h
      simp only [BvUn.apply, Shape.ev, ea, hx, ofBv_num, val_extract_all x hk]
    · cases h
  case signExtend k =>
    split at h
    · rename_i hk; subst hk; cases h
      simp only [BvUn.apply, Shape.ev, ea, hx, ofBv_num, BvUn.width, val_signExtend_zero]
    · cases h

theorem concat_sound (hwP : Low.wellFormed P.nodes = true) {i wa wb a b : Nat} {s : Shape}
    (hn : SP.nodes[i]? = some (.concat wa wb a b)) (h : expect SP P tr i = some s)
    (ih : ∀ c < i, ρ (tr.at c) = enc (vs c)) : s.ev MI ρ = enc (vs i) := by
  have hai := children_lt hw hn a (by simp [SNode.children])
  have hbi := children_lt hw hn b (by simp [SNode.children])
  have hl := lt_of_get hn
  have hty := typed_at hM hw ht hn
  simp only [Tab.at_eq, Tab.at_eq, Surf.nodeTyped, Bool.and_eq_true] at hty
  obtain ⟨x, hx⟩ := v_bv hM hw ht (by omega) hty.1.1
  obtain ⟨y, hy⟩ := v_bv hM hw ht (by omega) hty.1.2
  have la := lin_ev hwP (ih a hai)
  have lb := lin_ev hwP (ih b hbi)
  rw [hx, ofBv_num, toR_num] at la
  rw [hy, ofBv_num, toR_num] at lb
  have hv := Surf.val_node (I := Ms.toInterp) hw hn
  simp only [Surf.evalNode, surf_get_values, hx, hy, bvOf_ofBv] at hv
  rw [hv]
  simp only [Tab.at_eq, expect, hn, Option.some.injEq] at h; subst h
  simp only [Shape.ev, ofBv_num, enc_num, concat_val]
  congr 1
  rw [eval_append, Lia.eval_scale, Lia.rat_intCast, Ring.intCast_add, Ring.intCast_add, Ring.intCast_mul,
    Ring.intCast_mul, ← la, ← lb]
  grind

theorem bv2int_sound {i w a : Nat} {sg : Bool} {s : Shape}
    (hn : SP.nodes[i]? = some (.bv2int sg w a)) (h : expect SP P tr i = some s)
    (ih : ∀ c < i, ρ (tr.at c) = enc (vs c)) : s.ev MI ρ = enc (vs i) := by
  have hai := children_lt hw hn a (by simp [SNode.children])
  have hl := lt_of_get hn
  have hty := typed_at hM hw ht hn
  simp only [Tab.at_eq, Tab.at_eq, Surf.nodeTyped, Bool.and_eq_true] at hty
  obtain ⟨x, hx⟩ := v_bv hM hw ht (by omega) hty.1
  cases sg with
  | true => simp only [Tab.at_eq, expect, hn] at h; cases h
  | false =>
    simp only [Tab.at_eq, expect, hn, Option.some.injEq] at h; subst h
    have hv := Surf.val_node (I := Ms.toInterp) hw hn
    simp only [Surf.evalNode, surf_get_values, hx, bvOf_ofBv, Bool.false_eq_true, if_false] at hv
    rw [hv]
    simp only [Shape.ev, ih a hai, hx, ofBv_num]
    rfl

open Classical in
theorem bvcmp_sound (hwP : Low.wellFormed P.nodes = true) {i w a b : Nat} {op : BvCmp} {s : Shape}
    (hn : SP.nodes[i]? = some (.bvcmp op w a b)) (h : expect SP P tr i = some s)
    (ih : ∀ c < i, ρ (tr.at c) = enc (vs c)) : s.ev MI ρ = enc (vs i) := by
  have hai := children_lt hw hn a (by simp [SNode.children])
  have hbi := children_lt hw hn b (by simp [SNode.children])
  have hl := lt_of_get hn
  have hty := typed_at hM hw ht hn
  simp only [Tab.at_eq, Tab.at_eq, Surf.nodeTyped, Bool.and_eq_true] at hty
  obtain ⟨x, hx⟩ := v_bv hM hw ht (by omega) hty.1.1
  obtain ⟨y, hy⟩ := v_bv hM hw ht (by omega) hty.1.2
  have ea := ih a hai
  have eb := ih b hbi
  have hv := Surf.val_node (I := Ms.toInterp) hw hn
  simp only [Surf.evalNode, surf_get_values, hx, hy, bvOf_ofBv] at hv
  rw [hv, enc_bool]
  simp only [Tab.at_eq, expect, hn] at h
  split at h
  · cases h
  · rename_i hw0
    simp only [Option.some.injEq] at h; subst h
    have hwpos : 0 < w := by omega
    have lt' : ∀ {l r : Nat} {u v : BitVec w}, ρ (tr.at l) = enc (vs l) → ρ (tr.at r) = enc (vs r) →
        vs l = ofBv u → vs r = ofBv v →
        (ltInt P tr l r).ev MI ρ = .bool (decide (Vik.val u < Vik.val v)) := by
      intro l r u v el er hu hv'
      rw [ltInt_ev hwP el er, hu, hv', ofBv_num, ofBv_num, toR_num, toR_num]
      exact congrArg Val.bool (decide_eq_decide.mpr cast_succ_le_iff)
    have le' : ∀ {l r : Nat} {u v : BitVec w}, ρ (tr.at l) = enc (vs l) → ρ (tr.at r) = enc (vs r) →
        vs l = ofBv u → vs r = ofBv v →
        (Shape.le (.same (tr.at l)) (.same (tr.at r))).ev MI ρ = .bool (decide (Vik.val u ≤ Vik.val v)) := by
      intro l r u v el er hu hv'
      rw [le_ev el er, hu, hv', ofBv_num, ofBv_num, toR_num, toR_num]
      exact congrArg Val.bool (decide_eq_decide.mpr cast_le_iff)
    have na := negS_ev hwP ea hx
    have nb := negS_ev hwP eb hy
    have sg : ∀ {l r : Nat} {u v : BitVec w} {us : Shape} {ub : Bool},
        (negS P (tr.at l) w).ev MI ρ = .bool (decide (2 ^ (w - 1) ≤ Vik.val u)) →
        (negS P (tr.at r) w).ev MI ρ = .bool (decide (2 ^ (w - 1) ≤ Vik.val v)) →
        us.ev MI ρ = .bool ub →
        (signedS P tr w l r us).ev MI ρ = .bool (decide ((2 ^ (w - 1) ≤ Vik.val u ∧ ¬2 ^ (w - 1) ≤ Vik.val v) ∨
          ((2 ^ (w - 1) ≤ Vik.val u ↔ 2 ^ (w - 1) ≤ Vik.val v) ∧ ub = true))) := by
      intro l r u v us ub hl hr hu
      simp only [signedS, Shape.ev, Shape.anyTrue, Shape.allTrue, hl, hr, hu, truth_bool]
      congr 1
      by_cases p : 2 ^ (w - 1) ≤ Vik.val u <;> by_cases q : 2 ^ (w - 1) ≤ Vik.val v <;> cases ub <;> simp [p, q]
    cases op <;> simp only [cmpS, BvCmp.apply]
    · rw [lt' ea eb hx hy]; congr 1; exact (bool_eq_decide (ult_iff x y)).symm
    · rw [le' ea eb hx hy]; congr 1; exact (bool_eq_decide (ule_iff x y)).symm
    · rw [lt' eb ea hy hx]; congr 1; exact (bool_eq_decide (ult_iff y x)).symm
    · rw [le' eb ea hy hx]; congr 1; exact (bool_eq_decide (ule_iff y x)).symm
    · rw [sg na nb (lt' ea eb hx hy)]; congr 1
      exact (bool_eq_decide ((slt_iff x y hwpos).trans (by simp))).symm
    · rw [sg na nb (le' ea eb hx hy)]; congr 1
      exact (bool_eq_decide ((sle_iff x y hwpos).trans (by simp))).symm
    · rw [sg nb na (lt' eb ea hy hx)]; congr 1
      exact (bool_eq_decide ((slt_iff y x hwpos).trans (by simp))).symm
    · rw [sg nb na (le' eb ea hy hx)]; congr 1
      exact (bool_eq_decide ((sle_iff y x hwpos).trans (by simp))).symm

end

end Vik.Lower
