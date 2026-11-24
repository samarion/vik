import Vik.Lowered

/-!
# Simplified inputs

Vik simplifies its assertions before solving them (`vik/Simplifier.scala`): in
a conjunction `c = t ∧ φ` in a positive position, it eliminates `c`,
replacing the conjunction by `φ[t/c]`. The simplified formula holds in every
model of the original one, which is all a refutation needs.

`weaker` checks that a formula `s` is such a simplification of a formula
`o`, both nodes of a table: it walks the two in parallel through the positive
positions, and at each conjunction of `o` that the hints name, adds the
equalities it eliminated, each oriented from its constant, to those that
hold. Elsewhere, `s` must have the value of `o` given those equalities
(`eqv`): the same node, what an equality replaces it by, or a node of the same
kind whose children have the same values. The equalities only ever lead from
a constant to a term without it, so `eqv` always ends; its fuel only bounds
the proof.
-/

set_option linter.unusedSectionVars false

namespace Vik.Low

open Lean.Grind

/-- A node with its children left out. -/
def Node.skel : Node → Node
  | .const n => .const n
  | .app _ args => .app 0 (args.map fun _ => 0)
  | .num v => .num v
  | .linear ts c => .linear (ts.map fun p => (p.1, 0)) c
  | .bterm _ => .bterm 0
  | .tt => .tt
  | .ff => .ff
  | .not _ => .not 0
  | .and as => .and (as.map fun _ => 0)
  | .or as => .or (as.map fun _ => 0)
  | .implies _ _ => .implies 0 0
  | .iff _ _ => .iff 0 0
  | .ite _ _ _ => .ite 0 0 0
  | .eq _ _ => .eq 0 0
  | .pred _ => .pred 0
  | .le _ _ => .le 0 0
  | .lt _ _ => .lt 0 0

/-- Whether `r` relates the lists pairwise. -/
def allPairs (r : Nat → Nat → Bool) : List Nat → List Nat → Bool
  | [], [] => true
  | a :: as, b :: bs => r a b && allPairs r as bs
  | _, _ => false

/-- Whether nodes `a` and `b` take the same value in every model where the
    two sides of each pair of `E` do, within `fuel` steps: `a` may be replaced
    by the right side of a pair of which it is the left side. -/
def eqv (nodes : List Node) (E : List (Nat × Nat)) : Nat → Nat → Nat → Bool
  | 0, a, b => a == b
  | k + 1, a, b =>
    a == b ||
      E.any (fun p => p.1 == a && eqv nodes E k p.2 b) ||
      match Tab.at nodes a, Tab.at nodes b with
      | some na, some nb => na.skel == nb.skel && allPairs (eqv nodes E k) na.children nb.children
      | _, _ => false

/-- The equalities among the conjuncts `os` at the positions of `elim`, from
    the left side when `elim` says `true`, from the right one otherwise. -/
def eliminated (nodes : List Node) (os : List Nat) (elim : List (Nat × Bool)) : List (Nat × Nat) :=
  elim.filterMap fun (i, left) =>
    match os[i]? with
    | some o =>
      match Tab.at nodes o with
      | some (.eq x y) => some (if left then (x, y) else (y, x))
      | _ => none
    | none => none

/-- The conjuncts of `os` outside the positions of `elim`. -/
def kept (os : List Nat) (elim : List (Nat × Bool)) : List Nat :=
  (os.zipIdx.filter fun p => !elim.any (·.1 == p.2)).map (·.1)

/-- Whether formula `s` holds in every model where formula `o` and the pairs
    of `E` do, `s` the simplification of `o` that eliminates, at each
    conjunction `a` in a positive position, the conjuncts at the positions
    `H` gives `a`, within `d` levels. -/
def weaker (nodes : List Node) (H : List (Nat × List (Nat × Bool))) (fuel : Nat) :
    Nat → List (Nat × Nat) → Nat → Nat → Bool
  | 0, _, _, _ => false
  | d + 1, E, o, s =>
    eqv nodes E fuel o s ||
      match Tab.at nodes o, Tab.at nodes s with
      | some (.or os), some (.or ss) => allPairs (weaker nodes H fuel d E) os ss
      | some (.implies a b), some (.implies a' b') => eqv nodes E fuel a a' && weaker nodes H fuel d E b b'
      | some (.ite c a b), some (.ite c' a' b') =>
        eqv nodes E fuel c c' && weaker nodes H fuel d E a a' && weaker nodes H fuel d E b b'
      | some (.and os), sn =>
        let elim := (H.lookup o).getD []
        let E' := E ++ eliminated nodes os elim
        match kept os elim with
        | [] => sn == some .tt
        | [x] => weaker nodes H fuel d E' x s
        | xs =>
          match sn with
          | some (.and ss) => allPairs (weaker nodes H fuel d E') xs ss
          | _ => false
      | _, _ => false

/-- Whether formula `s` is a simplification of formula `o` by the hints `H`. -/
def simplifies (nodes : List Node) (H : List (Nat × List (Nat × Bool))) (o s : Nat) : Bool :=
  weaker nodes H ((H.foldl (fun n h => n + h.2.length) 0 + 1) * (nodes.length + 1)) (nodes.length + 1) [] o s

variable {R U : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R]
  [OrderedRing R] [IsCharP R 0]

theorem allPairs_forall2 {r : Nat → Nat → Bool} {p : Nat → Nat → Prop} (h : ∀ a b, r a b = true → p a b) :
    ∀ {as bs : List Nat}, allPairs r as bs = true → Forall2 p as bs
  | [], [], _ => trivial
  | _ :: _, _ :: _, e => by
    simp only [allPairs, Bool.and_eq_true] at e
    exact ⟨h _ _ e.1, allPairs_forall2 h e.2⟩
  | [], _ :: _, e | _ :: _, [], e => by simp [allPairs] at e

theorem forall2_map_eq {g : Nat → Val R U} :
    ∀ {as bs : List Nat}, Forall2 (fun x y => g x = g y) as bs → as.map g = bs.map g
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp only [List.map_cons, h.1, forall2_map_eq h.2]
  | [], _ :: _, h | _ :: _, [], h => h.elim

theorem linSum_eq {vals : List (Val R U)} :
    ∀ {ts ts' : List (Int × Nat)}, ts.map (fun p => (p.1, 0)) = ts'.map (fun p => (p.1, 0)) →
      Forall2 (fun x y => get vals x = get vals y) (ts.map (·.2)) (ts'.map (·.2)) →
      linSum vals ts = linSum vals ts'
  | [], [], _, _ => rfl
  | (a, t) :: ts, (a', t') :: ts', hs, hk => by
    simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq, and_true] at hs
    simp only [List.map_cons, Forall2] at hk
    simp only [linSum, hs.1, hk.1, linSum_eq hs.2 hk.2]
  | [], _ :: _, hs, _ | _ :: _, [], hs, _ => by simp at hs

theorem all_map_eq {as bs : List Nat} {g : Nat → Val R U} (h : as.map g = bs.map g) (p : Val R U → Bool) :
    as.all (fun a => p (g a)) = bs.all (fun a => p (g a)) := by
  have := congrArg (fun l => l.all p) h
  simpa [List.all_map] using this

theorem any_map_eq {as bs : List Nat} {g : Nat → Val R U} (h : as.map g = bs.map g) (p : Val R U → Bool) :
    as.any (fun a => p (g a)) = bs.any (fun a => p (g a)) := by
  have := congrArg (fun l => l.any p) h
  simpa [List.any_map] using this

/-- Nodes of the same kind whose children have the same values have the same
    value. -/
theorem evalNode_skel (I : Interp R U) (vals : List (Val R U)) {na nb : Node} (hs : na.skel = nb.skel)
    (hk : Forall2 (fun x y => get vals x = get vals y) na.children nb.children) :
    evalNode I vals na = evalNode I vals nb := by
  cases na <;> cases nb <;> simp only [Node.skel, reduceCtorEq, Node.const.injEq, Node.num.injEq,
    Node.app.injEq, Node.linear.injEq, Node.and.injEq, Node.or.injEq] at hs <;>
    simp only [Node.children, Forall2, and_true] at hk
  case const.const => rw [hs]
  case num.num => rw [hs]
  case app.app f as g bs =>
    simp only [evalNode, hk.1, forall2_map_eq hk.2]
  case linear.linear ts c ts' c' =>
    simp only [evalNode, hs.2, linSum_eq hs.1 hk]
  case and.and as bs => simp only [evalNode, all_map_eq (forall2_map_eq hk) Val.truth]
  case or.or as bs => simp only [evalNode, any_map_eq (forall2_map_eq hk) Val.truth]
  all_goals first
    | rfl
    | (simp only [evalNode, hk.1, hk.2.1, hk.2.2]; done)
    | (simp only [evalNode, hk.1, hk.2]; done)
    | (simp only [evalNode, hk]; done)
    | (simp only [evalNode]; rw [hk.1, hk.2])

variable {I : Interp R U} {nodes : List Node} (hw : wellFormed nodes = true)
include hw

theorem eqv_sound {E : List (Nat × Nat)} (hE : ∀ p ∈ E, val I nodes p.1 = val I nodes p.2) :
    ∀ {k a b : Nat}, eqv nodes E k a b = true → val I nodes a = val I nodes b
  | 0, a, b, h => by simp only [eqv, beq_iff_eq] at h; rw [h]
  | k + 1, a, b, h => by
    simp only [eqv, Bool.or_eq_true, beq_iff_eq, List.any_eq_true, Bool.and_eq_true] at h
    rcases h with (h | ⟨p, hp, e, h⟩) | h
    · rw [h]
    · rw [← e, hE p hp, eqv_sound hE h]
    · split at h
      · rename_i na nb ha hb
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        rw [Tab.at_eq] at ha hb
        rw [val_node hw ha, val_node hw hb]
        exact evalNode_skel I _ h.1 (allPairs_forall2 (fun x y e => eqv_sound hE e) h.2)
      · cases h

theorem holds_of_eqv {E : List (Nat × Nat)} (hE : ∀ p ∈ E, val I nodes p.1 = val I nodes p.2) {k a b : Nat}
    (h : eqv nodes E k a b = true) (ha : holds I nodes a) : holds I nodes b := by
  unfold holds at *; rw [← eqv_sound hw hE h]; exact ha

theorem forall2_holds {r : Nat → Nat → Bool} (h : ∀ a b, r a b = true → holds I nodes a → holds I nodes b) :
    ∀ {as bs : List Nat}, allPairs r as bs = true → ∀ b ∈ bs, ∃ a ∈ as, (holds I nodes a → holds I nodes b)
  | [], [], _ => by simp
  | a :: as, b :: bs, e => by
    simp only [allPairs, Bool.and_eq_true] at e
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨a, by simp, h a c e.1⟩
    · obtain ⟨x, hx, hxc⟩ := forall2_holds h e.2 c hc
      exact ⟨x, by simp [hx], hxc⟩
  | [], _ :: _, e | _ :: _, [], e => by simp [allPairs] at e

theorem forall2_holds' {r : Nat → Nat → Bool} (h : ∀ a b, r a b = true → holds I nodes a → holds I nodes b) :
    ∀ {as bs : List Nat}, allPairs r as bs = true → ∀ a ∈ as, holds I nodes a → ∃ b ∈ bs, holds I nodes b
  | [], [], _ => by simp
  | a :: as, b :: bs, e => by
    simp only [allPairs, Bool.and_eq_true] at e
    intro c hc hh
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨b, by simp, h c b e.1 hh⟩
    · obtain ⟨x, hx, hxc⟩ := forall2_holds' h e.2 c hc hh
      exact ⟨x, by simp [hx], hxc⟩
  | [], _ :: _, e | _ :: _, [], e => by simp [allPairs] at e

theorem kept_sub {os : List Nat} {elim : List (Nat × Bool)} : ∀ x ∈ kept os elim, x ∈ os := by
  intro x hx
  simp only [kept, List.mem_map, List.mem_filter] at hx
  obtain ⟨⟨y, i⟩, ⟨hm, _⟩, rfl⟩ := hx
  exact List.fst_mem_of_mem_zipIdx hm

theorem eliminated_hold {os : List Nat} {elim : List (Nat × Bool)} (h : ∀ a ∈ os, holds I nodes a) :
    ∀ p ∈ eliminated nodes os elim, val I nodes p.1 = val I nodes p.2 := by
  intro p hp
  simp only [eliminated, List.mem_filterMap] at hp
  obtain ⟨⟨i, left⟩, _, hi⟩ := hp
  split at hi
  · rename_i o ho
    split at hi
    · rename_i x y hxy
      simp only [Option.some.injEq] at hi
      subst hi
      rw [Tab.at_eq] at hxy
      have e := (holds_eq hw hxy).mp (h o (List.mem_of_getElem? ho))
      cases left
      · exact e.symm
      · exact e
    · cases hi
  · cases hi

theorem weaker_sound {H : List (Nat × List (Nat × Bool))} {fuel : Nat} :
    ∀ {d : Nat} {E : List (Nat × Nat)} {o s : Nat}, (∀ p ∈ E, val I nodes p.1 = val I nodes p.2) →
      weaker nodes H fuel d E o s = true → holds I nodes o → holds I nodes s
  | 0, _, _, _, _, h, _ => by simp [weaker] at h
  | d + 1, E, o, s, hE, h, ho => by
    simp only [weaker, Bool.or_eq_true] at h
    rcases h with h | h
    · exact holds_of_eqv hw hE h ho
    · split at h
      · rename_i os ss hoN hsN
        rw [Tab.at_eq] at hoN hsN
        obtain ⟨a, ha, hh⟩ := (holds_or hw hoN).mp ho
        obtain ⟨b, hb, hbh⟩ := forall2_holds' hw (fun x y e => weaker_sound hE e) h a ha hh
        exact (holds_or hw hsN).mpr ⟨b, hb, hbh⟩
      · rename_i a b a' b' hoN hsN
        rw [Tab.at_eq] at hoN hsN
        simp only [Bool.and_eq_true] at h
        refine (holds_implies hw hsN).mpr fun ha' => ?_
        have ha : holds I nodes a := by
          unfold holds at *; rw [eqv_sound hw hE h.1]; exact ha'
        exact weaker_sound hE h.2 ((holds_implies hw hoN).mp ho ha)
      · rename_i c a b c' a' b' hoN hsN
        rw [Tab.at_eq] at hoN hsN
        simp only [Bool.and_eq_true] at h
        have hc : holds I nodes c ↔ holds I nodes c' := by unfold holds; rw [eqv_sound hw hE h.1.1]
        have hoi := (holds_ite hw hoN).mp ho
        refine (holds_ite hw hsN).mpr ?_
        classical
        by_cases e : holds I nodes c
        · rw [if_pos (hc.mp e)]; rw [if_pos e] at hoi; exact weaker_sound hE h.1.2 hoi
        · rw [if_neg (fun e' => e (hc.mpr e'))]; rw [if_neg e] at hoi; exact weaker_sound hE h.2 hoi
      · rename_i sn os hoN
        rw [Tab.at_eq] at hoN
        have hos := (holds_and hw hoN).mp ho
        have hE' : ∀ p ∈ E ++ eliminated nodes os ((H.lookup o).getD []), val I nodes p.1 = val I nodes p.2 := by
          intro p hp
          rcases List.mem_append.mp hp with hp | hp
          · exact hE p hp
          · exact eliminated_hold hw hos p hp
        have hk : ∀ x ∈ kept os ((H.lookup o).getD []), x ∈ os := kept_sub hw
        split at h
        · simp only [beq_iff_eq] at h
          rw [Tab.at_eq] at h
          exact holds_tt hw h
        · rename_i x hx
          exact weaker_sound hE' h (hos x (hk x (by rw [hx]; simp)))
        · split at h
          · rename_i ss hsN
            rw [Tab.at_eq] at hsN
            refine (holds_and hw hsN).mpr fun b hb => ?_
            obtain ⟨a, ha, hab⟩ := forall2_holds hw (fun x y e => weaker_sound hE' e) h b hb
            exact hab (hos a (hk a ha))
          · cases h
      · cases h

/-- A simplification holds in every model of its original. -/
theorem simplifies_sound {H : List (Nat × List (Nat × Bool))} {o s : Nat} (h : simplifies nodes H o s = true)
    (ho : holds I nodes o) : holds I nodes s :=
  weaker_sound hw (by simp) h ho

end Vik.Low
