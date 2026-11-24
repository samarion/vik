import Vik.Cert.Inputs

/-!
# Shapes of lowered formulas

The lowering turns one SMT-LIB operation into a few lowered nodes: a chain of
comparisons into a conjunction of pairs, a `distinct` on integers into
disjunctions of strict bounds, `a < b` on integers into `a + 1 ≤ b`. A shape
describes those nodes, its leaves nodes already lowered; `fits` tells whether
a lowered node has a shape, and `fits_sound` that it then takes the value the
shape describes.
-/

set_option linter.unusedSectionVars false

namespace Vik.Low

open Lean.Grind Vik.Real

inductive Shape where
  /-- Node `t` itself. -/
  | same (t : Nat)
  /-- Node `t`, of sort `Bool`, as a formula or as a term. -/
  | bool (t : Nat)
  /-- A linear combination of nodes and a constant. -/
  | num (f : Lia.Form) (c : Int)
  | const (k : Nat)
  | app (f : Shape) (args : List Shape)
  | tt
  | ff
  | not (a : Shape)
  | and (as : List Shape)
  | or (as : List Shape)
  | implies (a b : Shape)
  | iff (a b : Shape)
  | ite (c a b : Shape)
  | eq (a b : Shape)
  | le (a b : Shape)
  | lt (a b : Shape)
  deriving Repr

variable {R U : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R]
  [OrderedRing R] [IsCharP R 0]

attribute [local instance low] Lean.Grind.Ring.intCast

section
variable (I : Interp R U) (ρ : Nat → Val R U)

open Classical in
mutual
/-- The value a shape describes, its leaves taking their values in `ρ`. -/
noncomputable def Shape.ev : Shape → Val R U
  | .same t => ρ t
  | .bool t => .bool (ρ t).truth
  | .num f c => .num (Lia.eval (fun u => (ρ u).toR) f + (c : R))
  | .const k => I.const k
  | .app f args => I.app f.ev (Shape.evs args)
  | .tt => .bool true
  | .ff => .bool false
  | .not a => .bool !a.ev.truth
  | .and as => .bool (Shape.allTrue as)
  | .or as => .bool (Shape.anyTrue as)
  | .implies a b => .bool (!a.ev.truth || b.ev.truth)
  | .iff a b => .bool (a.ev.truth == b.ev.truth)
  | .ite c a b => .bool (if c.ev.truth then a.ev.truth else b.ev.truth)
  | .eq a b => .bool (decide (a.ev = b.ev))
  | .le a b => .bool (decide (a.ev.toR ≤ b.ev.toR))
  | .lt a b => .bool (decide (a.ev.toR < b.ev.toR))

noncomputable def Shape.evs : List Shape → List (Val R U)
  | [] => []
  | s :: ss => s.ev :: Shape.evs ss

noncomputable def Shape.allTrue : List Shape → Bool
  | [] => true
  | s :: ss => s.ev.truth && Shape.allTrue ss

noncomputable def Shape.anyTrue : List Shape → Bool
  | [] => false
  | s :: ss => s.ev.truth || Shape.anyTrue ss
end

theorem Shape.evs_eq : ∀ ss : List Shape, Shape.evs I ρ ss = ss.map (Shape.ev I ρ)
  | [] => rfl
  | s :: ss => by simp only [Shape.evs, List.map_cons, Shape.evs_eq ss]

theorem Shape.allTrue_eq : ∀ ss : List Shape, Shape.allTrue I ρ ss = ss.all (fun s => (s.ev I ρ).truth)
  | [] => rfl
  | s :: ss => by simp only [Shape.allTrue, List.all_cons, Shape.allTrue_eq ss]

theorem Shape.anyTrue_eq : ∀ ss : List Shape, Shape.anyTrue I ρ ss = ss.any (fun s => (s.ev I ρ).truth)
  | [] => rfl
  | s :: ss => by simp only [Shape.anyTrue, List.any_cons, Shape.anyTrue_eq ss]

end

section
variable (sig : Sig) (nodes : List Node) (sortOf : List Nat)

mutual
/-- Whether node `j` has shape `s`. -/
def fits (j : Nat) : Shape → Bool
  | .same t => j == t
  | .bool t =>
    (j == t && sig.is ((Tab.at sortOf t).getD 0) .bool) || Tab.at nodes j == some (.bterm t) || Tab.at nodes j == some (.pred t)
  | .num f c =>
    let (g, d) := lin nodes j
    canon (g ++ Lia.neg f) == [] && d == c &&
      (sig.numeric ((Tab.at sortOf j).getD 0) ||
        match Tab.at nodes j with
        | some (.num _) | some (.linear _ _) => true
        | _ => false)
  | .const k => Tab.at nodes j == some (.const k)
  | .app f args =>
    match Tab.at nodes j with
    | some (.app g xs) => fits g f && fitsAll xs args
    | _ => false
  | .tt => Tab.at nodes j == some .tt
  | .ff => Tab.at nodes j == some .ff
  | .not a =>
    match Tab.at nodes j with
    | some (.not x) => fits x a
    | _ => false
  | .and as =>
    match Tab.at nodes j with
    | some (.and xs) => fitsAll xs as
    | _ => false
  | .or as =>
    match Tab.at nodes j with
    | some (.or xs) => fitsAll xs as
    | _ => false
  | .implies a b =>
    match Tab.at nodes j with
    | some (.implies x y) => fits x a && fits y b
    | _ => false
  | .iff a b =>
    match Tab.at nodes j with
    | some (.iff x y) => fits x a && fits y b
    | _ => false
  | .ite c a b =>
    match Tab.at nodes j with
    | some (.ite z x y) => fits z c && fits x a && fits y b
    | _ => false
  | .eq a b =>
    match Tab.at nodes j with
    | some (.eq x y) => fits x a && fits y b
    | _ => false
  | .le a b =>
    match Tab.at nodes j with
    | some (.le x y) => fits x a && fits y b
    | _ => false
  | .lt a b =>
    match Tab.at nodes j with
    | some (.lt x y) => fits x a && fits y b
    | _ => false

def fitsAll : List Nat → List Shape → Bool
  | [], [] => true
  | x :: xs, s :: ss => fits x s && fitsAll xs ss
  | _, _ => false
end

end

theorem all_as_map {α : Type} (l : List α) (f : α → Bool) : l.all f = (l.map f).all id := by
  simp [List.all_map]

theorem any_as_map {α : Type} (l : List α) (f : α → Bool) : l.any f = (l.map f).any id := by
  simp [List.any_map]

theorem truth_bool (b : Bool) : (Val.bool b : Val R U).truth = b := by
  cases b <;> simp [Val.truth]

section
variable {sig : Sig} {bv : List (Nat × Nat)} {M : Model R U} (hM : M.Sound sig bv) {nodes : List Node}
  {sortOf : List Nat} (hw : wellFormed nodes = true) (ht : typed sig nodes sortOf = true)
  (hrng : ∀ i < nodes.length, inRange bv (sortOf[i]?.getD 0) (val M.toInterp nodes i))
include hM hw ht hrng

theorem fits_node_lt {j : Nat} {n : Node} (h : nodes[j]? = some n) : j < nodes.length := by
  rcases Nat.lt_or_ge j nodes.length with h' | h'
  · exact h'
  · rw [List.getElem?_eq_none h'] at h; cases h

theorem fits_child_lt {j : Nat} {n : Node} (h : nodes[j]? = some n) : ∀ c ∈ n.children, c < j := by
  have := List.all_eq_true.mp hw j (List.mem_range.mpr (fits_node_lt hM hw ht hrng h))
  rw [Tab.at_eq, h] at this; simpa using this

theorem bool_of_sort {t : Nat} (ht' : t < nodes.length) (hb : sig.is (sortOf[t]?.getD 0) .bool = true) :
    ∃ b, val M.toInterp nodes t = .bool b := by
  have := val_dom hM hw ht hrng t ht'
  simp only [Sig.is, beq_iff_eq] at hb
  exact (hM.bool _ _ hb).mp this

/-- A node with a shape takes the value the shape describes, its leaves at
    their values. -/
theorem fits_sound : ∀ j, j < nodes.length → ∀ s, fits sig nodes sortOf j s = true →
    val M.toInterp nodes j = s.ev M.toInterp (val M.toInterp nodes) := by
  intro j
  induction j using Nat.strongRecOn with
  | ind j ih =>
  intro hj s hs
  -- the lists of children
  have hall : ∀ xs ss, (∀ x ∈ xs, x < j) → fitsAll sig nodes sortOf xs ss = true →
      xs.map (val M.toInterp nodes) = Shape.evs M.toInterp (val M.toInterp nodes) ss := by
    intro xs
    induction xs with
    | nil => intro ss _ h; cases ss <;> simp_all [fitsAll, Shape.evs]
    | cons x xs ihx =>
      intro ss hlt h
      cases ss with
      | nil => simp [fitsAll] at h
      | cons s ss =>
        simp only [fitsAll, Bool.and_eq_true] at h
        have hx := hlt x (by simp)
        simp only [List.map_cons, Shape.evs]
        rw [ih x hx (by omega) s h.1, ihx ss (fun y m => hlt y (by simp [m])) h.2]
  have truths : ∀ xs ss, (∀ x ∈ xs, x < j) → fitsAll sig nodes sortOf xs ss = true →
      xs.map (fun x => (val M.toInterp nodes x).truth) = ss.map (fun s => (s.ev M.toInterp (val M.toInterp nodes)).truth) := by
    intro xs ss hlt h
    have := hall xs ss hlt h
    rw [Shape.evs_eq] at this
    have := congrArg (List.map Val.truth) this
    simpa [List.map_map] using this
  have one : ∀ {x : Nat} {n : Node}, nodes[j]? = some n → x ∈ n.children → ∀ s, fits sig nodes sortOf x s = true →
      val M.toInterp nodes x = s.ev M.toInterp (val M.toInterp nodes) := by
    intro x n hn hx s h
    have := fits_child_lt hM hw ht hrng hn x hx
    exact ih x this (by omega) s h
  cases s with
  | same t => simp only [Tab.at_eq, fits, beq_iff_eq] at hs; subst hs; rfl
  | bool t =>
    simp only [Tab.at_eq, fits, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hs
    rcases hs with (⟨rfl, hb⟩ | hb) | hb
    · obtain ⟨b, hb'⟩ := bool_of_sort hM hw ht hrng hj hb
      show _ = Val.bool _
      rw [hb', truth_bool (R := R) (U := U)]
    · rw [val_bterm hw hb]; rfl
    · have := val_node (I := M.toInterp) hw hb
      simp only [val] at this ⊢; rw [this]; rfl
  | num f c =>
    simp only [Tab.at_eq, fits, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hs
    obtain ⟨⟨hc, hd⟩, hk⟩ := hs
    have e := congrArg (Lia.eval (nums M.toInterp nodes)) hc
    rw [eval_canon, eval_append, Lia.eval_neg] at e
    simp only [Lia.eval] at e
    have hl := lin_sound (I := M.toInterp) hw j
    have hnum : ∃ r, val M.toInterp nodes j = .num r := by
      rcases hk with hk | hk
      · exact dom_num_of_numeric hM hk (val_dom hM hw ht hrng j hj)
      · split at hk
        · rename_i v h; exact ⟨_, val_num hw h⟩
        · rename_i ts c' h; exact ⟨_, val_linear hw h⟩
        · cases hk
    obtain ⟨r, hr⟩ := hnum
    rw [hr] at hl ⊢
    simp only [Shape.ev]
    congr 1
    simp only [Val.toR] at hl
    rw [hl, ← hd]
    have : Lia.eval (nums M.toInterp nodes) f = Lia.eval (fun u => (val M.toInterp nodes u).toR) f := rfl
    grind
  | const k =>
    simp only [Tab.at_eq, fits, beq_iff_eq] at hs
    exact val_const hw hs
  | app f args =>
    simp only [Tab.at_eq, fits] at hs
    split at hs
    · rename_i g xs hn
      simp only [Bool.and_eq_true] at hs
      rw [val_app hw hn]
      simp only [Shape.ev]
      rw [one hn (by simp [Node.children]) f hs.1,
        hall xs args (fun x m => fits_child_lt hM hw ht hrng hn x (by simp [Node.children, m])) hs.2]
    · cases hs
  | tt => simp only [Tab.at_eq, fits, beq_iff_eq] at hs; have := val_node (I := M.toInterp) hw hs; simp only [val] at this ⊢; rw [this]; rfl
  | ff => simp only [Tab.at_eq, fits, beq_iff_eq] at hs; have := val_node (I := M.toInterp) hw hs; simp only [val] at this ⊢; rw [this]; rfl
  | not a =>
    simp only [Tab.at_eq, fits] at hs
    split at hs
    · rename_i x hn
      have := val_node (I := M.toInterp) hw hn; simp only [val] at this ⊢; rw [this]
      simp only [evalNode, Shape.ev]
      rw [← one hn (by simp [Node.children]) a hs]; rfl
    · cases hs
  | and as =>
    simp only [Tab.at_eq, fits] at hs
    split at hs
    · rename_i xs hn
      have := val_node (I := M.toInterp) hw hn; simp only [val] at this ⊢; rw [this]
      simp only [evalNode, Shape.ev, Shape.allTrue_eq]
      have := truths xs as (fun x m => fits_child_lt hM hw ht hrng hn x (by simpa [Node.children] using m)) hs
      congr 1
      rw [all_as_map xs, all_as_map as]; simp only [val] at this; rw [this]
    · cases hs
  | or as =>
    simp only [Tab.at_eq, fits] at hs
    split at hs
    · rename_i xs hn
      have := val_node (I := M.toInterp) hw hn; simp only [val] at this ⊢; rw [this]
      simp only [evalNode, Shape.ev, Shape.anyTrue_eq]
      have := truths xs as (fun x m => fits_child_lt hM hw ht hrng hn x (by simpa [Node.children] using m)) hs
      congr 1
      rw [any_as_map xs, any_as_map as]; simp only [val] at this; rw [this]
    · cases hs
  | implies a b | iff a b | eq a b | le a b | lt a b =>
    simp only [Tab.at_eq, fits] at hs
    split at hs
    · rename_i x y hn
      simp only [Bool.and_eq_true] at hs
      have := val_node (I := M.toInterp) hw hn; simp only [val] at this ⊢; rw [this]
      simp only [evalNode, Shape.ev]
      rw [← one hn (by simp [Node.children]) a hs.1, ← one hn (by simp [Node.children]) b hs.2]; rfl
    · cases hs
  | ite c a b =>
    simp only [Tab.at_eq, fits] at hs
    split at hs
    · rename_i z x y hn
      simp only [Bool.and_eq_true] at hs
      have := val_node (I := M.toInterp) hw hn; simp only [val] at this ⊢; rw [this]
      simp only [evalNode, Shape.ev]
      rw [← one hn (by simp [Node.children]) c hs.1.1, ← one hn (by simp [Node.children]) a hs.1.2,
        ← one hn (by simp [Node.children]) b hs.2]; rfl
    · cases hs

end

end Vik.Low
