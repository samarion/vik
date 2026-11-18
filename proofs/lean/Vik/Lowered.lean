import Vik.Cert.RatCast
import Vik.Tab

/-!
# Lowered formulas

The language Vik lowers SMT-LIB scripts to (`vik/Expr.scala`): linear
arithmetic over integers and reals, uninterpreted functions and arrays,
datatypes, and Boolean connectives. Terms and formulas form one table of
nodes, each referring to earlier ones by their index, so that a shared
subterm is one node.

A model gives each sort a domain of values, each symbol a value, and
applications a meaning. Values are numbers of an ordered field `R` of
characteristic zero, Booleans, or objects of a type `U` (the values of the
other sorts, functions among them).
-/

set_option linter.unusedSectionVars false

namespace Vik.Low

open Lean.Grind Vik.Real

/-- A term or formula, over the nodes before it. -/
inductive Node where
  | const (n : Nat)
  | app (f : Nat) (args : List Nat)
  | num (v : Int)
  | linear (ts : List (Int × Nat)) (c : Int)
  /-- A formula as a Boolean term. -/
  | bterm (f : Nat)
  | tt
  | ff
  | not (a : Nat)
  | and (as : List Nat)
  | or (as : List Nat)
  | implies (a b : Nat)
  | iff (a b : Nat)
  | ite (c a b : Nat)
  | eq (a b : Nat)
  /-- A Boolean term as a formula. -/
  | pred (t : Nat)
  | le (a b : Nat)
  | lt (a b : Nat)
  deriving DecidableEq, Repr

/-- The nodes a node refers to. -/
def Node.children : Node → List Nat
  | .const _ | .num _ | .tt | .ff => []
  | .app f args => f :: args
  | .linear ts _ => ts.map (·.2)
  | .bterm a | .not a | .pred a => [a]
  | .and as | .or as => as
  | .implies a b | .iff a b | .eq a b | .le a b | .lt a b => [a, b]
  | .ite c a b => [c, a, b]

/-- Whether every node refers to earlier nodes only. -/
def wellFormed (nodes : List Node) : Bool :=
  (List.range nodes.length).all fun i =>
    match Tab.at nodes i with
    | some n => n.children.all (· < i)
    | none => false

inductive Val (R U : Type) where
  | num (r : R)
  | bool (b : Bool)
  | obj (u : U)

/-- The numeric value of a value; `0` for the others, which a well-sorted
    formula never takes. -/
def Val.toR {R U : Type} [Zero R] : Val R U → R
  | .num r => r
  | _ => 0

/-- What a model gives the symbols and applications. -/
structure Interp (R U : Type) where
  const : Nat → Val R U
  app : Val R U → List (Val R U) → Val R U

variable {R U : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R]
  [OrderedRing R] [IsCharP R 0]

attribute [local instance low] Lean.Grind.Ring.intCast

open Classical in
/-- Whether a value is `true`. -/
noncomputable def Val.truth (v : Val R U) : Bool := decide (v = .bool true)

/-- The value of node `i` among `vals`. -/
def get (vals : List (Val R U)) (i : Nat) : Val R U := vals[i]?.getD (.bool false)

def linSum (vals : List (Val R U)) : List (Int × Nat) → R
  | [] => 0
  | (a, t) :: ts => (a : R) * (get vals t).toR + linSum vals ts

open Classical in
noncomputable def evalNode (I : Interp R U) (vals : List (Val R U)) : Node → Val R U
  | .const n => I.const n
  | .app f args => I.app (get vals f) (args.map (get vals))
  | .num v => .num (v : R)
  | .linear ts c => .num (linSum vals ts + (c : R))
  | .bterm a => .bool (get vals a).truth
  | .tt => .bool true
  | .ff => .bool false
  | .not a => .bool !(get vals a).truth
  | .and as => .bool (as.all fun a => (get vals a).truth)
  | .or as => .bool (as.any fun a => (get vals a).truth)
  | .implies a b => .bool (!(get vals a).truth || (get vals b).truth)
  | .iff a b => .bool ((get vals a).truth == (get vals b).truth)
  | .ite c a b => .bool (if (get vals c).truth then (get vals a).truth else (get vals b).truth)
  | .eq a b => .bool (decide (get vals a = get vals b))
  | .pred t => .bool (get vals t).truth
  | .le a b => .bool (decide ((get vals a).toR ≤ (get vals b).toR))
  | .lt a b => .bool (decide ((get vals a).toR < (get vals b).toR))

/-- The values of the nodes, in order. -/
noncomputable def values (I : Interp R U) (nodes : List Node) : List (Val R U) :=
  nodes.foldl (fun vals n => vals ++ [evalNode I vals n]) []

theorem values_length (I : Interp R U) (nodes : List Node) : (values I nodes).length = nodes.length := by
  unfold values
  suffices ∀ (acc : List (Val R U)),
      (nodes.foldl (fun vals n => vals ++ [evalNode I vals n]) acc).length = acc.length + nodes.length by
    simpa using this []
  induction nodes with
  | nil => intro acc; simp
  | cons n ns ih => intro acc; simp only [List.foldl_cons]; rw [ih]; simp; omega

/-- The values of a prefix are a prefix of the values. -/
theorem values_prefix (I : Interp R U) (nodes : List Node) :
    ∀ acc : List (Val R U), ∀ i < acc.length,
      (nodes.foldl (fun vals n => vals ++ [evalNode I vals n]) acc)[i]? = acc[i]? := by
  induction nodes with
  | nil => intro acc i _; rfl
  | cons n ns ih =>
    intro acc i hi
    simp only [List.foldl_cons]
    rw [ih _ i (by simp; omega)]
    simp [List.getElem?_append_left hi]

/-- Each node takes the value of its node over the values before it. -/
theorem values_get (I : Interp R U) (nodes : List Node) (i : Nat) (n : Node) (h : nodes[i]? = some n) :
    (values I nodes)[i]? = some (evalNode I (values I (nodes.take i)) n) := by
  have hi : i < nodes.length := by
    rcases Nat.lt_or_ge i nodes.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at h; cases h
  have split : nodes = nodes.take i ++ n :: nodes.drop (i + 1) := by
    conv => lhs; rw [← List.take_append_drop i nodes]
    congr 1
    rw [List.drop_eq_getElem_cons hi]
    congr 1
    rw [List.getElem?_eq_getElem hi] at h; cases h; rfl
  unfold values
  conv => lhs; rw [split]
  rw [List.foldl_append, List.foldl_cons]
  have hl : (List.foldl (fun vals n => vals ++ [evalNode I vals n]) [] (List.take i nodes)).length = i := by
    have := values_length I (nodes.take i); unfold values at this; rw [this]; simp; omega
  rw [values_prefix I _ _ i (by simp [hl])]
  simp [hl]

/-- The value of node `i`. -/
noncomputable def val (I : Interp R U) (nodes : List Node) (i : Nat) : Val R U := get (values I nodes) i

/-- Whether node `i`, a formula, holds. -/
def holds (I : Interp R U) (nodes : List Node) (i : Nat) : Prop := val I nodes i = .bool true

theorem truth_iff (v : Val R U) : v.truth = true ↔ v = .bool true := by
  simp [Val.truth]

theorem all_congr' {as : List Nat} {f g : Nat → Bool} (h : ∀ a ∈ as, f a = g a) :
    as.all f = as.all g := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [List.all_cons, h a (by simp), ih (fun b m => h b (by simp [m]))]

theorem any_congr' {as : List Nat} {f g : Nat → Bool} (h : ∀ a ∈ as, f a = g a) :
    as.any f = as.any g := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [List.any_cons, h a (by simp), ih (fun b m => h b (by simp [m]))]

theorem evalNode_congr (I : Interp R U) {v1 v2 : List (Val R U)} (n : Node)
    (h : ∀ j ∈ n.children, get v1 j = get v2 j) : evalNode I v1 n = evalNode I v2 n := by
  have hl : ∀ (as : List Nat), (∀ j ∈ as, get v1 j = get v2 j) → as.map (get v1) = as.map (get v2) :=
    fun as h => List.map_congr_left h
  cases n with
  | const _ | num _ | tt | ff => rfl
  | app f args =>
    simp only [Node.children, List.mem_cons, forall_eq_or_imp] at h
    simp only [evalNode, h.1, hl args h.2]
  | linear ts c =>
    simp only [Node.children, List.mem_map] at h
    have : linSum v1 ts = linSum v2 ts := by
      induction ts with
      | nil => rfl
      | cons p ts ih =>
        obtain ⟨a, t⟩ := p
        simp only [linSum]
        rw [h t ⟨(a, t), by simp, rfl⟩, ih (fun j ⟨q, hq, e⟩ => h j ⟨q, by simp [hq], e⟩)]
    simp only [evalNode, this]
  | bterm a | not a | pred a =>
    simp only [Node.children, List.mem_singleton, forall_eq] at h
    simp only [evalNode, h]
  | and as | or as =>
    simp only [Node.children] at h
    simp only [evalNode]
    congr 1
    first
      | exact all_congr' (fun a m => by rw [h a m])
      | exact any_congr' (fun a m => by rw [h a m])
  | implies a b | iff a b | eq a b | le a b | lt a b =>
    simp only [evalNode]
    rw [h a (by simp [Node.children]), h b (by simp [Node.children])]
  | ite c a b =>
    simp only [evalNode]
    rw [h c (by simp [Node.children]), h a (by simp [Node.children]), h b (by simp [Node.children])]

theorem get_take (I : Interp R U) (nodes : List Node) {i j : Nat} (hj : j < i) (hi : i ≤ nodes.length) :
    get (values I (nodes.take i)) j = get (values I nodes) j := by
  unfold get
  congr 1
  have hl : (values I (nodes.take i)).length = i := by rw [values_length]; simp; omega
  conv => rhs; unfold values; rw [← List.take_append_drop i nodes, List.foldl_append]
  rw [values_prefix I _ _ j (by unfold values at hl; rw [hl]; exact hj)]
  rfl

/-- In a well-formed table, node `i` takes the value of its node over the
    values of all nodes. -/
theorem val_node {I : Interp R U} {nodes : List Node} (hw : wellFormed nodes = true) {i : Nat} {n : Node}
    (h : nodes[i]? = some n) : val I nodes i = evalNode I (values I nodes) n := by
  have hi : i < nodes.length := by
    rcases Nat.lt_or_ge i nodes.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at h; cases h
  have hc : ∀ j ∈ n.children, j < i := by
    have := List.all_eq_true.mp hw i (List.mem_range.mpr hi)
    rw [Tab.at_eq, h] at this
    simpa using this
  unfold val get
  rw [values_get I nodes i n h]
  simp only [Option.getD_some]
  exact evalNode_congr I n (fun j m => get_take I nodes (hc j m) (Nat.le_of_lt hi))

section
variable {I : Interp R U} {nodes : List Node} (hw : wellFormed nodes = true)
include hw

theorem holds_tt {i : Nat} (h : nodes[i]? = some .tt) : holds I nodes i := by
  unfold holds; rw [val_node hw h]; simp [evalNode]

theorem not_holds_ff {i : Nat} (h : nodes[i]? = some .ff) : ¬holds I nodes i := by
  unfold holds; rw [val_node hw h]; simp [evalNode]

theorem holds_not {i a : Nat} (h : nodes[i]? = some (.not a)) : holds I nodes i ↔ ¬holds I nodes a := by
  unfold holds; rw [val_node hw h]; simp only [evalNode, Val.bool.injEq, Bool.not_eq_true']
  unfold val; rw [← truth_iff]; cases (get (values I nodes) a).truth <;> simp

theorem holds_and {i : Nat} {as : List Nat} (h : nodes[i]? = some (.and as)) :
    holds I nodes i ↔ ∀ a ∈ as, holds I nodes a := by
  unfold holds; rw [val_node hw h]; simp only [evalNode, Val.bool.injEq, List.all_eq_true, truth_iff, val]

theorem holds_or {i : Nat} {as : List Nat} (h : nodes[i]? = some (.or as)) :
    holds I nodes i ↔ ∃ a ∈ as, holds I nodes a := by
  unfold holds; rw [val_node hw h]; simp only [evalNode, Val.bool.injEq, List.any_eq_true, truth_iff, val]

theorem holds_implies {i a b : Nat} (h : nodes[i]? = some (.implies a b)) :
    holds I nodes i ↔ (holds I nodes a → holds I nodes b) := by
  unfold holds; rw [val_node hw h]; simp only [evalNode, Val.bool.injEq, Bool.or_eq_true, Bool.not_eq_true', val]
  rw [← truth_iff, ← truth_iff]
  cases (get (values I nodes) a).truth <;> simp

theorem holds_iff {i a b : Nat} (h : nodes[i]? = some (.iff a b)) :
    holds I nodes i ↔ (holds I nodes a ↔ holds I nodes b) := by
  unfold holds; rw [val_node hw h]; simp only [evalNode, Val.bool.injEq, beq_iff_eq, val]
  rw [← truth_iff, ← truth_iff]
  cases (get (values I nodes) a).truth <;> cases (get (values I nodes) b).truth <;> simp

open Classical in
theorem holds_ite {i c a b : Nat} (h : nodes[i]? = some (.ite c a b)) :
    holds I nodes i ↔ (if holds I nodes c then holds I nodes a else holds I nodes b) := by
  unfold holds; rw [val_node hw h]; simp only [evalNode, Val.bool.injEq, val]
  rw [← truth_iff, ← truth_iff, ← truth_iff]
  cases (get (values I nodes) c).truth <;> simp

theorem holds_eq {i a b : Nat} (h : nodes[i]? = some (.eq a b)) :
    holds I nodes i ↔ val I nodes a = val I nodes b := by
  unfold holds; rw [val_node hw h]; simp [evalNode, val]

theorem holds_pred {i t : Nat} (h : nodes[i]? = some (.pred t)) :
    holds I nodes i ↔ val I nodes t = .bool true := by
  unfold holds; rw [val_node hw h]; simp [evalNode, val, truth_iff]

open Classical in
theorem val_bterm {i f : Nat} (h : nodes[i]? = some (.bterm f)) :
    val I nodes i = .bool (decide (holds I nodes f)) := by
  rw [val_node hw h]
  simp only [evalNode]
  rfl

theorem holds_le {i a b : Nat} (h : nodes[i]? = some (.le a b)) :
    holds I nodes i ↔ (val I nodes a).toR ≤ (val I nodes b).toR := by
  unfold holds; rw [val_node hw h]; simp [evalNode, val]

theorem holds_lt {i a b : Nat} (h : nodes[i]? = some (.lt a b)) :
    holds I nodes i ↔ (val I nodes a).toR < (val I nodes b).toR := by
  unfold holds; rw [val_node hw h]; simp [evalNode, val]

theorem val_num {i : Nat} {v : Int} (h : nodes[i]? = some (.num v)) : val I nodes i = .num (v : R) := by
  simp [val_node hw h, evalNode]

theorem val_const {i n : Nat} (h : nodes[i]? = some (.const n)) : val I nodes i = I.const n := by
  simp [val_node hw h, evalNode]

theorem val_app {i f : Nat} {args : List Nat} (h : nodes[i]? = some (.app f args)) :
    val I nodes i = I.app (val I nodes f) (args.map (val I nodes)) := by
  rw [val_node hw h]; simp only [evalNode]; rfl

theorem val_linear {i : Nat} {ts : List (Int × Nat)} {c : Int} (h : nodes[i]? = some (.linear ts c)) :
    val I nodes i = .num (linSum (values I nodes) ts + (c : R)) := by
  simp [val_node hw h, evalNode]

end

/-! ## Sorts -/

inductive SortDef where
  | bool
  | int
  | real
  /-- An uninterpreted sort or a datatype. -/
  | user
  /-- Functions (and arrays) from the sorts `args` to `res`. -/
  | fn (args : List Nat) (res : Nat)
  deriving DecidableEq, Repr

/-- The sorts, by number, and the sort of each symbol. -/
structure Sig where
  sorts : List SortDef
  decls : List Nat

def Sig.is (sig : Sig) (s : Nat) (d : SortDef) : Bool := sig.sorts[s]? == some d

def Sig.numeric (sig : Sig) (s : Nat) : Bool := sig.is s .int || sig.is s .real

/-- Whether a value of sort `s` can stand for one of sort `a`: the same sort,
    or an integer for a real. -/
def Sig.fits (sig : Sig) (s a : Nat) : Bool := s == a || (sig.is s .int && sig.is a .real)

/-- Whether arguments of the sorts `ss` fit parameters of the sorts `as`. -/
def Sig.allFit (sig : Sig) : List Nat → List Nat → Bool
  | [], [] => true
  | s :: ss, a :: as => sig.fits s a && sig.allFit ss as
  | _, _ => false

/-- Whether node `n` has sort `s`, its children those of `sortOf`. -/
def nodeTyped (sig : Sig) (sortOf : List Nat) (n : Node) (s : Nat) : Bool :=
  let so (i : Nat) := (Tab.at sortOf i).getD 0
  let isBool (i : Nat) := sig.is (so i) .bool
  match n with
  | .const k => Tab.at sig.decls k == some s
  | .app f args =>
    match sig.sorts[so f]? with
    | some (.fn as r) => r == s && sig.allFit (args.map so) as
    | _ => false
  | .num _ => sig.is s .int
  | .linear ts _ =>
    (sig.is s .int && ts.all (fun p => sig.is (so p.2) .int))
      || (sig.is s .real && ts.all (fun p => sig.numeric (so p.2)))
  | .bterm f => sig.is s .bool && isBool f
  | .tt | .ff => sig.is s .bool
  | .not a | .pred a => sig.is s .bool && isBool a
  | .and as | .or as => sig.is s .bool && as.all isBool
  | .implies a b | .iff a b => sig.is s .bool && isBool a && isBool b
  | .ite c a b => sig.is s .bool && isBool c && isBool a && isBool b
  | .eq a b => sig.is s .bool && so a == so b
  | .le a b | .lt a b => sig.is s .bool && sig.numeric (so a) && sig.numeric (so b)

/-- Whether every node has the sort `sortOf` gives it. -/
def typed (sig : Sig) (nodes : List Node) (sortOf : List Nat) : Bool :=
  sortOf.length == nodes.length &&
    (List.range nodes.length).all fun i =>
      match Tab.at nodes i with
      | some n => nodeTyped sig sortOf n ((Tab.at sortOf i).getD 0)
      | none => false

/-- `r` relates the lists pairwise. -/
def Forall2 {α β : Type} (r : α → β → Prop) : List α → List β → Prop
  | [], [] => True
  | a :: as, b :: bs => r a b ∧ Forall2 r as bs
  | _, _ => False

theorem forall2_map {α β : Type} (r : α → β → Prop) (f : Nat → α) (g : Nat → β) :
    ∀ l : List Nat, (∀ j ∈ l, r (f j) (g j)) → Forall2 r (l.map f) (l.map g)
  | [], _ => trivial
  | a :: l, h => ⟨h a (by simp), forall2_map r f g l (fun j m => h j (by simp [m]))⟩

/-- A model: an interpretation with a domain for each sort. -/
structure Model (R U : Type) extends Interp R U where
  dom : Nat → Val R U → Prop

/-- A value of sort `s` is in its range, if `s` is a sort of bit-vectors. -/
def inRange (bv : List (Nat × Nat)) (s : Nat) (v : Val R U) : Prop :=
  ∀ w, bv.lookup s = some w → ∃ k : Int, v = .num (k : R) ∧ 0 ≤ k ∧ k < 2 ^ w

/-- What a model of the sorts and symbols of `sig` satisfies, the sorts of
    bit-vectors `bv` among its integer sorts: a function takes a value of its
    sort on arguments of theirs, in their ranges. -/
structure Model.Sound (sig : Sig) (bv : List (Nat × Nat)) (M : Model R U) : Prop where
  bool : ∀ s v, sig.sorts[s]? = some .bool → (M.dom s v ↔ ∃ b, v = .bool b)
  int : ∀ s v, sig.sorts[s]? = some .int → (M.dom s v ↔ ∃ k : Int, v = .num (k : R))
  real : ∀ s v, sig.sorts[s]? = some .real → (M.dom s v ↔ ∃ r, v = .num r)
  fn : ∀ s as r f xs, sig.sorts[s]? = some (.fn as r) → M.dom s f →
    Forall2 (fun a x => M.dom a x ∧ inRange bv a x) as xs → M.dom r (M.app f xs) ∧ inRange bv r (M.app f xs)
  const : ∀ k s, sig.decls[k]? = some s → M.dom s (M.const k)
  /-- The sorts of bit-vectors are integer sorts. -/
  bvInt : ∀ s w, bv.lookup s = some w → sig.sorts[s]? = some .int

section
variable {sig : Sig} {bv : List (Nat × Nat)} {M : Model R U} (hM : M.Sound sig bv)
include hM

/-- A value of a sort that fits another is a value of that sort, in range. -/
theorem dom_fit {s a : Nat} {v : Val R U} (h : sig.fits s a = true) (hd : M.dom s v) (hr : inRange bv s v) :
    M.dom a v ∧ inRange bv a v := by
  simp only [Sig.fits, Sig.is, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with e | ⟨hi, hre⟩
  · rw [← e]; exact ⟨hd, hr⟩
  · obtain ⟨k, ek⟩ := (hM.int _ _ hi).mp hd
    refine ⟨(hM.real _ _ hre).mpr ⟨_, ek⟩, fun w hw => ?_⟩
    rw [hM.bvInt a w hw] at hre; cases hre

/-- Arguments that fit their parameters take values of the parameters'
    sorts, in range. -/
theorem forall2_fit {so : Nat → Nat} {v : Nat → Val R U} :
    ∀ (l : List Nat) (as : List Nat), sig.allFit (l.map so) as = true →
      (∀ x ∈ l, M.dom (so x) (v x) ∧ inRange bv (so x) (v x)) →
      Forall2 (fun a x => M.dom a x ∧ inRange bv a x) as (l.map v)
  | [], [], _, _ => trivial
  | [], _ :: _, h, _ => by simp [Sig.allFit] at h
  | _ :: _, [], h, _ => by simp [Sig.allFit] at h
  | x :: l, a :: as, h, hx => by
    simp only [List.map_cons, Sig.allFit, Bool.and_eq_true] at h
    refine ⟨?_, forall2_fit l as h.2 (fun y m => hx y (List.mem_cons_of_mem x m))⟩
    obtain ⟨hd, hr⟩ := hx x List.mem_cons_self
    simp only [Sig.fits, Sig.is, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h.1 with e | ⟨hi, hre⟩
    · rw [← e]; exact ⟨hd, hr⟩
    · obtain ⟨k, ek⟩ := (hM.int _ _ hi).mp hd
      refine ⟨(hM.real _ _ hre).mpr ⟨_, ek⟩, fun w hw => ?_⟩
      rw [hM.bvInt a w hw] at hre; cases hre

theorem dom_num_of_numeric {s : Nat} {v : Val R U} (hs : sig.numeric s = true) (h : M.dom s v) :
    ∃ r, v = .num r := by
  simp only [Sig.numeric, Sig.is, Bool.or_eq_true, beq_iff_eq] at hs
  rcases hs with hs | hs
  · obtain ⟨k, rfl⟩ := (hM.int _ _ hs).mp h; exact ⟨_, rfl⟩
  · exact (hM.real _ _ hs).mp h

theorem linSum_int {nodes : List Node} (ts : List (Int × Nat))
    (h : ∀ p ∈ ts, ∃ k : Int, val M.toInterp nodes p.2 = .num (k : R)) :
    ∃ k : Int, linSum (values M.toInterp nodes) ts = (k : R) := by
  induction ts with
  | nil => exact ⟨0, by simp [linSum]; grind⟩
  | cons p ts ih =>
    obtain ⟨a, t⟩ := p
    obtain ⟨k, hk⟩ := h (a, t) (by simp)
    obtain ⟨m, hm⟩ := ih (fun q m => h q (by simp [m]))
    refine ⟨a * k + m, ?_⟩
    simp only [linSum, hm]
    unfold val at hk
    rw [hk]
    simp only [Val.toR, Ring.intCast_add, Ring.intCast_mul]

/-- In a well-sorted table, every node whose nodes before it of bit-vector
    sorts are in range takes a value of its sort. -/
theorem val_dom_lt {nodes : List Node} {sortOf : List Nat} (hw : wellFormed nodes = true)
    (ht : typed sig nodes sortOf = true) :
    ∀ i, i < nodes.length → (∀ j < i, inRange bv (sortOf[j]?.getD 0) (val M.toInterp nodes j)) →
      M.dom (sortOf[i]?.getD 0) (val M.toInterp nodes i) := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
  intro hi hrng
  simp only [typed, Tab.at_eq, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, Tab.at_eq] at ht
  have hn := ht.2 i hi
  obtain ⟨n, hn'⟩ : ∃ n, nodes[i]? = some n := ⟨nodes[i], List.getElem?_eq_getElem hi⟩
  rw [hn'] at hn
  have hc : ∀ j ∈ n.children, j < i := by
    have := List.all_eq_true.mp hw i (List.mem_range.mpr hi)
    rw [Tab.at_eq, hn'] at this; simpa using this
  have ihc : ∀ j ∈ n.children, M.dom (sortOf[j]?.getD 0) (val M.toInterp nodes j) :=
    fun j m => ih j (hc j m) (Nat.lt_trans (hc j m) hi) (fun j' h' => hrng j' (by have := hc j m; omega))
  generalize sortOf[i]?.getD 0 = s at *
  have boolv : sig.is s .bool = true → ∀ b : Bool, M.dom s (.bool b) := by
    intro hb b
    simp only [Sig.is, beq_iff_eq] at hb
    exact (hM.bool _ _ hb).mpr ⟨b, rfl⟩
  have boolv' : (sig.is s .bool && true) = true → ∀ b : Bool, M.dom s (.bool b) := by
    simpa using boolv
  have val_bool : ∀ b, val M.toInterp nodes i = .bool b → sig.is s .bool = true → M.dom s (val M.toInterp nodes i) :=
    fun b e hb => by rw [e]; exact boolv hb b
  cases n with
  | const k =>
    simp only [Tab.at_eq, nodeTyped, beq_iff_eq] at hn
    rw [val_const hw hn']; exact hM.const _ _ hn
  | app f args =>
    simp only [Tab.at_eq, nodeTyped] at hn
    split at hn
    · rename_i as r hs
      simp only [Bool.and_eq_true, beq_iff_eq] at hn
      obtain ⟨rfl, hargs⟩ := hn
      rw [val_app hw hn']
      refine (hM.fn _ as _ _ _ hs (ihc f (by simp [Node.children])) ?_).1
      exact forall2_fit hM args as hargs (fun j m =>
        ⟨ihc j (by simp [Node.children, m]),
          hrng j (hc j (by simp [Node.children, m]))⟩)
    · cases hn
  | num v =>
    simp only [Tab.at_eq, nodeTyped, Sig.is, beq_iff_eq] at hn
    rw [val_num hw hn']; exact (hM.int _ _ hn).mpr ⟨v, rfl⟩
  | linear ts c =>
    simp only [Tab.at_eq, nodeTyped, Bool.or_eq_true, Bool.and_eq_true, List.all_eq_true] at hn
    rw [val_linear hw hn']
    rcases hn with ⟨hs, hts⟩ | ⟨hs, _⟩
    · simp only [Sig.is, beq_iff_eq] at hs
      obtain ⟨k, hk⟩ := linSum_int hM (nodes := nodes) ts (fun p m => by
        have := hts p m
        simp only [Sig.is, beq_iff_eq] at this
        exact (hM.int _ _ this).mp (ihc p.2 (by simp [Node.children]; exact ⟨p.1, m⟩)))
      rw [hk]
      exact (hM.int _ _ hs).mpr ⟨k + c, by simp [Ring.intCast_add]⟩
    · simp only [Sig.is, beq_iff_eq] at hs
      exact (hM.real _ _ hs).mpr ⟨_, rfl⟩
  | bterm f =>
    simp only [Tab.at_eq, nodeTyped, Bool.and_eq_true] at hn
    exact val_bool _ (val_bterm hw hn') hn.1
  | tt | ff =>
    simp only [Tab.at_eq, nodeTyped] at hn
    rw [val_node hw hn']; exact boolv hn _
  | not a | pred a | and _ | or _ | implies _ _ | iff _ _ | ite _ _ _ | eq _ _ | le _ _ | lt _ _ =>
    simp only [Tab.at_eq, nodeTyped, Bool.and_eq_true] at hn
    rw [val_node hw hn']
    simp only [evalNode]
    first
      | exact boolv hn.1 _
      | exact boolv hn.1.1 _
      | exact boolv hn.1.1.1 _


/-- In a well-sorted table, every node of a set `S` closed under children,
    whose children of bit-vector sorts are in range, takes a value of its
    sort. -/
theorem val_dom_sub {nodes : List Node} {sortOf : List Nat} (hw : wellFormed nodes = true)
    (ht : typed sig nodes sortOf = true) (S : Nat → Prop)
    (hS : ∀ i n, nodes[i]? = some n → S i → ∀ c ∈ n.children, S c)
    (hrng : ∀ i n, nodes[i]? = some n → S i → ∀ c ∈ n.children,
      inRange bv (sortOf[c]?.getD 0) (val M.toInterp nodes c)) :
    ∀ i, i < nodes.length → S i → M.dom (sortOf[i]?.getD 0) (val M.toInterp nodes i) := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
  intro hi hSi
  simp only [typed, Tab.at_eq, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, Tab.at_eq] at ht
  have hn := ht.2 i hi
  obtain ⟨n, hn'⟩ : ∃ n, nodes[i]? = some n := ⟨nodes[i], List.getElem?_eq_getElem hi⟩
  rw [hn'] at hn
  have hc : ∀ j ∈ n.children, j < i := by
    have := List.all_eq_true.mp hw i (List.mem_range.mpr hi)
    rw [Tab.at_eq, hn'] at this; simpa using this
  have ihc : ∀ j ∈ n.children, M.dom (sortOf[j]?.getD 0) (val M.toInterp nodes j) :=
    fun j m => ih j (hc j m) (Nat.lt_trans (hc j m) hi) (hS i n hn' hSi j m)
  generalize sortOf[i]?.getD 0 = s at *
  have boolv : sig.is s .bool = true → ∀ b : Bool, M.dom s (.bool b) := by
    intro hb b
    simp only [Sig.is, beq_iff_eq] at hb
    exact (hM.bool _ _ hb).mpr ⟨b, rfl⟩
  have boolv' : (sig.is s .bool && true) = true → ∀ b : Bool, M.dom s (.bool b) := by
    simpa using boolv
  have val_bool : ∀ b, val M.toInterp nodes i = .bool b → sig.is s .bool = true → M.dom s (val M.toInterp nodes i) :=
    fun b e hb => by rw [e]; exact boolv hb b
  cases n with
  | const k =>
    simp only [Tab.at_eq, nodeTyped, beq_iff_eq] at hn
    rw [val_const hw hn']; exact hM.const _ _ hn
  | app f args =>
    simp only [Tab.at_eq, nodeTyped] at hn
    split at hn
    · rename_i as r hs
      simp only [Bool.and_eq_true, beq_iff_eq] at hn
      obtain ⟨rfl, hargs⟩ := hn
      rw [val_app hw hn']
      refine (hM.fn _ as _ _ _ hs (ihc f (by simp [Node.children])) ?_).1
      exact forall2_fit hM args as hargs (fun j m =>
        ⟨ihc j (by simp [Node.children, m]),
          hrng i _ hn' hSi j (by simp [Node.children, m])⟩)
    · cases hn
  | num v =>
    simp only [Tab.at_eq, nodeTyped, Sig.is, beq_iff_eq] at hn
    rw [val_num hw hn']; exact (hM.int _ _ hn).mpr ⟨v, rfl⟩
  | linear ts c =>
    simp only [Tab.at_eq, nodeTyped, Bool.or_eq_true, Bool.and_eq_true, List.all_eq_true] at hn
    rw [val_linear hw hn']
    rcases hn with ⟨hs, hts⟩ | ⟨hs, _⟩
    · simp only [Sig.is, beq_iff_eq] at hs
      obtain ⟨k, hk⟩ := linSum_int hM (nodes := nodes) ts (fun p m => by
        have := hts p m
        simp only [Sig.is, beq_iff_eq] at this
        exact (hM.int _ _ this).mp (ihc p.2 (by simp [Node.children]; exact ⟨p.1, m⟩)))
      rw [hk]
      exact (hM.int _ _ hs).mpr ⟨k + c, by simp [Ring.intCast_add]⟩
    · simp only [Sig.is, beq_iff_eq] at hs
      exact (hM.real _ _ hs).mpr ⟨_, rfl⟩
  | bterm f =>
    simp only [Tab.at_eq, nodeTyped, Bool.and_eq_true] at hn
    exact val_bool _ (val_bterm hw hn') hn.1
  | tt | ff =>
    simp only [Tab.at_eq, nodeTyped] at hn
    rw [val_node hw hn']; exact boolv hn _
  | not a | pred a | and _ | or _ | implies _ _ | iff _ _ | ite _ _ _ | eq _ _ | le _ _ | lt _ _ =>
    simp only [Tab.at_eq, nodeTyped, Bool.and_eq_true] at hn
    rw [val_node hw hn']
    simp only [evalNode]
    first
      | exact boolv hn.1 _
      | exact boolv hn.1.1 _
      | exact boolv hn.1.1.1 _


/-- An application in a well-sorted table whose nodes before it of bit-vector
    sorts are in range is in range. -/
theorem rng_app {nodes : List Node} {sortOf : List Nat} (hw : wellFormed nodes = true)
    (ht : typed sig nodes sortOf = true) {i f : Nat} {args : List Nat} (hi : i < nodes.length)
    (hn' : nodes[i]? = some (.app f args))
    (hrng : ∀ j < i, inRange bv (sortOf[j]?.getD 0) (val M.toInterp nodes j)) :
    inRange bv (sortOf[i]?.getD 0) (val M.toInterp nodes i) := by
  have hc : ∀ j ∈ (Node.app f args).children, j < i := by
    have := List.all_eq_true.mp hw i (List.mem_range.mpr hi)
    rw [Tab.at_eq, hn'] at this; simpa using this
  have hd : ∀ j ∈ (Node.app f args).children, M.dom (sortOf[j]?.getD 0) (val M.toInterp nodes j) :=
    fun j m => val_dom_lt hM hw ht j (by have := hc j m; omega)
      (fun j' h' => hrng j' (by have := hc j m; omega))
  have ht' := ht
  simp only [typed, Tab.at_eq, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at ht'
  have hn := ht'.2 i hi
  rw [hn'] at hn
  generalize sortOf[i]?.getD 0 = s at hn ⊢
  simp only [Tab.at_eq, nodeTyped] at hn
  split at hn
  · rename_i as r hs
    simp only [Bool.and_eq_true, beq_iff_eq] at hn
    obtain ⟨rfl, hargs⟩ := hn
    rw [val_app hw hn']
    refine (hM.fn _ as _ _ _ hs (hd f (by simp [Node.children])) ?_).2
    exact forall2_fit hM args as hargs (fun j m =>
      ⟨hd j (by simp [Node.children, m]), hrng j (hc j (by simp [Node.children, m]))⟩)
  · cases hn
/-- In a well-sorted table whose nodes of bit-vector sorts are in range, every
    node takes a value of its sort. -/
theorem val_dom {nodes : List Node} {sortOf : List Nat} (hw : wellFormed nodes = true)
    (ht : typed sig nodes sortOf = true)
    (hrng : ∀ i < nodes.length, inRange bv (sortOf[i]?.getD 0) (val M.toInterp nodes i)) :
    ∀ i, i < nodes.length → M.dom (sortOf[i]?.getD 0) (val M.toInterp nodes i) :=
  fun i hi => val_dom_lt hM hw ht i hi (fun j hj => hrng j (by omega))

end

/-- An integer node takes an integer value. -/
theorem val_int {sig : Sig} {bv : List (Nat × Nat)} {M : Model R U} (hM : M.Sound sig bv) {nodes : List Node}
    {sortOf : List Nat} (hw : wellFormed nodes = true) (ht : typed sig nodes sortOf = true)
    (hrng : ∀ i < nodes.length, inRange bv (sortOf[i]?.getD 0) (val M.toInterp nodes i)) {i : Nat} (hi : i < nodes.length)
    (hs : sig.is (sortOf[i]?.getD 0) .int = true) : ∃ k : Int, val M.toInterp nodes i = .num (k : R) := by
  simp only [Sig.is, beq_iff_eq] at hs
  exact (hM.int _ _ hs).mp (val_dom hM hw ht hrng i hi)

end Vik.Low
