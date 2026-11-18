import Vik.Lowered

/-!
# Witnesses

The extensionality instances of a proof (`Extensionality` in
`vik/ProofCheck.scala`) say that two functions are equal or differ at fresh
constants, their witnesses: `f = g ∨ f(w₁)…(wₙ) ≠ g(w₁)…(wₙ)`. Such a clause
does not hold in every model of the problem, only in one where the witnesses
take the right values. A witness of a bit-vector index also comes with its
range (`WitnessRange`), which holds for the same reason.

The checker of a whole answer extends any model of the problem with values of
the witnesses: one instance after the other, in the order the answer lists
them, each witness of an instance takes a value where the two functions
differ. For that to work, the witnesses must be fresh: no input, no level,
and no function of an instance may depend on the witnesses of that instance
or of a later one. This file holds what the checker computes for that, the
rank of each symbol and the depth of each node, with the facts the extension
relies on: a node's value only depends on the symbols of rank up to its
depth, and an application chain applies a function to its witnesses.
-/

set_option linter.unusedSectionVars false

namespace Vik.Low

open Lean.Grind Vik.Real

/-! ## Ranks and depths -/

/-- The instance whose witnesses include symbol `n`. -/
def extIndex (exts : List (Nat × Nat × List Nat)) (n : Nat) : Option Nat :=
  exts.findIdx? (fun x => x.2.2.contains n)

/-- The rank of a symbol: `k + 2` for a witness of instance `k`, `1` for
    another witness (one of a range alone), `0` for the other symbols. -/
def rankOf (exts : List (Nat × Nat × List Nat)) (wits : List Nat) (n : Nat) : Nat :=
  match extIndex exts n with
  | some k => k + 2
  | none => if wits.contains n then 1 else 0

def maxOf (l : List Nat) : Nat := l.foldl max 0

/-- The rank of a node's own symbol. -/
def Node.own (rank : Nat → Nat) : Node → Nat
  | .const n => rank n
  | _ => 0

/-- The depth of a node: the highest rank of a symbol it depends on. -/
def depthNode (rank : Nat → Nat) (ds : List Nat) (n : Node) : Nat :=
  max (n.own rank) (maxOf (n.children.map fun j => ds[j]?.getD 0))

/-- The values of `F` over a table of nodes, each over those before it. -/
def scan {α : Type} (F : List α → Node → α) (nodes : List Node) : List α :=
  nodes.foldl (fun ds n => ds ++ [F ds n]) []

/-- The depths of the nodes from the `k`-th on, `acc` those before it in
    reverse and `t` their tree, where a node looks the depths of its children
    up. -/
def depthsAux (rank : Nat → Nat) : Tab Nat → List Nat → Nat → List Node → List Nat
  | _, acc, _, [] => acc
  | t, acc, k, n :: ns =>
    let d := max (n.own rank) (maxOf (n.children.map fun j => (t.get j).getD 0))
    depthsAux rank (t.set k d) (d :: acc) (k + 1) ns

def depths (rank : Nat → Nat) (nodes : List Node) : List Nat := (depthsAux rank .leaf [] 0 nodes).reverse

def depthOf (ds : List Nat) (i : Nat) : Nat := (Tab.at ds i).getD 0

theorem depthOf_eq (ds : List Nat) (i : Nat) : depthOf ds i = ds[i]?.getD 0 := by simp [depthOf]

theorem le_foldl_max : ∀ (l : List Nat) (acc : Nat), acc ≤ l.foldl max acc
  | [], _ => Nat.le_refl _
  | a :: l, acc => Nat.le_trans (Nat.le_max_left acc a) (le_foldl_max l (max acc a))

theorem mem_le_foldl_max : ∀ {l : List Nat} {x : Nat} (acc : Nat), x ∈ l → x ≤ l.foldl max acc
  | a :: l, x, acc, m => by
    rcases List.mem_cons.mp m with rfl | m'
    · exact Nat.le_trans (Nat.le_max_right acc x) (le_foldl_max l _)
    · exact mem_le_foldl_max (max acc a) m'

theorem le_maxOf {l : List Nat} {x : Nat} (h : x ∈ l) : x ≤ maxOf l := mem_le_foldl_max 0 h

section Scan
variable {α : Type} (F : List α → Node → α)

theorem scan_length' (nodes : List Node) :
    ∀ acc : List α, (nodes.foldl (fun ds n => ds ++ [F ds n]) acc).length = acc.length + nodes.length := by
  induction nodes with
  | nil => intro acc; simp
  | cons n ns ih => intro acc; simp only [List.foldl_cons]; rw [ih]; simp; omega

theorem scan_length (nodes : List Node) : (scan F nodes).length = nodes.length := by
  simpa using scan_length' F nodes []

theorem scan_prefix (nodes : List Node) :
    ∀ acc : List α, ∀ i < acc.length, (nodes.foldl (fun ds n => ds ++ [F ds n]) acc)[i]? = acc[i]? := by
  induction nodes with
  | nil => intro acc i _; rfl
  | cons n ns ih =>
    intro acc i hi
    simp only [List.foldl_cons]
    rw [ih _ i (by simp; omega)]
    simp [List.getElem?_append_left hi]

theorem scan_get (nodes : List Node) (i : Nat) (n : Node) (h : nodes[i]? = some n) :
    (scan F nodes)[i]? = some (F (scan F (nodes.take i)) n) := by
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
  unfold scan
  conv => lhs; rw [split]
  rw [List.foldl_append, List.foldl_cons]
  have hl : (List.foldl (fun ds n => ds ++ [F ds n]) [] (List.take i nodes)).length = i := by
    rw [scan_length']; simp; omega
  rw [scan_prefix F _ _ i (by simp [hl])]
  simp [hl]

theorem scan_take (nodes : List Node) {i j : Nat} (hj : j < i) (hi : i ≤ nodes.length) :
    (scan F (nodes.take i))[j]? = (scan F nodes)[j]? := by
  have hl : (scan F (nodes.take i)).length = i := by rw [scan_length]; simp; omega
  conv => rhs; unfold scan; rw [← List.take_append_drop i nodes, List.foldl_append]
  rw [scan_prefix F _ _ j (by unfold scan at hl; rw [hl]; exact hj)]
  rfl

theorem depthsAux_eq (rank : Nat → Nat) :
    ∀ (ns : List Node) (pre : List Nat) (t : Tab Nat), t.Holds (fun j => pre[j]?.getD 0) pre.length →
      depthsAux rank t pre.reverse pre.length ns = (ns.foldl (fun ds n => ds ++ [depthNode rank ds n]) pre).reverse
  | [], _, _, _ => rfl
  | n :: ns, pre, t, ht => by
    have hd : max (n.own rank) (maxOf (n.children.map fun j => (t.get j).getD 0)) = depthNode rank pre n := by
      unfold depthNode
      congr 2
      apply List.map_congr_left
      intro j _
      rw [ht j]
      split
      · rfl
      · rename_i hj; rw [List.getElem?_eq_none (by omega)]
    simp only [depthsAux, List.foldl_cons]
    rw [hd]
    have ht' := Tab.Holds.congr (Tab.holds_set t _ pre.length (depthNode rank pre n) ht) (g := fun j => (pre ++ [depthNode rank pre n])[j]?.getD 0)
      (by
        intro j hj
        by_cases e : j = pre.length
        · subst e; simp
        · simp only [e, ↓reduceIte]; rw [List.getElem?_append_left (by omega)])
    rw [← depthsAux_eq rank ns (pre ++ [depthNode rank pre n]) _ (by simpa using ht')]
    simp

theorem depths_eq_scan (rank : Nat → Nat) (nodes : List Node) : depths rank nodes = scan (depthNode rank) nodes := by
  unfold depths scan
  have := depthsAux_eq rank nodes [] .leaf (fun _ => rfl)
  simp only [List.reverse_nil, List.length_nil] at this
  rw [this, List.reverse_reverse]

end Scan

theorem lt_length_of_get {nodes : List Node} {i : Nat} {n : Node} (h : nodes[i]? = some n) :
    i < nodes.length := by
  rcases Nat.lt_or_ge i nodes.length with h' | h'
  · exact h'
  · rw [List.getElem?_eq_none h'] at h; cases h

theorem children_lt {nodes : List Node} (hw : wellFormed nodes = true) {i : Nat} {n : Node}
    (h : nodes[i]? = some n) : ∀ j ∈ n.children, j < i := by
  have := List.all_eq_true.mp hw i (List.mem_range.mpr (lt_length_of_get h))
  rw [Tab.at_eq, h] at this; simpa using this

/-- A node is at least as deep as its own symbol and as its children. -/
theorem depth_node {rank : Nat → Nat} {nodes : List Node} (hw : wellFormed nodes = true) {i : Nat} {n : Node}
    (h : nodes[i]? = some n) :
    n.own rank ≤ depthOf (depths rank nodes) i ∧
      ∀ j ∈ n.children, depthOf (depths rank nodes) j ≤ depthOf (depths rank nodes) i := by
  have hi := lt_length_of_get h
  have hc := children_lt hw h
  have e : depthOf (depths rank nodes) i = depthNode rank (scan (depthNode rank) (nodes.take i)) n := by
    rw [depthOf_eq, depths_eq_scan, scan_get _ nodes i n h]; rfl
  rw [e]
  refine ⟨Nat.le_max_left _ _, fun j m => ?_⟩
  unfold depthNode
  refine Nat.le_trans ?_ (Nat.le_max_right _ _)
  have : (scan (depthNode rank) (nodes.take i))[j]?.getD 0 = depthOf (depths rank nodes) j := by
    rw [depthOf_eq, depths_eq_scan, scan_take _ nodes (hc j m) (Nat.le_of_lt hi)]
  rw [← this]
  exact le_maxOf (List.mem_map.mpr ⟨j, m, rfl⟩)

/-! ## Values that depend on low ranks only -/

variable {R U : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R]
  [OrderedRing R] [IsCharP R 0]

attribute [local instance low] Lean.Grind.Ring.intCast

theorem val_of_ge {I : Interp R U} {nodes : List Node} {i : Nat} (h : nodes.length ≤ i) :
    val I nodes i = .bool false := by
  unfold val get
  rw [List.getElem?_eq_none (by rw [values_length]; exact h)]
  rfl

/-- Two interpretations that agree on the applications and on the symbols of
    rank up to `D` give the same value to the nodes of depth up to `D`. -/
theorem val_agree {rank : Nat → Nat} {nodes : List Node} (hw : wellFormed nodes = true) {I I' : Interp R U}
    (happ : I.app = I'.app) {D : Nat} (hc : ∀ n, rank n ≤ D → I.const n = I'.const n) :
    ∀ i, depthOf (depths rank nodes) i ≤ D → val I nodes i = val I' nodes i := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
  intro hd
  rcases Nat.lt_or_ge i nodes.length with hi | hi
  · obtain ⟨n, hn⟩ : ∃ n, nodes[i]? = some n := ⟨nodes[i], List.getElem?_eq_getElem hi⟩
    have ⟨hown, hch⟩ := depth_node (rank := rank) hw hn
    have hlt := children_lt hw hn
    rw [val_node hw hn, val_node hw hn]
    rw [evalNode_congr I (v2 := values I' nodes) n (fun j m => ih j (hlt j m) (Nat.le_trans (hch j m) hd))]
    cases n with
    | const k =>
      simp only [evalNode]
      exact hc k (Nat.le_trans hown hd)
    | app f args => simp only [evalNode, happ]
    | _ => rfl
  · rw [val_of_ge hi, val_of_ge hi]

/-! ## Application chains -/

/-- `F` is `f` applied to the witnesses in turn, given last first:
    `F = (…(f w₁)…) wₙ` with `ws = [wₙ, …, w₁]`. -/
def chainRev (nodes : List Node) (f : Nat) : Nat → List Nat → Bool
  | F, [] => F == f
  | F, w :: rest =>
    match nodes[F]? with
    | some (.app h [c]) => nodes[c]? == some (.const w) && chainRev nodes f h rest
    | _ => false

/-- Whether the witnesses of a chain `F` (as `chainRev`) have the sorts of the
    parameters they are given for, not merely sorts that fit them. -/
def chainExact (sig : Sig) (nodes : List Node) (sortOf : List Nat) : Nat → List Nat → Bool
  | _, [] => true
  | F, _ :: rest =>
    match nodes[F]? with
    | some (.app h [c]) =>
      (match sig.sorts[sortOf[h]?.getD 0]? with
        | some (.fn [a] _) => a == sortOf[c]?.getD 0
        | _ => false) && chainExact sig nodes sortOf h rest
    | _ => false

/-- `p` applied to the values `xs` in turn. -/
def appAll (I : Interp R U) (p : Val R U) (xs : List (Val R U)) : Val R U :=
  xs.foldl (fun v x => I.app v [x]) p

theorem chain_val {I : Interp R U} {nodes : List Node} (hw : wellFormed nodes = true) {f : Nat} :
    ∀ (ws : List Nat) (F : Nat), chainRev nodes f F ws = true →
      val I nodes F = appAll I (val I nodes f) (ws.reverse.map I.const)
  | [], F, h => by
    simp only [chainRev, beq_iff_eq] at h; subst h; rfl
  | w :: rest, F, h => by
    simp only [chainRev] at h
    split at h
    · rename_i h' c hF
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      rw [val_app hw hF, List.map_cons, List.map_nil, val_const hw h.1, chain_val hw rest h' h.2]
      simp [appAll, List.foldl_append]
    · cases h

/-- The sorts of a chain: from `s`, functions of one argument of each sort of
    `as` in turn, to `t`. -/
def SortChain (sig : Sig) : Nat → List Nat → Nat → Prop
  | s, [], t => s = t
  | s, a :: as, t => ∃ r, sig.sorts[s]? = some (.fn [a] r) ∧ SortChain sig r as t

theorem sortChain_snoc {sig : Sig} {a t : Nat} :
    ∀ {s : Nat} {as : List Nat} {r : Nat}, SortChain sig s as r → sig.sorts[r]? = some (.fn [a] t) →
      SortChain sig s (as ++ [a]) t
  | s, [], r, h, h' => by simp only [SortChain] at h; subst h; exact ⟨t, h', rfl⟩
  | s, b :: as, r, ⟨r', h1, h2⟩, h' => ⟨r', h1, sortChain_snoc h2 h'⟩

/-- The sort of symbol `n`. -/
def Sig.declOf (sig : Sig) (n : Nat) : Nat := (sig.decls[n]?).getD 0

theorem chain_sorts {sig : Sig} {nodes : List Node} {sortOf : List Nat} (ht : typed sig nodes sortOf = true)
    {f : Nat} : ∀ (ws : List Nat) (F : Nat), chainRev nodes f F ws = true → chainExact sig nodes sortOf F ws = true →
      SortChain sig (sortOf[f]?.getD 0) (ws.reverse.map sig.declOf) (sortOf[F]?.getD 0)
  | [], F, h, _ => by
    simp only [chainRev, beq_iff_eq] at h; subst h; rfl
  | w :: rest, F, h, hx => by
    simp only [chainRev] at h
    split at h
    · rename_i h' c hF
      simp only [chainExact, hF, Bool.and_eq_true] at hx
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      have ih := chain_sorts ht rest h' h.2 hx.2
      simp only [typed, Tab.at_eq, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at ht
      have tF := ht.2 F (lt_length_of_get hF)
      rw [hF] at tF
      have tc := ht.2 c (lt_length_of_get h.1)
      rw [h.1] at tc
      simp only [Tab.at_eq, nodeTyped, beq_iff_eq] at tF tc
      split at tF
      · rename_i as r hs
        simp only [Bool.and_eq_true, beq_iff_eq, List.map_cons, List.map_nil] at tF
        obtain ⟨rfl, -⟩ := tF
        have eas : as = [sortOf[c]?.getD 0] := by
          have hx1 := hx.1
          rw [hs] at hx1
          rcases as with _ | ⟨a, _ | ⟨b, _⟩⟩ <;> simp_all
        subst eas
        have hd : sig.declOf w = sortOf[c]?.getD 0 := by simp [Sig.declOf, tc]
        simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil, hd]
        exact sortChain_snoc ih hs
      · cases tF
    · cases h

end Vik.Low
