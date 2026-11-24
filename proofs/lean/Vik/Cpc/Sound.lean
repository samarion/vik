import Vik.Cpc.Check

/-!
# Soundness of the CPC checker

Every fact a checked proof derives holds in every model of the script's
assertions, under the assumptions of the scopes open; a proof the checker
accepts derives `false`, so no model satisfies the script (`Proof.unsat`).
-/

set_option linter.unusedSectionVars false

namespace Vik.Cpc

open Lean.Grind Vik.Real Vik.Surf Vik.Clausal
open Vik.Low (Val get truth_iff)

variable {R U : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R]
  [OrderedRing R] [IsCharP R 0]

/-- The arguments of a use of a definition are in the domains of its
    parameters' sorts. -/
theorem def_args_dom' {M : Surf.Model R U} {decls sortOf : List Nat} {f : Nat → Val R U} :
    ∀ (ps args : List Nat), ps.length = args.length →
      (∀ q ∈ ps.zip args, decls.getD q.1 0 = sortOf.getD q.2 0) →
      (∀ a ∈ args, M.dom (sortOf[a]?.getD 0) (f a)) →
      Vik.Low.Forall2 M.dom (ps.map fun p => decls.getD p 0) (args.map f)
  | [], [], _, _, _ => trivial
  | p :: ps, a :: args, hl, hs, hd => by
    refine ⟨?_, def_args_dom' ps args (by simpa using hl) (fun q m => hs q (by simp [m]))
      (fun b m => hd b (by simp [m]))⟩
    have e := hs (p, a) (by simp)
    simp only at e
    show M.dom (decls.getD p 0) (f a)
    rw [e, List.getD_eq_getElem?_getD]
    exact hd a (by simp)
  | [], _ :: _, hl, _, _ => by simp at hl
  | _ :: _, [], hl, _, _ => by simp at hl

theorem map_eq_of_zip {α β : Type} (f : α → β) :
    ∀ (as bs : List α), as.length = bs.length → (∀ p ∈ as.zip bs, f p.1 = f p.2) → as.map f = bs.map f
  | [], [], _, _ => rfl
  | a :: as, b :: bs, hl, h => by
    simp only [List.zip_cons_cons, List.mem_cons, forall_eq_or_imp] at h
    simp only [List.map_cons, h.1, map_eq_of_zip f as bs (by simpa using hl) h.2]
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

/-- Nodes of one shape take the same value when their children do. -/
theorem evalNode_kids (I : Surf.Interp R U) (vals : List (Val R U)) {n m : SNode} {k : Nat} {as bs : List Nat}
    (hn : kids n = some (k, as)) (hm : kids m = some (k, bs)) (h : as.map (get vals) = bs.map (get vals)) :
    Surf.evalNode I vals n = Surf.evalNode I vals m := by
  have tr : ∀ (xs ys : List Nat), xs.map (get vals) = ys.map (get vals) →
      xs.map (fun a => (get vals a).truth) = ys.map (fun a => (get vals a).truth) := by
    intro xs ys e
    have := congrArg (List.map Val.truth) e
    simpa [List.map_map] using this
  cases n <;> simp only [kids, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hn <;>
    cases m <;> simp only [kids, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hm <;>
    obtain ⟨rfl, rfl⟩ := hn <;> obtain ⟨hk, rfl⟩ := hm <;> simp at hk <;> simp only [Surf.evalNode]
  case app.app f as g bs =>
    simp only [List.map_cons, List.cons.injEq] at h
    rw [h.1, h.2]
  case not.not a b =>
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
    rw [h]
  case and.and xs ys =>
    have e := tr _ _ h
    have r : ∀ l : List Nat, (l.all fun a => (get vals a).truth) = (l.map fun a => (get vals a).truth).all id := by
      intro l; simp [List.all_map]
    rw [r xs, r ys, e]
  case or.or xs ys =>
    have e := tr _ _ h
    have r : ∀ l : List Nat, (l.any fun a => (get vals a).truth) = (l.map fun a => (get vals a).truth).any id := by
      intro l; simp [List.any_map]
    rw [r xs, r ys, e]
  case implies.implies => rw [tr _ _ h]
  case iff.iff => rw [tr _ _ h]
  case eq.eq => rw [h]
  case xor.xor => rw [tr _ _ h]
  case distinct.distinct => rw [h]
  case ite.ite =>
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
    rw [h.1, h.2.1, h.2.2]

theorem xorL_snoc : ∀ (l : List Bool) (b : Bool), l ≠ [] → xorL (l ++ [b]) = (xorL l != b)
  | a :: rest, b, _ => by simp [xorL, List.foldl_append]

theorem pairwise_pairsOf {α : Type} (r : α → α → Prop) (f : Nat → α) :
    ∀ as : List Nat, pairwiseP r (as.map f) ↔ ∀ p ∈ pairsOf as, r (f p.1) (f p.2)
  | [] => by simp [pairwiseP, pairsOf]
  | a :: rest => by
    simp only [List.map_cons, pairwiseP, pairsOf, List.mem_append, pairwise_pairsOf r f rest]
    constructor
    · rintro ⟨h1, h2⟩ p (hp | hp)
      · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hp
        exact h1 _ (List.mem_map.mpr ⟨b, hb, rfl⟩)
      · exact h2 p hp
    · intro h
      refine ⟨fun x hx => ?_, fun p hp => h p (Or.inr hp)⟩
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
      exact h (a, b) (Or.inl (List.mem_map.mpr ⟨b, hb, rfl⟩))

theorem pairsOk_sound {V : Nat → Val R U} {eqvs : List Eqv} {k : Nat}
    (hprev : ∀ j < k, ∀ e, Tab.at eqvs j = some e → V e.x = V e.y) :
    ∀ (ps : List (Nat × Nat)) (hs : List Nat), pairsOk eqvs k ps hs = true → ∀ p ∈ ps, V p.1 = V p.2
  | [], _, _ => by simp
  | (p, q) :: ps, hs, h => by
    simp only [pairsOk] at h
    split at h
    · rename_i e
      simp only [beq_iff_eq] at e; subst e
      intro r hr
      simp only [List.mem_cons] at hr
      rcases hr with rfl | hr
      · rfl
      · exact pairsOk_sound hprev ps hs h r hr
    · split at h
      · rename_i h' hs'
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨hk, he⟩, hrest⟩ := h
        split at he
        · rename_i e hhe
          simp only [Bool.and_eq_true, beq_iff_eq] at he
          intro r hr
          simp only [List.mem_cons] at hr
          rcases hr with rfl | hr
          · have := hprev h' hk e hhe; rw [he.1, he.2] at this; exact this
          · exact pairsOk_sound hprev ps hs' hrest r hr
        · cases he
      · cases h

theorem viaEqv_sound {V : Nat → Val R U} {eqvs : List Eqv}
    (hE : ∀ j e, Tab.at eqvs j = some e → V e.x = V e.y) {x y : Nat} {e : Option Nat}
    (h : viaEqv eqvs x y e = true) : V x = V y := by
  cases e with
  | none => simp only [viaEqv, beq_iff_eq] at h; rw [h]
  | some j =>
    simp only [viaEqv] at h
    split at h
    · rename_i q hq
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      have := hE j q hq; rw [h.1, h.2] at this; exact this
    · cases h
theorem zip3_mem {α β : Type} (P : α → β → Prop) :
    ∀ (ks : List α) (ps : List β), ks.length = ps.length → (∀ q ∈ ks.zip ps, P q.1 q.2) → ∀ p ∈ ps, ∃ k, P k p
  | [], [], _, _, p, hp => by simp at hp
  | k :: ks, p :: ps, hl, h, q, hq => by
    simp only [List.zip_cons_cons, List.mem_cons, forall_eq_or_imp] at h hq
    rcases hq with rfl | hq
    · exact ⟨k, h.1⟩
    · exact zip3_mem P ks ps (by simpa using hl) h.2 q hq
  | [], _ :: _, hl, _, _, _ => by simp at hl
  | _ :: _, [], hl, _, _, _ => by simp at hl

theorem zip_left_mem {α β : Type} : ∀ (as : List α) (bs : List β), as.length = bs.length →
    ∀ a ∈ as, ∃ b, (a, b) ∈ as.zip bs
  | x :: as, y :: bs, hl, a, ha => by
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact ⟨y, by simp⟩
    · obtain ⟨b, hb⟩ := zip_left_mem as bs (by simpa using hl) a ha
      exact ⟨b, by simp [hb]⟩
  | [], _, _, a, ha => by simp at ha
  | _ :: _, [], hl, _, _ => by simp at hl

theorem Trie.get_leaf (j : Nat) : Trie.leaf.get j = none := by cases j <;> rfl

theorem Trie.get_single : ∀ (f n b : Nat), n < f → ∀ j, (Trie.single f n b).get j = if j = n then some b else none
  | 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | f + 1, 0, b, _, j => by
    cases j with
    | zero => rfl
    | succ j => simp [Trie.single, Trie.get]
  | f + 1, n + 1, b, h, j => by
    cases j with
    | zero => simp only [Trie.single]; split <;> simp [Trie.get]
    | succ j =>
      have ih := Trie.get_single f (n / 2) b (by omega)
      simp only [Trie.single, Nat.add_right_cancel_iff]
      by_cases hn : n % 2 = 0 <;> by_cases hj : j % 2 = 0 <;>
        simp only [hn, hj, beq_iff_eq, if_true, if_false, Trie.get, ih, not_false_eq_true]
      · simp only [TT.half_iff (show j % 2 = n % 2 by omega)]
      · have : j ≠ n := by omega
        simp [this]
      · have : j ≠ n := by omega
        simp [this]
      · simp only [TT.half_iff (show j % 2 = n % 2 by omega)]

theorem Trie.get_set : ∀ (t : Trie) (k b j : Nat), (t.set k b).get j = if j = k then some b else t.get j
  | .leaf, k, b, j => by
    simp only [Trie.set, Trie.get_leaf]
    exact Trie.get_single (k + 1) k b (Nat.lt_succ_self k) j
  | .node v l r, 0, b, j => by
    cases j with
    | zero => rfl
    | succ j => simp [Trie.set, Trie.get]
  | .node v l r, k + 1, b, j => by
    cases j with
    | zero => simp only [Trie.set]; split <;> simp [Trie.get]
    | succ j =>
      simp only [Trie.set, Nat.add_right_cancel_iff]
      by_cases hk : k % 2 = 0 <;> by_cases hj : j % 2 = 0 <;>
        simp only [hk, hj, beq_iff_eq, if_true, if_false, Trie.get, Trie.get_set, not_false_eq_true]
      · simp only [TT.half_iff (show j % 2 = k % 2 by omega)]
      · have : j ≠ k := by omega
        simp [this]
      · have : j ≠ k := by omega
        simp [this]
      · simp only [TT.half_iff (show j % 2 = k % 2 by omega)]

theorem optAll_mem : ∀ (xs : List (Option Nat)) (ys : List Nat), optAll xs = some ys → ∀ y ∈ ys, some y ∈ xs
  | [], ys, h, y, hy => by simp only [optAll, Option.some.injEq] at h; subst h; simp at hy
  | x :: xs, ys, h, y, hy => by
    simp only [optAll, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, rfl, ys', h', rfl⟩ := h
    simp only [List.mem_cons] at hy ⊢
    rcases hy with rfl | hy
    · exact Or.inl rfl
    · exact Or.inr (optAll_mem xs ys' h' y hy)

theorem val_append {I : Surf.Interp R U} {A B : List SNode} {i : Nat} (hi : i < A.length) :
    Surf.val I (A ++ B) i = Surf.val I A i := by
  unfold Surf.val Surf.values Low.get
  rw [List.foldl_append]
  congr 1
  have hl := values_length I A
  unfold values at hl
  rw [Surf.values_prefix I B _ i (by rw [hl]; exact hi)]

section
variable {c : Ctx} {M : Surf.Model R U}

/-- The value of node `i`. -/
noncomputable def Ctx.V (c : Ctx) (M : Surf.Model R U) (i : Nat) : Val R U := Surf.val M.toInterp c.nodes i

/-- Node `i` holds. -/
def Ctx.H (c : Ctx) (M : Surf.Model R U) (i : Nat) : Prop := Surf.holds M.toInterp c.nodes i

theorem Ctx.H_def {i : Nat} : c.H M i ↔ c.V M i = .bool true := Iff.rfl

variable (hw : wellFormed c.nodes = true)
include hw

theorem Ctx.V_node {i : Nat} {n : SNode} (h : c.node i = some n) :
    c.V M i = Surf.evalNode M.toInterp (Surf.values M.toInterp c.nodes) n := by
  simp only [Ctx.node, Tab.at_eq] at h
  exact Surf.val_node hw h

theorem Ctx.H_not {i a : Nat} (h : c.node i = some (.not a)) : c.H M i ↔ ¬c.H M a := by
  rw [Ctx.H_def, c.V_node hw h]
  simp only [Surf.evalNode]
  simp [Ctx.H, Ctx.V, Surf.holds, Surf.val, Val.truth]

theorem Ctx.H_and {i : Nat} {as : List Nat} (h : c.node i = some (.and as)) : c.H M i ↔ ∀ a ∈ as, c.H M a := by
  rw [Ctx.H_def, c.V_node hw h]
  simp only [Surf.evalNode]
  simp [Ctx.H, Ctx.V, Surf.holds, Surf.val, Val.truth]

theorem Ctx.H_or {i : Nat} {as : List Nat} (h : c.node i = some (.or as)) : c.H M i ↔ ∃ a ∈ as, c.H M a := by
  rw [Ctx.H_def, c.V_node hw h]
  simp only [Surf.evalNode]
  simp [Ctx.H, Ctx.V, Surf.holds, Surf.val, Val.truth]

theorem Ctx.H_tt {i : Nat} (h : c.node i = some .tt) : c.H M i := by
  rw [Ctx.H_def, c.V_node hw h]
  simp only [Surf.evalNode]

theorem Ctx.H_ff {i : Nat} (h : c.node i = some .ff) : ¬c.H M i := by
  rw [Ctx.H_def, c.V_node hw h]
  simp only [Surf.evalNode]; simp

theorem Ctx.V_tt {i : Nat} (h : c.node i = some .tt) : c.V M i = .bool true := by
  simp only [c.V_node hw h, Surf.evalNode]

theorem Ctx.V_ff {i : Nat} (h : c.node i = some .ff) : c.V M i = .bool false := by
  simp only [c.V_node hw h, Surf.evalNode]

theorem Ctx.H_iff {i a b : Nat} (h : c.node i = some (.iff [a, b])) : c.H M i ↔ (c.H M a ↔ c.H M b) := by
  rw [Ctx.H_def, c.V_node hw h]
  simp only [Surf.evalNode, List.map, chainP, and_true, Val.bool.injEq,
    decide_eq_true_iff]
  simp only [Ctx.H, Ctx.V, Surf.holds, Surf.val, Val.truth]
  by_cases ha : Low.get (Surf.values M.toInterp c.nodes) a = .bool true <;>
    by_cases hb : Low.get (Surf.values M.toInterp c.nodes) b = .bool true <;> simp [ha, hb]

theorem Ctx.H_eq {i a b : Nat} (h : c.node i = some (.eq [a, b])) : c.H M i ↔ c.V M a = c.V M b := by
  rw [Ctx.H_def, c.V_node hw h]
  simp only [Surf.evalNode, List.map, chainP, and_true, Val.bool.injEq,
    decide_eq_true_iff]
  rfl

theorem Ctx.H_implies {i a b : Nat} (h : c.node i = some (.implies [a, b])) :
    c.H M i ↔ (c.H M a → c.H M b) := by
  rw [Ctx.H_def, c.V_node hw h]
  simp only [Surf.evalNode, List.map, impliesR, Val.bool.injEq]
  simp only [Ctx.H, Ctx.V, Surf.holds, Surf.val, Val.truth]
  by_cases ha : Low.get (Surf.values M.toInterp c.nodes) a = .bool true <;>
    by_cases hb : Low.get (Surf.values M.toInterp c.nodes) b = .bool true <;> simp [ha, hb]

open Classical in
theorem Ctx.V_ite {i x a b : Nat} (h : c.node i = some (.ite x a b)) :
    c.V M i = if c.H M x then c.V M a else c.V M b := by
  rw [c.V_node hw h]
  simp only [Surf.evalNode]
  by_cases hx : c.H M x
  · rw [if_pos hx, if_pos (show (Low.get (Surf.values M.toInterp c.nodes) x).truth = true from (truth_iff _).mpr hx)]
    rfl
  · rw [if_neg hx, if_neg (show ¬(Low.get (Surf.values M.toInterp c.nodes) x).truth = true from
      fun e => hx ((truth_iff _).mp e))]
    rfl

theorem Ctx.H_ite {i x a b : Nat} (h : c.node i = some (.ite x a b)) :
    c.H M i ↔ (c.H M x ∧ c.H M a) ∨ (¬c.H M x ∧ c.H M b) := by
  rw [Ctx.H_def, c.V_ite hw h]
  by_cases hx : c.H M x
  · rw [if_pos hx]; simp [hx, Ctx.H_def]
  · rw [if_neg hx]; simp [hx, Ctx.H_def]

theorem Ctx.H_clause (i : Nat) : c.H M i ↔ ∃ l ∈ c.clause i, c.H M l := by
  unfold Ctx.clause
  split
  · rename_i as h; exact c.H_or hw h
  · rename_i h; simp only [List.not_mem_nil, false_and, exists_false, iff_false]; exact c.H_ff hw h
  · simp

theorem Ctx.H_sgn : ∀ (fuel l : Nat), c.H M l ↔ (c.H M (c.sgn fuel l).1 ↔ (c.sgn fuel l).2 = true)
  | 0, l => by simp [Ctx.sgn]
  | fuel + 1, l => by
    simp only [Ctx.sgn]
    split
    · rename_i a ha
      have ha' : c.node l = some (.not a) := by
        simp only [Ctx.notOf] at ha; split at ha <;> simp_all
      split
      · rename_i b hb
        have hb' : c.node a = some (.not b) := by
          simp only [Ctx.notOf] at hb; split at hb <;> simp_all
        rw [← Ctx.H_sgn fuel b, c.H_not hw ha', c.H_not hw hb', not_not]
      · simp only [Bool.false_eq_true, iff_false]; exact c.H_not hw ha'
    · simp

theorem Ctx.lt_of_node {i : Nat} {n : SNode} (h : c.node i = some n) : i < c.nodes.length := by
  simp only [Ctx.node, Tab.at_eq] at h
  rcases Nat.lt_or_ge i c.nodes.length with h' | h'
  · exact h'
  · rw [List.getElem?_eq_none h'] at h; cases h

/-! ## Sorts -/

variable (ht : typed c.sig c.nodes c.sortOf = true) (hM : M.Sound c.sig)
include ht hM

theorem Ctx.bool_val {i : Nat} (hb : c.isBool i = true) : ∃ b, c.V M i = .bool b := by
  rcases Nat.lt_or_ge i c.nodes.length with hi | hi
  · have hd := val_dom hM hw ht i hi
    simp only [Ctx.isBool, Tab.at_eq, SSig.is, beq_iff_eq] at hb
    exact (hM.bool _ _ hb).mp hd
  · refine ⟨false, ?_⟩
    simp only [Ctx.V, Surf.val, Low.get]
    rw [List.getElem?_eq_none (by rw [values_length]; exact hi)]
    rfl

/-- The children of a connective are Booleans. -/
theorem Ctx.bool_kids {i : Nat} {n : SNode} (h : c.node i = some n) :
    ∀ a ∈ (match n with
      | .not a => [a]
      | .and as | .or as | .implies as | .iff as | .xor as => as
      | _ => []), c.isBool a = true := by
  have hi := c.lt_of_node hw h
  have ht' := ht
  simp only [typed, Tab.at_eq, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at ht'
  have hn := ht'.2 i hi
  simp only [Ctx.node, Tab.at_eq] at h
  rw [h] at hn
  intro a ha
  simp only [Ctx.isBool]
  cases n <;> simp only [List.not_mem_nil] at ha <;>
    simp only [nodeTyped, Bool.and_eq_true, List.all_eq_true] at hn
  all_goals first
    | (simp only [List.mem_singleton] at ha; subst ha; exact hn.2)
    | exact hn.2 a ha

theorem Ctx.H_iff_V {a b : Nat} (ha : c.isBool a = true) (hb : c.isBool b = true) :
    (c.H M a ↔ c.H M b) ↔ c.V M a = c.V M b := by
  obtain ⟨x, hx⟩ := c.bool_val hw ht hM ha
  obtain ⟨y, hy⟩ := c.bool_val hw ht hM hb
  simp only [Ctx.H_def, hx, hy, Val.bool.injEq]
  cases x <;> cases y <;> simp

theorem Ctx.H_eqOf {i a b : Nat} (h : c.eqOf i = some (a, b)) : c.H M i ↔ c.V M a = c.V M b := by
  simp only [Ctx.eqOf, Option.bind_eq_some_iff] at h
  obtain ⟨n, hn, he⟩ := h
  unfold eqArgs at he
  split at he
  · simp only [Option.some.injEq, Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he; exact c.H_eq hw hn
  · simp only [Option.some.injEq, Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    have hk := c.bool_kids hw ht hM hn
    rw [c.H_iff hw hn]
    exact c.H_iff_V hw ht hM (hk _ (by simp)) (hk _ (by simp))
  · cases he

/-! ## Equivalences -/

theorem Ctx.same_sound {x y : Nat} {n m : SNode} (hx : c.node x = some n) (hy : c.node y = some m)
    {ps : List (Nat × Nat)} (h : samePairs n m = some ps) (hp : ∀ p ∈ ps, c.V M p.1 = c.V M p.2) :
    c.V M x = c.V M y := by
  unfold samePairs at h
  split at h
  · rename_i k as k' bs hn hm
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨rfl, hl⟩ := hc
      simp only [Option.some.injEq] at h
      subst h
      rw [c.V_node hw hx, c.V_node hw hy]
      exact evalNode_kids _ _ hn hm (map_eq_of_zip _ as bs hl (fun p m => hp p m))
    · cases h
  · cases h

theorem Ctx.truthV_eq {a b : Nat} (h : c.V M a = c.V M b) :
    (get (Surf.values M.toInterp c.nodes) a).truth = (get (Surf.values M.toInterp c.nodes) b).truth := by
  have : c.V M a = get (Surf.values M.toInterp c.nodes) a := rfl
  have h' : c.V M b = get (Surf.values M.toInterp c.nodes) b := rfl
  rw [← this, ← h', h]

theorem Ctx.chain_eq_sound : ∀ (as es : List Nat) (ps : List (Nat × Nat)), c.chainPairs true as es = some ps →
    (∀ p ∈ ps, c.V M p.1 = c.V M p.2) →
    (chainP (· = ·) (as.map (get (Surf.values M.toInterp c.nodes))) ↔ ∀ e ∈ es, c.H M e)
  | a :: b :: rest, e :: es, ps, h, hp => by
    simp only [Ctx.chainPairs] at h
    split at h
    · rename_i p q he
      simp only [if_true, Option.map_eq_some_iff] at h
      obtain ⟨ps', h', rfl⟩ := h
      simp only [List.cons_append, List.nil_append, List.mem_cons, forall_eq_or_imp] at hp
      have ih := chain_eq_sound (b :: rest) es ps' h' hp.2.2
      simp only [List.map_cons, chainP, List.mem_cons, forall_eq_or_imp] at ih ⊢
      rw [ih, c.H_eq hw he]
      have e1 : get (Surf.values M.toInterp c.nodes) a = c.V M p := hp.1
      have e2 : get (Surf.values M.toInterp c.nodes) b = c.V M q := hp.2.1
      rw [e1, e2]
    · simp at h
    · cases h
  | [_], [], _, _, _ => by simp [chainP]
  | [], _, _, h, _ => by simp [Ctx.chainPairs] at h
  | [_], _ :: _, _, h, _ => by simp [Ctx.chainPairs] at h
  | _ :: _ :: _, [], _, h, _ => by simp [Ctx.chainPairs] at h

theorem Ctx.chain_iff_sound : ∀ (as es : List Nat) (ps : List (Nat × Nat)), c.chainPairs false as es = some ps →
    (∀ p ∈ ps, c.V M p.1 = c.V M p.2) →
    (chainP (· = ·) (as.map fun a => (get (Surf.values M.toInterp c.nodes) a).truth) ↔ ∀ e ∈ es, c.H M e)
  | a :: b :: rest, e :: es, ps, h, hp => by
    simp only [Ctx.chainPairs] at h
    split at h
    · simp at h
    · rename_i p q he
      simp only [Bool.false_eq_true, if_false, Option.map_eq_some_iff] at h
      obtain ⟨ps', h', rfl⟩ := h
      simp only [List.cons_append, List.nil_append, List.mem_cons, forall_eq_or_imp] at hp
      have ih := chain_iff_sound (b :: rest) es ps' h' hp.2.2
      simp only [List.map_cons, chainP, List.mem_cons, forall_eq_or_imp] at ih ⊢
      rw [ih, c.H_iff hw he, c.truthV_eq hw ht hM hp.1, c.truthV_eq hw ht hM hp.2.1]
      simp only [Ctx.H_def, Ctx.V, Surf.val, ← truth_iff]
      cases (get (Surf.values M.toInterp c.nodes) p).truth <;>
        cases (get (Surf.values M.toInterp c.nodes) q).truth <;> simp
    · cases h
  | [_], [], _, _, _ => by simp [chainP]
  | [], _, _, h, _ => by simp [Ctx.chainPairs] at h
  | [_], _ :: _, _, h, _ => by simp [Ctx.chainPairs] at h
  | _ :: _ :: _, [], _, h, _ => by simp [Ctx.chainPairs] at h

theorem Ctx.impl_sound : ∀ (as : List Nat) (y : Nat) (ps : List (Nat × Nat)), c.implPairs as y = some ps →
    (∀ p ∈ ps, c.V M p.1 = c.V M p.2) →
    c.V M y = .bool (impliesR (as.map fun a => (get (Surf.values M.toInterp c.nodes) a).truth))
  | [a, b], y, ps, h, hp => by
    simp only [Ctx.implPairs] at h
    split at h
    · rename_i p q hy
      simp only [Option.some.injEq] at h; subst h
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hp
      rw [c.V_node hw hy]
      simp only [Surf.evalNode, List.map, impliesR, c.truthV_eq hw ht hM hp.1, c.truthV_eq hw ht hM hp.2]
    · cases h
  | a :: b :: d :: rest, y, ps, h, hp => by
    simp only [Ctx.implPairs] at h
    split at h
    · rename_i p z hy
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨ps', h', rfl⟩ := h
      simp only [List.mem_cons, forall_eq_or_imp] at hp
      have ih := impl_sound (b :: d :: rest) z ps' h' hp.2
      rw [c.V_node hw hy]
      simp only [Surf.evalNode, List.map, c.truthV_eq hw ht hM hp.1]
      have : (get (Surf.values M.toInterp c.nodes) z).truth = impliesR (List.map
          (fun a => (get (Surf.values M.toInterp c.nodes) a).truth) (b :: d :: rest)) := by
        have e : get (Surf.values M.toInterp c.nodes) z = c.V M z := rfl
        rw [e, ih]; simp [Val.truth]
      simp only [List.map] at this
      rw [this]
      rfl
    · cases h
  | [], _, _, h, _ => by simp [Ctx.implPairs] at h
  | [_], _, _, h, _ => by simp [Ctx.implPairs] at h

theorem Ctx.xor_sound : ∀ (rs : List Nat) (y : Nat) (ps : List (Nat × Nat)), c.xorPairs rs y = some ps →
    (∀ p ∈ ps, c.V M p.1 = c.V M p.2) →
    c.V M y = .bool (xorL (rs.reverse.map fun a => (get (Surf.values M.toInterp c.nodes) a).truth))
  | [b, a], y, ps, h, hp => by
    simp only [Ctx.xorPairs] at h
    split at h
    · rename_i p q hy
      simp only [Option.some.injEq] at h; subst h
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hp
      rw [c.V_node hw hy]
      simp only [Surf.evalNode, List.map, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.cons_append, xorL, List.foldl]
      rw [c.truthV_eq hw ht hM hp.1, c.truthV_eq hw ht hM hp.2]
    · cases h
  | b :: x :: d :: rest, y, ps, h, hp => by
    simp only [Ctx.xorPairs] at h
    split at h
    · rename_i z q hy
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨ps', h', rfl⟩ := h
      simp only [List.mem_cons, forall_eq_or_imp] at hp
      have ih := xor_sound (x :: d :: rest) z ps' h' hp.2
      rw [c.V_node hw hy]
      have hz : (get (Surf.values M.toInterp c.nodes) z).truth = xorL (List.map
          (fun a => (get (Surf.values M.toInterp c.nodes) a).truth) (x :: d :: rest).reverse) := by
        have e : get (Surf.values M.toInterp c.nodes) z = c.V M z := rfl
        rw [e, ih]; simp [Val.truth]
      have hq := (c.truthV_eq hw ht hM hp.1).symm
      simp only [Surf.evalNode, List.map]
      rw [List.reverse_cons, List.map_append, List.map_cons, List.map_nil, xorL_snoc _ _ (by simp [List.map_eq_nil_iff, List.reverse_eq_nil_iff]), ← hz,
        hq]
      simp [xorL]
    · cases h
  | [], _, _, h, _ => by simp [Ctx.xorPairs] at h
  | [_], _, _, h, _ => by simp [Ctx.xorPairs] at h

theorem Ctx.diseq_sound : ∀ (qs : List (Nat × Nat)) (es : List Nat) (ps : List (Nat × Nat)),
    c.diseqPairs qs es = some ps → (∀ p ∈ ps, c.V M p.1 = c.V M p.2) →
    ((∀ q ∈ qs, c.V M q.1 ≠ c.V M q.2) ↔ ∀ e ∈ es, c.H M e)
  | (a, b) :: qs, e :: es, ps, h, hp => by
    simp only [Ctx.diseqPairs] at h
    split at h
    · rename_i p q hd
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨ps', h', rfl⟩ := h
      simp only [List.mem_cons, forall_eq_or_imp] at hp
      have ih := diseq_sound qs es ps' h' hp.2.2
      simp only [List.mem_cons, forall_eq_or_imp]
      rw [ih]
      simp only [Ctx.diseq, Option.bind_eq_some_iff] at hd
      obtain ⟨f, hf, hfe⟩ := hd
      have hn : c.node e = some (.not f) := by
        simp only [Ctx.notOf] at hf; split at hf <;> simp_all
      rw [c.H_not hw hn, c.H_eqOf hw ht hM hfe, ← hp.1, ← hp.2.1]
    · cases h
  | [], [], _, _, _ => by simp
  | [], _ :: _, _, h, _ => by simp [Ctx.diseqPairs] at h
  | _ :: _, [], _, h, _ => by simp [Ctx.diseqPairs] at h

open Classical in
theorem Ctx.eqvPairs_sound {x y : Nat} {ps : List (Nat × Nat)} (h : c.eqvPairs x y = some ps)
    (hp : ∀ p ∈ ps, c.V M p.1 = c.V M p.2) : c.V M x = c.V M y := by
  unfold Ctx.eqvPairs at h
  split at h
  next _ _ _ b hx =>
    simp only [Option.some.injEq] at h; subst h
    rw [c.V_node hw hx]; exact hp (_, y) (by simp)
  next _ _ d hx =>
    simp only [Option.some.injEq] at h; subst h
    rw [c.V_node hw hx]; exact hp (_, y) (by simp)
  next _ _ hx hy =>
    rw [c.V_node hw hx, c.V_node hw hy]; rfl
  next _ _ hx hy =>
    rw [c.V_node hw hx, c.V_node hw hy]; rfl
  next _ _ a1 a2 a3 tl es hx hy =>
    rw [c.V_node hw hx, c.V_node hw hy]
    simp only [Surf.evalNode, Val.bool.injEq]
    have e := c.chain_eq_sound hw ht hM _ es ps h hp
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq]
    rw [e]
    simp [List.all_eq_true, Ctx.H_def, Ctx.V, Surf.val, truth_iff]
  next _ _ a1 a2 a3 tl es hx hy =>
    rw [c.V_node hw hx, c.V_node hw hy]
    simp only [Surf.evalNode, Val.bool.injEq]
    have e := c.chain_iff_sound hw ht hM _ es ps h hp
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq]
    rw [e]
    simp [List.all_eq_true, Ctx.H_def, Ctx.V, Surf.val, truth_iff]
  next _ _ a1 a2 a3 tl hx =>
    rw [c.V_node hw hx, c.impl_sound hw ht hM _ y ps h hp]; rfl
  next _ _ a1 a2 a3 tl hx =>
    rw [c.V_node hw hx, c.xor_sound hw ht hM _ y ps h hp, List.reverse_reverse]; rfl
  next _ _ a b e hx hy =>
    split at h
    next p q he =>
      simp only [Option.some.injEq] at h; subst h
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hp
      rw [c.V_node hw hx, c.V_node hw hy]
      have hv : c.V M e = Val.bool (decide (chainP (· = ·)
          [(get (Surf.values M.toInterp c.nodes) p).truth, (get (Surf.values M.toInterp c.nodes) q).truth])) := by
        rw [c.V_node hw he]; rfl
      simp only [Surf.evalNode, List.map, xorL, List.foldl, c.truthV_eq hw ht hM hp.1, c.truthV_eq hw ht hM hp.2]
      have : (get (Surf.values M.toInterp c.nodes) e) = c.V M e := rfl
      rw [this, hv]
      cases (get (Surf.values M.toInterp c.nodes) p).truth <;>
        cases (get (Surf.values M.toInterp c.nodes) q).truth <;> simp [Val.truth, chainP]
    next => cases h
  next _ _ as es hx hy =>
    split at h
    next =>
      rw [c.V_node hw hx, c.V_node hw hy]
      simp only [Surf.evalNode, Val.bool.injEq]
      have e := c.diseq_sound hw ht hM (pairsOf as) es ps h hp
      rw [Bool.eq_iff_iff]
      simp only [decide_eq_true_eq]
      rw [pairwise_pairsOf _ (Low.get (Surf.values M.toInterp c.nodes))]
      rw [show (∀ p ∈ pairsOf as, get (Surf.values M.toInterp c.nodes) p.1 ≠ get (Surf.values M.toInterp c.nodes) p.2) ↔
          ∀ p ∈ pairsOf as, c.V M p.1 ≠ c.V M p.2 from Iff.rfl, e]
      simp [List.all_eq_true, Ctx.H_def, Ctx.V, Surf.val, truth_iff]
    next => cases h
  next =>
    rename_i hx hy
    exact c.same_sound hw ht hM hx hy h hp
  next => cases h

theorem Ctx.defUse_sound {x k : Nat} {as : List Nat} {isApp : Bool} (h : c.defUse x = some (k, as, isApp)) :
    c.V M x = (if isApp then M.app (M.const k) (as.map (c.V M)) else M.const k) ∧ (∀ a ∈ as, a < x) ∧
      x < c.nodes.length := by
  unfold Ctx.defUse at h
  split at h
  next k' hx =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    refine ⟨?_, by simp, c.lt_of_node hw hx⟩
    rw [c.V_node hw hx]; rfl
  next f as' hx =>
    split at h
    next k' hf =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      have hxl := c.lt_of_node hw hx
      refine ⟨?_, ?_, hxl⟩
      · rw [c.V_node hw hx, if_pos rfl]
        show M.app (get _ f) _ = _
        rw [show get (Surf.values M.toInterp c.nodes) f = c.V M f from rfl, c.V_node hw hf]
        rfl
      · intro a ha
        have := List.all_eq_true.mp hw x (List.mem_range.mpr hxl)
        simp only [Ctx.node] at hx
        rw [hx] at this
        have hm : a ∈ (SNode.app f as').children := by simp [SNode.children, ha]
        simpa using (List.all_eq_true.mp this) a hm
    next => cases h
  next => cases h

theorem Ctx.defPairs_sound {defs : List SDef} (hD : ∀ d ∈ defs, d.Holds c.sig M) {x y : Nat} {ms : List Nat}
    {ps : List (Nat × Nat)} (h : c.defPairs defs x y ms = some ps)
    (hp : ∀ p ∈ ps, c.V M p.1 = c.V M p.2) : c.V M x = c.V M y := by
  unfold Ctx.defPairs at h
  split at h
  next k as isApp hu =>
    split at h
    next d hd =>
      split at h
      next hc =>
        simp only [Option.some.injEq] at h; subst h
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at hc
        obtain ⟨⟨⟨⟨⟨hap, hlen⟩, hwd⟩, hroot⟩, hsorts⟩, hinst⟩ := hc
        obtain ⟨hx, has, hxl⟩ := c.defUse_sound hw ht hM hu
        have hdm := List.mem_of_find?_eq_some hd
        have hsym : d.sym = k := beq_iff_eq.mp (List.find?_some (p := fun x : SDef => x.sym == k) hd)
        have hfa := def_args_dom' (M := M) (decls := c.sig.decls) (sortOf := c.sortOf) (f := c.V M) d.params as hlen
          (fun q m => by simpa using hsorts q m)
          (fun a m => Surf.val_dom hM hw ht a (by have := has a m; omega))
        have hH : _ = Surf.val (M.toInterp.bind d.params (as.map (Surf.val M.toInterp c.nodes))) d.nodes d.root :=
          hD d hdm (as.map (c.V M)) hfa
        have hi := Surf.inst_val M.toInterp hw hwd hinst d.root hroot
        rw [hx, ← hp (ms.getD d.root 0, y) (by simp)]
        show _ = Surf.val M.toInterp c.nodes (ms.getD d.root 0)
        rw [hi, ← hH, hsym]
        cases isApp with
        | true =>
          have hne : d.params ≠ [] := by
            intro e; rw [e] at hap; simp at hap
          rw [if_neg hne, if_pos rfl]
        | false =>
          have he : d.params = [] := by
            cases e : d.params with
            | nil => rfl
            | cons _ _ => rw [e] at hap; simp at hap
          rw [if_pos he]; rfl
      next => cases h
    next => cases h
  next => cases h

theorem Ctx.eqvs_sound {defs : List SDef} (hD : ∀ d ∈ defs, d.Holds c.sig M) {eqvs : List Eqv}
    (h : c.eqvsOk defs eqvs = true) :
    ∀ j e, Tab.at eqvs j = some e → c.V M e.x = c.V M e.y := by
  intro j
  induction j using Nat.strongRecOn with
  | ind j ih =>
  intro e he
  have hj : j < eqvs.length := by
    simp only [Tab.at_eq] at he
    rcases Nat.lt_or_ge j eqvs.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at he; cases he
  have hok := List.all_eq_true.mp h j (List.mem_range.mpr hj)
  simp only [Ctx.eqvOk, he] at hok
  split at hok
  · rename_i ps hps
    have hp := pairsOk_sound (fun j' hj' e' he' => ih j' hj' e' he') ps e.hs hok
    split at hps
    · exact c.eqvPairs_sound hw ht hM hps hp
    · exact c.defPairs_sound hw ht hM hD hps hp
  · cases hok


/-! ## Reverse unit propagation -/

open Classical in
/-- The assignment of the atoms that the model gives. -/
noncomputable def Ctx.rho (c : Ctx) (M : Surf.Model R U) : Assignment := fun a => decide (c.H M a)

theorem Ctx.litVal_sound {t : TT} (hA : t.Agrees (c.rho M)) {l : Nat} {b : Bool} (h : c.litVal t l = some b) :
    c.H M l ↔ b = true := by
  simp only [Ctx.litVal] at h
  have hs := c.H_sgn hw (M := M) sgnFuel l
  generalize c.sgn sgnFuel l = q at h hs
  obtain ⟨a, p⟩ := q
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨v, hv, rfl⟩ := h
  have := hA a v hv
  simp only [Ctx.rho] at this
  simp only at hs
  rw [hs]
  by_cases ha : c.H M a <;> cases v <;> cases p <;> simp_all

theorem Ctx.setLit_agrees {t : TT} (hA : t.Agrees (c.rho M)) {l : Nat} {b : Bool} (h : c.H M l ↔ b = true) :
    (c.setLit t l b).Agrees (c.rho M) := by
  simp only [Ctx.setLit]
  have hs := c.H_sgn hw (M := M) sgnFuel l
  generalize c.sgn sgnFuel l = q at hs ⊢
  obtain ⟨a, p⟩ := q
  apply TT.agrees_set hA
  simp only at hs
  simp only [Ctx.rho]
  by_cases ha : c.H M a <;> cases p <;> cases b <;> simp_all

theorem Ctx.openLits_none {t : TT} (hA : t.Agrees (c.rho M)) :
    ∀ ls : List Nat, c.openLits t ls = none → ∃ l ∈ ls, c.H M l
  | [], h => by simp [Ctx.openLits] at h
  | l :: ls, h => by
    simp only [Ctx.openLits] at h
    split at h
    · rename_i hl; exact ⟨l, by simp, (c.litVal_sound hw ht hM hA hl).mpr rfl⟩
    · obtain ⟨l', hl', h'⟩ := Ctx.openLits_none hA ls h; exact ⟨l', by simp [hl'], h'⟩
    · simp only [Option.map_eq_none_iff] at h
      obtain ⟨l', hl', h'⟩ := Ctx.openLits_none hA ls h; exact ⟨l', by simp [hl'], h'⟩

theorem Ctx.openLits_some {t : TT} (hA : t.Agrees (c.rho M)) :
    ∀ (ls us : List Nat), c.openLits t ls = some us → ∀ l ∈ ls, c.H M l → l ∈ us
  | [], _, _, l, hl, _ => by simp at hl
  | x :: ls, us, h, l, hl, hH => by
    simp only [Ctx.openLits] at h
    split at h
    · cases h
    · rename_i hx
      simp only [List.mem_cons] at hl
      rcases hl with rfl | hl
      · exact absurd ((c.litVal_sound hw ht hM hA hx).mp hH) (by simp)
      · exact Ctx.openLits_some hA ls us h l hl hH
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨us', h', rfl⟩ := h
      simp only [List.mem_cons] at hl ⊢
      rcases hl with rfl | hl
      · exact Or.inl rfl
      · exact Or.inr (Ctx.openLits_some hA ls us' h' l hl hH)

theorem Ctx.propagate_sound : ∀ (t : TT) (xs : List Nat), t.Agrees (c.rho M) → (∀ x ∈ xs, c.H M x) →
    c.propagate t xs = true → False
  | _, [], _, _, h => by simp [Ctx.propagate] at h
  | t, x :: xs, hA, hx, h => by
    simp only [List.mem_cons, forall_eq_or_imp] at hx
    simp only [Ctx.propagate] at h
    split at h
    · rename_i hf
      simp only [beq_iff_eq] at hf
      exact absurd ((c.litVal_sound hw ht hM hA hf).mp hx.1) (by simp)
    · have hA2 : (if c.isOr x = true then c.setLit t x true else t).Agrees (c.rho M) := by
        split
        · exact c.setLit_agrees hw ht hM hA (by simp [hx.1])
        · exact hA
      generalize (if c.isOr x = true then c.setLit t x true else t) = t2 at h hA2
      obtain ⟨l, hl, hH⟩ := (c.H_clause hw x).mp hx.1
      split at h
      · exact Ctx.propagate_sound t2 xs hA2 hx.2 h
      · rename_i h0
        have := c.openLits_some hw ht hM hA2 _ _ h0 l hl hH; simp at this
      · rename_i u hu
        have hlu := c.openLits_some hw ht hM hA2 _ _ hu l hl hH
        simp only [List.mem_singleton] at hlu; subst hlu
        exact Ctx.propagate_sound _ xs (c.setLit_agrees hw ht hM hA2 (by simp [hH])) hx.2 h
      · exact Ctx.propagate_sound t2 xs hA2 hx.2 h

theorem Ctx.foldl_agrees : ∀ (ls : List Nat) (t : TT), t.Agrees (c.rho M) → (∀ l ∈ ls, ¬c.H M l) →
    (ls.foldl (fun t l => c.setLit t l false) t).Agrees (c.rho M)
  | [], _, hA, _ => hA
  | l :: ls, t, hA, h => by
    simp only [List.foldl_cons]
    simp only [List.mem_cons, forall_eq_or_imp] at h
    exact Ctx.foldl_agrees ls _ (c.setLit_agrees hw ht hM hA (by simp [h.1])) h.2

theorem Ctx.rup_sound {cs : List Nat} {d : Nat} (h : c.rup cs d = true) (hc : ∀ x ∈ cs, c.H M x) : c.H M d := by
  refine Classical.byContradiction fun hd => ?_
  simp only [Ctx.rup, Bool.or_eq_true] at h
  have hls : ∀ l ∈ (if c.isOr d = true then d :: c.clause d else c.clause d), ¬c.H M l := by
    have hcl : ∀ l ∈ c.clause d, ¬c.H M l := fun l hl hH => hd ((c.H_clause hw d).mpr ⟨l, hl, hH⟩)
    split
    · intro l hl; simp only [List.mem_cons] at hl; rcases hl with rfl | hl
      · exact hd
      · exact hcl l hl
    · exact hcl
  generalize (if c.isOr d = true then d :: c.clause d else c.clause d) = ls at h hls
  rcases h with h | h
  · simp only [Ctx.taut, List.any_eq_true, List.contains_iff, List.mem_map] at h
    obtain ⟨⟨a, p⟩, ⟨l1, hl1, e1⟩, ⟨l2, hl2, e2⟩⟩ := h
    have h1 := c.H_sgn hw (M := M) sgnFuel l1
    have h2 := c.H_sgn hw (M := M) sgnFuel l2
    rw [e1] at h1; rw [e2] at h2
    simp only at h1 h2
    have n1 := hls l1 hl1; have n2 := hls l2 hl2
    cases p <;> simp_all
  · exact c.propagate_sound hw ht hM _ cs (c.foldl_agrees hw ht hM ls _ (TT.agrees_leaf _) hls) hc h

/-! ## Equality lemmas -/

/-- Hypothesis `h` holds: its atom has its value. -/
def Ctx.HypOk (c : Ctx) (M : Surf.Model R U) (h : Nat × Bool) : Prop := c.H M h.1 ↔ h.2 = true

theorem Ctx.hyps_ok {d : Nat} (hd : ¬c.H M d) : ∀ h ∈ c.hyps d, c.HypOk M h := by
  intro h hh
  simp only [Ctx.hyps, List.mem_map] at hh
  obtain ⟨l, hl, rfl⟩ := hh
  have hnl : ¬c.H M l := fun hH => hd ((c.H_clause hw d).mpr ⟨l, hl, hH⟩)
  have hs := c.H_sgn hw (M := M) sgnFuel l
  generalize c.sgn sgnFuel l = q at hs ⊢
  obtain ⟨a, p⟩ := q
  simp only [Ctx.HypOk] at hs ⊢
  cases p <;> simp_all

theorem Ctx.isTt_V {i : Nat} (h : c.isTt i = true) : c.V M i = .bool true := by
  simp only [Ctx.isTt, beq_iff_eq] at h; exact c.V_tt hw h

theorem Ctx.isFf_V {i : Nat} (h : c.isFf i = true) : c.V M i = .bool false := by
  simp only [Ctx.isFf, beq_iff_eq] at h; exact c.V_ff hw h

theorem Ctx.given_sound {tt ff : Nat} (htt : c.isTt tt = true) (hff : c.isFf ff = true) {h : Nat × Bool}
    (hh : c.HypOk M h) {e : Nat × Nat} (hg : c.given tt ff h = some e) : c.V M e.1 = c.V M e.2 := by
  obtain ⟨a, v⟩ := h
  simp only [Ctx.given] at hg
  simp only [Ctx.HypOk] at hh
  cases v
  · simp only [Bool.false_eq_true, if_false] at hg
    split at hg
    · rename_i hb
      simp only [Option.some.injEq] at hg; subst hg
      obtain ⟨b, hv⟩ := c.bool_val hw ht hM hb
      simp only [Bool.false_eq_true, iff_false, Ctx.H_def, hv, Val.bool.injEq] at hh
      simp only [hv, c.isFf_V hw ht hM hff]
      cases b <;> simp_all
    · cases hg
  · simp only [if_true] at hg
    simp only [iff_true] at hh
    split at hg
    · rename_i e' he
      simp only [Option.some.injEq] at hg; subst hg
      exact (c.H_eqOf hw ht hM he).mp hh
    · simp only [Option.some.injEq] at hg; subst hg
      simp only [c.isTt_V hw ht hM htt]; exact Ctx.H_def.mp hh

theorem Ctx.ufSteps_sound {tt ff : Nat} (htt : c.isTt tt = true) (hff : c.isFf ff = true)
    {H : List (Nat × Bool)} (hH : ∀ h ∈ H, c.HypOk M h) :
    ∀ (ss : List UfStep) (done r : List (Nat × Nat)), (∀ p ∈ done, c.V M p.1 = c.V M p.2) →
      c.ufSteps tt ff H done ss = some r → ∀ p ∈ r, c.V M p.1 = c.V M p.2
  | [], done, r, hd, h => by simp only [Ctx.ufSteps, Option.some.injEq] at h; subst h; exact hd
  | s :: ss, done, r, hd, h => by
    simp only [Ctx.ufSteps] at h
    split at h
    · rename_i e he
      apply Ctx.ufSteps_sound htt hff hH ss (done ++ [e]) r _ h
      have hdi : ∀ {j : Nat} {p : Nat × Nat}, done[j]? = some p → c.V M p.1 = c.V M p.2 :=
        fun hj => hd _ (List.mem_of_getElem? hj)
      have hev : c.V M e.1 = c.V M e.2 := by
        cases s with
        | refl t => simp only [Option.some.injEq] at he; subst he; rfl
        | given i =>
          simp only [Option.bind_eq_some_iff] at he
          obtain ⟨g, hg, he⟩ := he
          exact c.given_sound hw ht hM htt hff (hH g (List.mem_of_getElem? hg)) he
        | symm j =>
          simp only [Option.map_eq_some_iff] at he
          obtain ⟨⟨a, b⟩, hj, rfl⟩ := he
          exact (hdi hj).symm
        | trans j k =>
          simp only at he
          split at he
          · rename_i a b b' d hj hk
            split at he
            · rename_i hbb
              simp only [beq_iff_eq] at hbb; subst hbb
              simp only [Option.some.injEq] at he; subst he
              exact (hdi hj).trans (hdi hk)
            · cases he
          · cases he
        | cong j ks l r' =>
          simp only at he
          split at he
          · rename_i f g f' as g' bs hj hl hr
            split at he
            · rename_i hc
              simp only [Option.some.injEq] at he; subst he
              simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hc
              obtain ⟨⟨⟨⟨rfl, rfl⟩, hla⟩, hlb⟩, hall⟩ := hc
              have hfg := hdi hj
              have hargs : ∀ p ∈ as.zip bs, c.V M p.1 = c.V M p.2 := by
                have := zip3_mem (fun k (p : Nat × Nat) => done[k]? = some p) ks (as.zip bs)
                  (by simp [List.length_zip, hla, hlb]) (fun q hq => by
                    have := hall q hq; simpa using this)
                intro p hp
                obtain ⟨k, hk⟩ := this p hp
                exact hdi hk
              simp only
              rw [c.V_node hw hl, c.V_node hw hr]
              simp only [Surf.evalNode]
              have hm := map_eq_of_zip (get (Surf.values M.toInterp c.nodes)) as bs (by omega) hargs
              rw [hm]
              exact congrArg (fun v => M.app v (bs.map (get (Surf.values M.toInterp c.nodes)))) hfg
            · cases he
          · cases he
      intro p hp
      simp only [List.mem_append, List.mem_singleton] at hp
      rcases hp with hp | rfl
      · exact hd p hp
      · exact hev
    · cases h

theorem Ctx.clash_sound {H : List (Nat × Bool)} (hH : ∀ h ∈ H, c.HypOk M h) {a b : Nat}
    (he : c.V M a = c.V M b) (h : c.clash H a b = true) : False := by
  simp only [Ctx.clash, Bool.or_eq_true, Bool.and_eq_true, List.contains_iff, List.any_eq_true,
    Bool.not_eq_true', beq_iff_eq] at h
  rcases h with (((((⟨ha, hb⟩ | ⟨ha, hb⟩) | ⟨hb, hm⟩) | ⟨ha, hm⟩) | ⟨hb, hm⟩) | ⟨ha, hm⟩) | ⟨⟨e, v⟩, hm, hv, hq⟩
  · rw [c.isTt_V hw ht hM ha, c.isFf_V hw ht hM hb] at he; simp at he
  · rw [c.isFf_V hw ht hM ha, c.isTt_V hw ht hM hb] at he; simp at he
  · have := hH _ hm; simp only [Ctx.HypOk] at this
    rw [c.isTt_V hw ht hM hb] at he
    simp_all [Ctx.H_def]
  · have := hH _ hm; simp only [Ctx.HypOk] at this
    rw [c.isTt_V hw ht hM ha] at he
    simp_all [Ctx.H_def]
  · have := hH _ hm; simp only [Ctx.HypOk] at this
    rw [c.isFf_V hw ht hM hb] at he
    have hs := c.H_sgn hw (M := M) sgnFuel a
    rw [← this] at hs
    have : ¬c.H M a := by simp [Ctx.H_def, he]
    exact this (hs.mpr Iff.rfl)
  · have := hH _ hm; simp only [Ctx.HypOk] at this
    rw [c.isFf_V hw ht hM ha] at he
    have hs := c.H_sgn hw (M := M) sgnFuel b
    rw [← this] at hs
    have : ¬c.H M b := by simp [Ctx.H_def, ← he]
    exact this (hs.mpr Iff.rfl)
  · have := hH _ hm; simp only [Ctx.HypOk] at this
    subst hv
    simp only [Bool.false_eq_true, iff_false] at this
    rcases hq with hq | hq
    · exact this ((c.H_eqOf hw ht hM hq).mpr he)
    · exact this ((c.H_eqOf hw ht hM hq).mpr he.symm)

theorem Ctx.uf_sound {tt ff d : Nat} {ss : List UfStep} (htt : c.isTt tt = true) (hff : c.isFf ff = true)
    (h : c.uf tt ff d ss = true) : c.H M d := by
  refine Classical.byContradiction fun hd => ?_
  have hH := c.hyps_ok hw ht hM hd
  simp only [Ctx.uf] at h
  split at h
  · rename_i done hdone
    split at h
    · rename_i a b hl
      have hall := c.ufSteps_sound hw ht hM htt hff hH ss [] done (by simp) hdone
      exact c.clash_sound hw ht hM hH (hall _ (List.mem_of_getLast? hl)) h
    · cases h
  · cases h

/-! ## Resolution -/

theorem Ctx.isNot_H {l L : Nat} (h : c.isNot l L = true) : c.H M l ↔ ¬c.H M L := by
  simp only [Ctx.isNot, beq_iff_eq, Ctx.notOf] at h
  split at h
  · rename_i a ha; simp only [Option.some.injEq] at h; subst h; exact c.H_not hw ha
  · cases h

theorem Ctx.isPos_H {pol : Bool} {L l : Nat} (h : c.isPos pol L l = true) : c.H M l ↔ (c.H M L ↔ pol = true) := by
  simp only [Ctx.isPos] at h
  cases pol
  · simp only [Bool.false_eq_true, if_false] at h; rw [c.isNot_H hw ht hM h]; simp
  · simp only [if_true, beq_iff_eq] at h; subst h; simp

theorem Ctx.isNeg_H {pol : Bool} {L l : Nat} (h : c.isNeg pol L l = true) : c.H M l ↔ ¬(c.H M L ↔ pol = true) := by
  simp only [Ctx.isNeg] at h
  cases pol
  · simp only [Bool.false_eq_true, if_false, beq_iff_eq] at h; subst h; simp
  · simp only [if_true] at h; rw [c.isNot_H hw ht hM h]; simp

theorem Ctx.resolve_sound : ∀ (cur xs : List Nat) (pols : List Bool) (Ls : List Nat) (r : List Nat),
    c.resolve cur xs pols Ls = some r → (∃ l ∈ cur, c.H M l) → (∀ x ∈ xs, c.H M x) → ∃ l ∈ r, c.H M l
  | cur, [], [], [], r, h, hc, _ => by simp only [Ctx.resolve, Option.some.injEq] at h; subst h; exact hc
  | cur, x :: xs, pol :: pols, L :: Ls, r, h, hc, hx => by
    simp only [Ctx.resolve] at h
    simp only [List.mem_cons, forall_eq_or_imp] at hx
    apply Ctx.resolve_sound _ xs pols Ls r h _ hx.2
    by_cases hp : (c.H M L ↔ pol = true)
    · -- the negative pivot is false: premise `x` keeps a literal
      have hx1 := hx.1
      simp only [Ctx.rest]
      split
      · rename_i hn; exact absurd hp ((c.isNeg_H hw ht hM hn).mp hx1)
      · obtain ⟨l, hl, hH⟩ := (c.H_clause hw x).mp hx1
        refine ⟨l, List.mem_append_right _ (List.mem_filter.mpr ⟨hl, ?_⟩), hH⟩
        cases hn : c.isNeg pol L l
        · rfl
        · exact absurd hp ((c.isNeg_H hw ht hM hn).mp hH)
    · obtain ⟨l, hl, hH⟩ := hc
      refine ⟨l, List.mem_append_left _ (List.mem_filter.mpr ⟨hl, ?_⟩), hH⟩
      cases hn : c.isPos pol L l
      · rfl
      · exact absurd ((c.isPos_H hw ht hM hn).mp hH) hp
  | _, [], _ :: _, _, _, h, _, _ => by simp [Ctx.resolve] at h
  | _, [], [], _ :: _, _, h, _, _ => by simp [Ctx.resolve] at h
  | _, _ :: _, [], _, _, h, _, _ => by simp [Ctx.resolve] at h
  | _, _ :: _, _ :: _, [], _, h, _, _ => by simp [Ctx.resolve] at h

theorem Ctx.implies_sound {ls : List Nat} {d : Nat} (h : c.implies ls d = true) (hl : ∃ l ∈ ls, c.H M l) :
    c.H M d := by
  obtain ⟨l, hl, hH⟩ := hl
  have := List.all_eq_true.mp h l hl
  simp only [Bool.or_eq_true, beq_iff_eq, List.contains_iff] at this
  rcases this with rfl | hm
  · exact hH
  · exact (c.H_clause hw d).mpr ⟨l, hm, hH⟩

theorem Ctx.chain_sound {ps : List Nat} {pols : List Bool} {Ls : List Nat} {d : Nat}
    (h : c.chain ps pols Ls d = true) (hp : ∀ x ∈ ps, c.H M x) : c.H M d := by
  simp only [Ctx.chain] at h
  split at h
  · rename_i x xs pol pols' L Ls'
    simp only [List.mem_cons, forall_eq_or_imp] at hp
    split at h
    · rename_i r hr
      apply c.implies_sound hw ht hM h
      apply c.resolve_sound hw ht hM _ xs (pol :: pols') (L :: Ls') r hr _ hp.2
      split
      · exact ⟨x, by simp, hp.1⟩
      · exact (c.H_clause hw x).mp hp.1
    · cases h
  · cases h

/-! ## Tautologies -/

theorem Ctx.orNot_H {d f : Nat} {ls : List Nat} (h : c.orNot d = some (f, ls)) :
    c.H M d ↔ ¬c.H M f ∨ ∃ l ∈ ls, c.H M l := by
  simp only [Ctx.orNot] at h
  split at h
  · rename_i n ls' hd
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨f', hf, rfl, rfl⟩ := h
    have hn : c.node n = some (.not f') := by simp only [Ctx.notOf] at hf; split at hf <;> simp_all
    rw [c.H_or hw hd, ← c.H_not hw hn]
    simp
  · cases h

theorem Ctx.evalB_sound : ∀ (fuel t : Nat) (b : Bool), c.evalB fuel t = some b → (c.H M t ↔ b = true)
  | 0, _, _, h => by simp [Ctx.evalB] at h
  | fuel + 1, t, b, h => by
    simp only [Ctx.evalB] at h
    split at h
    · rename_i ht'; simp only [Option.some.injEq] at h; subst h; simp [c.H_tt hw ht']
    · rename_i ht'; simp only [Option.some.injEq] at h; subst h; simp [c.H_ff hw ht']
    · rename_i a ha
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨b', hb, rfl⟩ := h
      rw [c.H_not hw ha, Ctx.evalB_sound fuel a b' hb]
      cases b' <;> simp
    · cases h

theorem Ctx.taut_sound {k : Taut} {d : Nat} (h : c.tautOk k d = true) : c.H M d := by
  have hNot := fun {l L : Nat} (h : c.isNot l L = true) => c.isNot_H hw ht hM (M := M) h
  cases k <;> simp only [Ctx.tautOk] at h
  case andPos =>
    split at h
    · rename_i f x hd
      split at h
      · rename_i as hf
        rw [c.orNot_H hw ht hM hd]
        by_cases hF : c.H M f
        · exact Or.inr ⟨x, by simp, (c.H_and hw hf).mp hF x (by simpa using h)⟩
        · exact Or.inl hF
      · cases h
    · cases h
  case andNeg =>
    split at h
    · rename_i f ns hd
      split at h
      · rename_i as hf
        simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
        rw [c.H_or hw hd]
        by_cases hall : ∀ a ∈ as, c.H M a
        · exact ⟨f, by simp, (c.H_and hw hf).mpr hall⟩
        · simp only [not_forall] at hall
          obtain ⟨a, ha, hna⟩ := hall
          obtain ⟨n, hz⟩ := zip_left_mem as ns h.1 a ha
          have hnn := h.2 _ hz
          exact ⟨n, List.mem_cons_of_mem _ (List.of_mem_zip hz).2, (hNot hnn).mpr hna⟩
      · cases h
    · cases h
  case orPos =>
    split at h
    · rename_i f ls hd
      simp only [beq_iff_eq] at h
      rw [c.orNot_H hw ht hM hd]
      by_cases hF : c.H M f
      · exact Or.inr ((c.H_or hw h).mp hF)
      · exact Or.inl hF
    · cases h
  case orNeg =>
    split at h
    · rename_i f n hd
      split at h
      · rename_i as x hf hn
        have hn' : c.isNot n x = true := by simp [Ctx.isNot, hn]
        rw [c.H_or hw hd]
        by_cases hx : c.H M x
        · exact ⟨f, by simp, (c.H_or hw hf).mpr ⟨x, by simpa using h, hx⟩⟩
        · exact ⟨n, by simp, (hNot hn').mpr hx⟩
      · cases h
    · cases h
  case equivPos1 | equivPos2 =>
    split at h
    · rename_i e l1 l2 hd
      split at h
      · rename_i a b he
        rw [c.orNot_H hw ht hM hd, c.H_iff hw he]
        simp only [beq_iff_eq, reduceCtorEq, if_true, if_false, Bool.and_eq_true] at h
        obtain ⟨h1, rfl⟩ | ⟨rfl, h2⟩ := (show (c.isNot l1 a = true ∧ l2 = b) ∨ (l1 = a ∧ c.isNot l2 b = true) by
          first | exact Or.inl h | exact Or.inr h)
        · by_cases ha : c.H M a
          · by_cases hb : c.H M l2
            · exact Or.inr ⟨l2, by simp, hb⟩
            · exact Or.inl (fun e => hb (e.mp ha))
          · exact Or.inr ⟨l1, by simp, (hNot h1).mpr ha⟩
        · by_cases hb : c.H M b
          · by_cases ha : c.H M l1
            · exact Or.inr ⟨l1, by simp, ha⟩
            · exact Or.inl (fun e => ha (e.mpr hb))
          · exact Or.inr ⟨l2, by simp, (hNot h2).mpr hb⟩
      · cases h
    · cases h
  case equivNeg1 | equivNeg2 =>
    split at h
    · rename_i e l1 l2 hd
      split at h
      · rename_i a b he
        rw [c.H_or hw hd]
        simp only [beq_iff_eq, reduceCtorEq, if_true, if_false, Bool.and_eq_true] at h
        obtain ⟨rfl, rfl⟩ | ⟨h1, h2⟩ := (show (l1 = a ∧ l2 = b) ∨ (c.isNot l1 a = true ∧ c.isNot l2 b = true) by
          first | exact Or.inl h | exact Or.inr h)
        · by_cases ha : c.H M l1
          · exact ⟨l1, by simp, ha⟩
          · by_cases hb : c.H M l2
            · exact ⟨l2, by simp, hb⟩
            · exact ⟨e, by simp, (c.H_iff hw he).mpr (iff_of_false ha hb)⟩
        · by_cases ha : c.H M a
          · by_cases hb : c.H M b
            · exact ⟨e, by simp, (c.H_iff hw he).mpr (iff_of_true ha hb)⟩
            · exact ⟨l2, by simp, (hNot h2).mpr hb⟩
          · exact ⟨l1, by simp, (hNot h1).mpr ha⟩
      · cases h
    · cases h
  case itePos1 | itePos2 | itePos3 =>
    split at h
    · rename_i e l1 l2 hd
      split at h
      · rename_i x a b he
        rw [c.orNot_H hw ht hM hd, c.H_ite hw he]
        simp only [beq_iff_eq, reduceCtorEq, if_true, if_false, Bool.and_eq_true] at h
        by_cases hE : (c.H M x ∧ c.H M a) ∨ (¬c.H M x ∧ c.H M b)
        · refine Or.inr ?_
          first
          | (obtain ⟨h1, rfl⟩ := h
             rcases hE with ⟨hx, ha⟩ | ⟨hx, _⟩
             · exact ⟨l2, by simp, ha⟩
             · exact ⟨l1, by simp, (hNot h1).mpr hx⟩)
          | (obtain ⟨rfl, rfl⟩ := h
             first
             | (rcases hE with ⟨hx, _⟩ | ⟨_, hb⟩
                · exact ⟨l1, by simp, hx⟩
                · exact ⟨l2, by simp, hb⟩)
             | (rcases hE with ⟨_, ha⟩ | ⟨_, hb⟩
                · exact ⟨l1, by simp, ha⟩
                · exact ⟨l2, by simp, hb⟩))
        · exact Or.inl hE
      · cases h
    · cases h
  case iteNeg1 | iteNeg2 | iteNeg3 =>
    split at h
    · rename_i e l1 l2 hd
      split at h
      · rename_i x a b he
        rw [c.H_or hw hd]
        have hE := c.H_ite hw he (M := M)
        simp only [beq_iff_eq, reduceCtorEq, if_true, if_false, Bool.and_eq_true] at h
        first
        | (obtain ⟨h1, h2⟩ := h
           first
           | (by_cases hx : c.H M x
              · by_cases ha : c.H M a
                · exact ⟨e, by simp, hE.mpr (Or.inl ⟨hx, ha⟩)⟩
                · exact ⟨l2, by simp, (hNot h2).mpr ha⟩
              · exact ⟨l1, by simp, (hNot h1).mpr hx⟩)
           | (by_cases ha : c.H M a
              · by_cases hb : c.H M b
                · by_cases hx : c.H M x
                  · exact ⟨e, by simp, hE.mpr (Or.inl ⟨hx, ha⟩)⟩
                  · exact ⟨e, by simp, hE.mpr (Or.inr ⟨hx, hb⟩)⟩
                · exact ⟨l2, by simp, (hNot h2).mpr hb⟩
              · exact ⟨l1, by simp, (hNot h1).mpr ha⟩))
        | (obtain ⟨rfl, h2⟩ := h
           by_cases hx : c.H M l1
           · exact ⟨l1, by simp, hx⟩
           · by_cases hb : c.H M b
             · exact ⟨e, by simp, hE.mpr (Or.inr ⟨hx, hb⟩)⟩
             · exact ⟨l2, by simp, (hNot h2).mpr hb⟩)
      · cases h
    · cases h
  case refl =>
    split at h
    · rename_i a b he
      simp only [beq_iff_eq] at h; subst h
      exact (c.H_eqOf hw ht hM he).mpr rfl
    · cases h
  case iteEq =>
    split at h
    · rename_i x e1 e2 hd
      split at h
      · rename_i k1 a k2 b h1 h2
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨rfl, hk⟩ := h
        rw [c.H_ite hw hd, c.H_eqOf hw ht hM h1, c.H_eqOf hw ht hM h2, c.V_ite hw hk]
        by_cases hx : c.H M x <;> simp [hx]
      · cases h
    · cases h
  case evaluate =>
    split at h
    · rename_i t v hd
      rw [c.H_iff hw hd]
      split at h
      · rename_i hb
        rw [c.evalB_sound hw ht hM 64 t true hb]
        simp only [Ctx.isTt, beq_iff_eq] at h
        simp [c.H_tt hw h]
      · rename_i hb
        rw [c.evalB_sound hw ht hM 64 t false hb]
        simp only [Ctx.isFf, beq_iff_eq] at h
        simp [c.H_ff hw h]
      · cases h
    · cases h
  case doubleNot =>
    split at h
    · rename_i x y hd
      rw [c.H_iff hw hd]
      simp only [beq_iff_eq, Option.bind_eq_some_iff] at h
      obtain ⟨z, hz, hy⟩ := h
      have hz' : c.isNot x z = true := by simp [Ctx.isNot, hz]
      have hy' : c.isNot z y = true := by simp [Ctx.isNot, hy]
      rw [hNot hz', hNot hy', not_not]
    · cases h
  case implElim =>
    split at h
    · rename_i x y hd
      rw [c.H_iff hw hd]
      split at h
      · rename_i a b n b' hx hy
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨hn, rfl⟩ := h
        rw [c.H_implies hw hx, c.H_or hw hy]
        simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, hNot hn]
        by_cases ha : c.H M a <;> simp [ha]
      · cases h
    · cases h
  case eqRefl =>
    split at h
    · rename_i e t hd
      simp only [Bool.and_eq_true] at h
      obtain ⟨htt, h⟩ := h
      rw [c.H_iff hw hd]
      split at h
      · rename_i a b he
        simp only [beq_iff_eq] at h; subst h
        simp only [Ctx.isTt, beq_iff_eq] at htt
        exact iff_of_true ((c.H_eqOf hw ht hM he).mpr rfl) (c.H_tt hw htt)
      · cases h
    · cases h

/-! ## Steps -/

theorem Ctx.transOk_sound {s0 : Nat} : ∀ (a : Nat) (ps : List Nat) (d : Nat), c.transOk s0 a ps d = true →
    c.V M s0 = c.V M a → (∀ p ∈ ps, c.H M p) → c.H M d
  | a, [], d, h, hs, _ => by
    simp only [Ctx.transOk] at h
    split at h
    · rename_i x y hd
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact (c.H_eqOf hw ht hM hd).mpr hs
    · cases h
  | a, p :: ps, d, h, hs, hp => by
    simp only [Ctx.transOk] at h
    simp only [List.mem_cons, forall_eq_or_imp] at hp
    split at h
    · rename_i x y he
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, h⟩ := h
      exact Ctx.transOk_sound y ps d h (hs.trans ((c.H_eqOf hw ht hM he).mp hp.1)) hp.2
    · cases h

theorem Ctx.congOk_sound {ps : List Nat} {d : Nat} (h : c.congOk ps d = true) (hp : ∀ x ∈ ps, c.H M x) :
    c.H M d := by
  simp only [Ctx.congOk] at h
  split at h
  · rename_i t u hd
    rw [c.H_eqOf hw ht hM hd]
    split at h
    · rename_i n m hn hm
      split at h
      · rename_i pairs hpairs
        apply c.same_sound hw ht hM hn hm hpairs
        simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
        obtain ⟨⟨hhead, hl⟩, hall⟩ := h
        -- each pair of arguments is equated by its premise
        have hargs : ∀ q ∈ (match n with
            | .app _ _ => pairs.tail
            | _ => pairs), c.V M q.1 = c.V M q.2 := by
          intro q hq
          obtain ⟨p, hz⟩ := zip_left_mem _ ps hl q hq
          have hpq := hall _ hz
          simp only at hpq
          exact (c.H_eqOf hw ht hM hpq).mp (hp p (List.of_mem_zip hz).2)
        intro q hq
        cases n with
        | app f as =>
          cases m with
          | app g bs =>
            simp only [beq_iff_eq] at hhead
            simp only [samePairs, kids] at hpairs
            split at hpairs
            · simp only [Option.some.injEq] at hpairs; subst hpairs
              simp only [List.zip_cons_cons, List.mem_cons] at hq
              rcases hq with rfl | hq
              · simp [hhead]
              · exact hargs q (by simpa using hq)
            · cases hpairs
          | _ => simp [samePairs, kids] at hpairs
        | _ => exact hargs q hq
      · cases h
    · cases h
  · cases h

theorem Ctx.step_sound {asserts : List Nat} {P : Proof} {s : Step} {ps : List Nat}
    (hA : ∀ a ∈ asserts, c.H M a) (hE : ∀ j e, Tab.at P.eqvs j = some e → c.V M e.x = c.V M e.y)
    (htt : c.isTt P.tt = true) (hff : c.isFf P.ff = true)
    (h : c.stepOk asserts P s ps = true) (hp : ∀ x ∈ ps, c.H M x) : c.H M s.concl := by
  have hNot := fun {l L : Nat} (h : c.isNot l L = true) => c.isNot_H hw ht hM (M := M) h
  unfold Ctx.stepOk at h
  split at h <;> simp only at h
  next _ _ a e _ =>
    simp only [Bool.and_eq_true, List.contains_iff] at h
    exact (Ctx.H_def).mpr ((viaEqv_sound hE h.2).symm.trans (Ctx.H_def.mp (hA a h.1)))
  next _ _ e f _ =>
    exact (Ctx.H_def).mpr ((viaEqv_sound hE h).symm.trans (Ctx.H_def.mp (hp f (by simp))))
  next => exact c.rup_sound hw ht hM h hp
  next => exact c.uf_sound hw ht hM htt hff h
  next => exact c.taut_sound hw ht hM h
  next _ _ x _ =>
    simp only [Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h
    · exact hp _ (by simp)
    · exact c.implies_sound hw ht hM h ((c.H_clause hw x).mp (hp x (by simp)))
  next => exact c.chain_sound hw ht hM h hp
  next _ _ x _ =>
    split at h
    · rename_i as hx
      simp only [List.contains_iff] at h
      exact (c.H_and hw hx).mp (hp x (by simp)) _ h
    · cases h
  next ps' _ _ _ =>
    simp only [Bool.or_eq_true, beq_iff_eq] at h
    rcases h with h | rfl
    · exact (c.H_and hw h).mpr hp
    · exact hp _ (by simp)
  next _ _ x _ =>
    have hx := hp x (by simp)
    split at h
    · rename_i a b b' a' h1 h2
      simp only [Bool.and_eq_true, beq_iff_eq] at h; obtain ⟨rfl, rfl⟩ := h
      rw [c.H_eq hw h1] at hx; rw [c.H_eq hw h2]; exact hx.symm
    · rename_i a b b' a' h1 h2
      simp only [Bool.and_eq_true, beq_iff_eq] at h; obtain ⟨rfl, rfl⟩ := h
      rw [c.H_iff hw h1] at hx; rw [c.H_iff hw h2]; exact hx.symm
    · rename_i e e' h1 h2
      rw [c.H_not hw h1] at hx; rw [c.H_not hw h2]
      split at h
      · rename_i a b b' a' h3 h4
        simp only [Bool.and_eq_true, beq_iff_eq] at h; obtain ⟨rfl, rfl⟩ := h
        rw [c.H_eq hw h3] at hx; rw [c.H_eq hw h4]; exact fun e => hx e.symm
      · rename_i a b b' a' h3 h4
        simp only [Bool.and_eq_true, beq_iff_eq] at h; obtain ⟨rfl, rfl⟩ := h
        rw [c.H_iff hw h3] at hx; rw [c.H_iff hw h4]; exact fun e => hx e.symm
      · cases h
    · cases h
  next _ _ p ps' _ =>
    split at h
    · rename_i a b he
      exact c.transOk_sound hw ht hM a (p :: ps') _ h rfl hp
    · cases h
  next => exact c.congOk_sound hw ht hM h hp
  next _ _ x e _ =>
    simp only [beq_iff_eq] at h
    exact ((c.H_iff hw h).mp (hp e (by simp))).mp (hp x (by simp))
  next _ _ e _ =>
    split at h
    · rename_i x t he
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, htt'⟩ := h
      simp only [Ctx.isTt, beq_iff_eq] at htt'
      exact ((c.H_iff hw he).mp (hp e (by simp))).mpr (c.H_tt hw htt')
    · cases h
  next _ _ x _ =>
    split at h
    · rename_i a b n b' hx hd
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨hn, rfl⟩ := h
      have := (c.H_implies hw hx).mp (hp x (by simp))
      rw [c.H_or hw hd]
      by_cases ha : c.H M a
      · exact ⟨b, by simp, this ha⟩
      · exact ⟨n, by simp, (hNot hn).mpr ha⟩
    · cases h
  next => cases h

/-! ## Proofs -/

/-- The assumptions of the open scopes hold. -/
def Ctx.Hyps (c : Ctx) (M : Surf.Model R U) (stack : List (Nat × Nat)) : Prop := ∀ q ∈ stack, c.H M q.1

/-- The first `n` facts hold where the assumptions of `stack` do. -/
def Ctx.Good (c : Ctx) (M : Surf.Model R U) (facts : Trie) (n : Nat) (stack : List (Nat × Nat)) : Prop :=
  c.Hyps M stack → ∀ j < n, ∀ x, facts.get j = some x → c.H M x

/-- The invariant of a proof's state: its facts hold under the scopes open,
    and those before each scope under the scopes it is in. -/
def Ctx.Inv (c : Ctx) (M : Surf.Model R U) (facts : Trie) : Nat → List (Nat × Nat) → Prop
  | n, [] => c.Good M facts n []
  | n, (h, m) :: rest => c.Good M facts n ((h, m) :: rest) ∧ m ≤ n ∧ c.Inv M facts m rest

theorem Ctx.good_set {facts : Trie} {n k x : Nat} {stack : List (Nat × Nat)} (hk : n ≤ k)
    (h : c.Good M facts n stack) : c.Good M (facts.set k x) n stack := by
  intro hh j hj y hy
  rw [Trie.get_set, if_neg (by omega)] at hy
  exact h hh j hj y hy

theorem Ctx.inv_set {facts : Trie} {k x : Nat} : ∀ {n : Nat} {stack : List (Nat × Nat)}, n ≤ k →
    c.Inv M facts n stack → c.Inv M (facts.set k x) n stack
  | _, [], hk, h => c.good_set hw ht hM hk h
  | _, (_, _) :: _, hk, ⟨hg, hm, hr⟩ => ⟨c.good_set hw ht hM hk hg, hm, Ctx.inv_set (by omega) hr⟩

theorem Ctx.inv_add {facts : Trie} {n x : Nat} {stack : List (Nat × Nat)} (h : c.Inv M facts n stack)
    (hx : c.Hyps M stack → c.H M x) : c.Inv M (facts.set n x) (n + 1) stack := by
  have hg : c.Good M facts n stack := by
    cases stack with
    | nil => exact h
    | cons q rest => exact h.1
  have hg' : c.Good M (facts.set n x) (n + 1) stack := by
    intro hh j hj y hy
    rw [Trie.get_set] at hy
    split at hy
    · cases hy; exact hx hh
    · exact hg hh j (by omega) y hy
  cases stack with
  | nil => exact hg'
  | cons q rest =>
    obtain ⟨_, hm, hr⟩ := h
    exact ⟨hg', by omega, c.inv_set hw ht hM (by omega) hr⟩

theorem Ctx.good_of_inv {facts : Trie} {n : Nat} {stack : List (Nat × Nat)} (h : c.Inv M facts n stack) :
    c.Good M facts n stack := by
  cases stack with
  | nil => exact h
  | cons q rest => exact h.1

theorem Ctx.cmd_sound {asserts : List Nat} {P : Proof} (hA : ∀ a ∈ asserts, c.H M a)
    (hE : ∀ j e, Tab.at P.eqvs j = some e → c.V M e.x = c.V M e.y)
    (htt : c.isTt P.tt = true) (hff : c.isFf P.ff = true) {st st' : State} {x : Cmd}
    (hi : c.Inv M st.facts st.n st.stack) (h : c.cmd asserts P st x = some st') :
    c.Inv M st'.facts st'.n st'.stack := by
  have hg := c.good_of_inv hw ht hM hi
  cases x with
  | step s =>
    simp only [Ctx.cmd] at h
    split at h
    · rename_i ps hps
      split at h
      · rename_i hok
        simp only [Option.some.injEq] at h; subst h
        apply c.inv_add hw ht hM hi
        intro hh
        apply c.step_sound hw ht hM hA hE htt hff hok
        intro y hy
        have hm := optAll_mem _ _ hps y hy
        simp only [List.mem_map] at hm
        obtain ⟨j, _, hj⟩ := hm
        simp only [State.prem] at hj
        split at hj
        · rename_i hjn; exact hg hh j hjn y hj
        · cases hj
      · cases h
    · cases h
  | push f =>
    simp only [Ctx.cmd] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h
      simp only [State.add]
      refine ⟨?_, by omega, c.inv_set hw ht hM (by omega) hi⟩
      intro hh j hj y hy
      rw [Trie.get_set] at hy
      split at hy
      · cases hy; exact hh (f, st.n) (by simp)
      · exact hg (fun q hq => hh q (by simp [hq])) j (by omega) y hy
    · cases h
  | pop p d =>
    simp only [Ctx.cmd] at h
    split at h
    · rename_i f m rest g hs hg'
      split at h
      · rename_i hd
        simp only [Option.some.injEq] at h; subst h
        rw [hs] at hi hg
        obtain ⟨_, _, hr⟩ := hi
        simp only [beq_iff_eq] at hd
        apply c.inv_add hw ht hM hr
        intro hh
        rw [c.H_implies hw hd]
        intro hf
        simp only [State.prem] at hg'
        split at hg'
        · rename_i hpn
          exact hg (fun q hq => by
            simp only [List.mem_cons] at hq
            rcases hq with rfl | hq
            · exact hf
            · exact hh q hq) p hpn g hg'
        · cases hg'
      · cases h
    · cases h

theorem Ctx.run_sound {asserts : List Nat} {P : Proof} (hA : ∀ a ∈ asserts, c.H M a)
    (hE : ∀ j e, Tab.at P.eqvs j = some e → c.V M e.x = c.V M e.y)
    (htt : c.isTt P.tt = true) (hff : c.isFf P.ff = true) :
    ∀ (xs : List Cmd) (st st' : State), c.Inv M st.facts st.n st.stack → c.run asserts P st xs = some st' →
      c.Inv M st'.facts st'.n st'.stack
  | [], st, st', hi, h => by simp only [Ctx.run, Option.some.injEq] at h; subst h; exact hi
  | x :: xs, st, st', hi, h => by
    simp only [Ctx.run] at h
    split at h
    · rename_i st1 h1
      exact Ctx.run_sound hA hE htt hff xs st1 st' (c.cmd_sound hw ht hM hA hE htt hff hi h1) h
    · cases h

end

/-- No model satisfies a script whose CPC proof the checker accepts. -/
theorem Proof.unsat {SP : Vik.Lower.SProblem} {P : Proof} (hc : P.check SP = true) (M : Surf.Model R U)
    (hM : M.Sound SP.sig) (hD : ∀ d ∈ SP.defs, d.Holds SP.sig M)
    (hin : ∀ a ∈ SP.asserts, Surf.holds M.toInterp SP.nodes a) : False := by
  simp only [Proof.check, Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨hlen, hw⟩, ht⟩, htt⟩, hff⟩, hE⟩, hrun⟩ := hc
  let c := P.ctx SP
  have hA : ∀ a ∈ SP.asserts, c.H M a := by
    intro a ha
    have h := hin a ha
    rcases Nat.lt_or_ge a SP.nodes.length with hl | hl
    · have e : c.nodes = SP.nodes ++ P.extra := rfl
      simp only [Ctx.H, Surf.holds] at h ⊢
      rw [e, val_append hl]; exact h
    · exfalso
      simp only [Surf.holds, Surf.val, Low.get] at h
      rw [List.getElem?_eq_none (by rw [values_length]; exact hl)] at h
      simp at h
  have hE' := c.eqvs_sound hw ht hM hD hE
  split at hrun
  · rename_i st hst
    simp only [Bool.and_eq_true, List.isEmpty_iff, decide_eq_true_eq, Option.any_eq_true] at hrun
    obtain ⟨⟨hs, hn⟩, x, hx, hf⟩ := hrun
    have hi := c.run_sound hw ht hM hA hE' htt hff P.cmds ⟨.leaf, 0, []⟩ st
      (fun _ j hj => absurd hj (Nat.not_lt_zero _)) hst
    have hg := c.good_of_inv hw ht hM hi
    rw [hs] at hg
    simp only [Ctx.isFf, beq_iff_eq] at hf
    exact c.H_ff hw hf (hg (fun q hq => by simp at hq) (st.n - 1) (by omega) x hx)
  · cases hrun

end Vik.Cpc
