import Vik.Tab

/-!
# Clausal proofs

A checker for the clausal proofs of `cdclt` (`cdclt/Proof.scala`), and its
soundness: every clause a checked proof derives holds under every assignment
that satisfies its input and lemma clauses. The inputs and lemmas are checked
apart, by the checkers of their origins and of the theories.

A step is an input clause, a lemma, or a clause derived by reverse unit
propagation over hints: with every literal of the clause false, each hint in
turn has all its literals false but one, which becomes true, until a hint has
them all false.
-/

namespace Vik.Clausal

/-- A literal: a variable, positive or negated. -/
structure Lit where
  var : Nat
  pos : Bool
  deriving DecidableEq, Repr

def Lit.neg (l : Lit) : Lit := ⟨l.var, !l.pos⟩

abbrev Clause := List Lit

/-- An assignment of the variables. -/
abbrev Assignment := Nat → Bool

def Lit.holds (ρ : Assignment) (l : Lit) : Prop := ρ l.var = l.pos

def Clause.holds (ρ : Assignment) (c : Clause) : Prop := ∃ l ∈ c, l.holds ρ

theorem Lit.neg_neg (l : Lit) : l.neg.neg = l := by
  cases l; simp [Lit.neg]

theorem Lit.holds_neg (ρ : Assignment) (l : Lit) : l.neg.holds ρ ↔ ¬l.holds ρ := by
  cases l with
  | mk v p => cases h : ρ v <;> cases p <;> simp [Lit.holds, Lit.neg, h]

/-! ## Truth tables

The literals taken as true during unit propagation, as a binary trie from
variables to their values: the kernel looks a variable up in about `log₂ v`
steps, where a list of the literals takes as many steps as the list is long. -/

/-- A partial assignment of the variables. -/
inductive TT where
  | leaf
  | node (v : Option Bool) (l r : TT)

def TT.get : TT → Nat → Option Bool
  | .leaf, _ => none
  | .node v l r, n =>
    match n with
    | 0 => v
    | n + 1 => if n % 2 == 0 then l.get (n / 2) else r.get (n / 2)

/-- The table of variable `n` alone, `n < f`. -/
def TT.single : Nat → Nat → Bool → TT
  | 0, _, _ => .leaf
  | _ + 1, 0, b => .node (some b) .leaf .leaf
  | f + 1, n + 1, b =>
    if n % 2 == 0 then .node none (TT.single f (n / 2) b) .leaf else .node none .leaf (TT.single f (n / 2) b)

def TT.set : TT → Nat → Bool → TT
  | .leaf, n, b => TT.single (n + 1) n b
  | .node _ l r, 0, b => .node (some b) l r
  | .node v l r, n + 1, b => if n % 2 == 0 then .node v (l.set (n / 2) b) r else .node v l (r.set (n / 2) b)

theorem TT.get_leaf (j : Nat) : TT.leaf.get j = none := by cases j <;> rfl

theorem TT.half_iff {j n : Nat} (hp : j % 2 = n % 2) : j / 2 = n / 2 ↔ j = n := by
  constructor <;> intro h <;> omega

theorem TT.get_single : ∀ (f n : Nat) (b : Bool), n < f → ∀ j, (TT.single f n b).get j = if j = n then some b else none
  | 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | f + 1, 0, b, _, j => by
    cases j with
    | zero => rfl
    | succ j => simp [TT.single, TT.get]
  | f + 1, n + 1, b, h, j => by
    cases j with
    | zero => simp only [TT.single]; split <;> simp [TT.get]
    | succ j =>
      have ih := TT.get_single f (n / 2) b (by omega)
      simp only [TT.single, Nat.add_right_cancel_iff]
      by_cases hn : n % 2 = 0 <;> by_cases hj : j % 2 = 0 <;>
        simp only [hn, hj, beq_iff_eq, if_true, if_false, TT.get, ih,
          not_false_eq_true]
      · simp only [TT.half_iff (show j % 2 = n % 2 by omega)]
      · have : j ≠ n := by omega
        simp [this]
      · have : j ≠ n := by omega
        simp [this]
      · simp only [TT.half_iff (show j % 2 = n % 2 by omega)]

theorem TT.get_set : ∀ (t : TT) (k : Nat) (b : Bool) (j : Nat), (t.set k b).get j = if j = k then some b else t.get j
  | .leaf, k, b, j => by
    simp only [TT.set, TT.get_leaf]
    exact TT.get_single (k + 1) k b (Nat.lt_succ_self k) j
  | .node v l r, 0, b, j => by
    cases j with
    | zero => rfl
    | succ j => simp [TT.set, TT.get]
  | .node v l r, k + 1, b, j => by
    cases j with
    | zero => simp only [TT.set]; split <;> simp [TT.get]
    | succ j =>
      simp only [TT.set, Nat.add_right_cancel_iff]
      by_cases hk : k % 2 = 0 <;> by_cases hj : j % 2 = 0 <;>
        simp only [hk, hj, beq_iff_eq, if_true, if_false, TT.get, TT.get_set,
          not_false_eq_true]
      · simp only [TT.half_iff (show j % 2 = k % 2 by omega)]
      · have : j ≠ k := by omega
        simp [this]
      · have : j ≠ k := by omega
        simp [this]
      · simp only [TT.half_iff (show j % 2 = k % 2 by omega)]

/-- `t` agrees with `ρ`. -/
def TT.Agrees (ρ : Assignment) (t : TT) : Prop := ∀ v b, t.get v = some b → ρ v = b

theorem TT.agrees_leaf (ρ : Assignment) : TT.leaf.Agrees ρ := fun v b h => by rw [TT.get_leaf] at h; cases h

theorem TT.agrees_set {ρ : Assignment} {t : TT} (ht : t.Agrees ρ) {k : Nat} {b : Bool} (hk : ρ k = b) :
    (t.set k b).Agrees ρ := by
  intro v c h
  rw [TT.get_set] at h
  split at h
  · rename_i e; subst e; cases h; exact hk
  · exact ht v c h

/-- Whether `l` is true in `t`. -/
def TT.isTrue (t : TT) (l : Lit) : Bool := t.get l.var == some l.pos

/-- Whether `l` is false in `t`. -/
def TT.isFalse (t : TT) (l : Lit) : Bool := t.get l.var == some !l.pos

theorem TT.isFalse_sound {ρ : Assignment} {t : TT} (ht : t.Agrees ρ) {l : Lit} (h : t.isFalse l = true) :
    ¬l.holds ρ := by
  unfold TT.isFalse at h
  simp only [beq_iff_eq] at h
  have := ht _ _ h
  unfold Lit.holds; rw [this]; cases l.pos <;> simp

/-! ## Reverse unit propagation -/

/-- One hint under the literals `t` takes as true: `none` if the hint is
    satisfied or has two open literals (the check fails), `some none` if all its
    literals are false, `some (some u)` if `u` is its one open literal. -/
def unit (t : TT) (h : Clause) : Option (Option Lit) :=
  if h.any t.isTrue then none
  else
    match h.filter (fun l => !t.isFalse l) with
    | [] => some none
    | u :: rest => if rest.all (· == u) then some (some u) else none

/-- Follows the hints from the literals `t` takes as true: whether they end in
    a hint whose literals are all false. -/
def propagate (db : List Clause) (t : TT) : List Nat → Bool
  | [] => false
  | i :: hints =>
    match db[i]? with
    | none => false
    | some h =>
      match unit t h with
      | some none => true
      | some (some u) => propagate db (t.set u.var u.pos) hints
      | none => false

/-- The negations of the literals of `c` taken as true, after `t`: `none` if
    `c` is a tautology. -/
def negs : TT → Clause → Option TT
  | t, [] => some t
  | t, l :: c =>
    match t.get l.var with
    | some b => if b == !l.pos then negs t c else none
    | none => negs (t.set l.var !l.pos) c

/-- Whether `c` follows from the clauses `db` by unit propagation over `hints`:
    a tautology does, and otherwise the negations of its literals must lead to a
    hint with all literals false. -/
def rup (db : List Clause) (c : Clause) (hints : List Nat) : Bool :=
  match negs .leaf c with
  | none => true
  | some t => propagate db t hints

theorem unit_sound {ρ : Assignment} {t : TT} {h : Clause} (ht : t.Agrees ρ)
    (hh : h.holds ρ) :
    (unit t h = some none → False) ∧ (∀ u, unit t h = some (some u) → u.holds ρ) := by
  obtain ⟨l, hl, hlρ⟩ := hh
  unfold unit
  split
  · simp
  · rename_i hsat
    have hl_in : l ∈ h.filter (fun l => !t.isFalse l) := by
      rw [List.mem_filter]
      refine ⟨hl, ?_⟩
      cases e : t.isFalse l
      · rfl
      · exact absurd hlρ (TT.isFalse_sound ht e)
    split
    · rename_i he; rw [he] at hl_in; simp at hl_in
    · rename_i u rest he
      rw [he] at hl_in
      split
      · rename_i hall
        refine ⟨by simp, ?_⟩
        intro v hv
        simp only [Option.some.injEq] at hv
        subst hv
        rcases List.mem_cons.mp hl_in with h1 | h1
        · rw [← h1]; exact hlρ
        · have := List.all_eq_true.mp hall l h1
          simp only [beq_iff_eq] at this
          rw [← this]; exact hlρ
      · simp

theorem propagate_sound {ρ : Assignment} {db : List Clause} (hdb : ∀ c ∈ db, c.holds ρ) :
    ∀ (hints : List Nat) (t : TT), t.Agrees ρ → propagate db t hints = true → False := by
  intro hints
  induction hints with
  | nil => intro t _ h; simp [propagate] at h
  | cons i hints ih =>
    intro t ht h
    unfold propagate at h
    split at h
    · simp at h
    · rename_i c hc
      have hcρ : c.holds ρ := hdb c (List.mem_of_getElem? hc)
      have ⟨h1, h2⟩ := unit_sound ht hcρ
      split at h
      · rename_i he; exact h1 he
      · rename_i u he
        exact ih _ (TT.agrees_set ht (h2 u he)) h
      · simp at h

/-- With every literal of `c` false, its negations agree with `ρ`. -/
theorem negs_sound {ρ : Assignment} {c : Clause} (hc : ¬c.holds ρ) :
    ∀ (d : Clause), (∀ l ∈ d, l ∈ c) → ∀ t, t.Agrees ρ → ∃ t', negs t d = some t' ∧ t'.Agrees ρ
  | [], _, t, ht => ⟨t, rfl, ht⟩
  | l :: d, hd, t, ht => by
    have hl : ρ l.var = !l.pos := by
      have : ¬l.holds ρ := fun h => hc ⟨l, hd l List.mem_cons_self, h⟩
      unfold Lit.holds at this
      cases e : ρ l.var <;> cases e' : l.pos <;> simp_all
    have hd' : ∀ m ∈ d, m ∈ c := fun m hm => hd m (List.mem_cons_of_mem l hm)
    simp only [negs]
    split
    · rename_i b hb
      have := ht _ _ hb
      rw [hl] at this
      subst this
      simp only [BEq.rfl, if_true]
      exact negs_sound hc d hd' t ht
    · exact negs_sound hc d hd' _ (TT.agrees_set ht hl)

/-- A clause that passes `rup` holds wherever the clauses `db` hold. -/
theorem rup_sound {ρ : Assignment} {db : List Clause} {c : Clause} {hints : List Nat}
    (hdb : ∀ c ∈ db, c.holds ρ) (h : rup db c hints = true) : c.holds ρ := by
  apply Classical.byContradiction
  intro hc
  obtain ⟨t, ht, hta⟩ := negs_sound hc c (fun _ m => m) .leaf (TT.agrees_leaf ρ)
  unfold rup at h
  rw [ht] at h
  exact propagate_sound hdb hints t hta h

/-! ## Proofs -/

/-- A step of a proof: an input clause, a lemma of a theory, or a clause derived
    by `rup` from the clauses of earlier steps, by their indices. -/
inductive Step where
  | input (c : Clause)
  | lemma (c : Clause)
  | derived (c : Clause) (hints : List Nat)

def Step.clause : Step → Clause
  | .input c => c
  | .lemma c => c
  | .derived c _ => c

/-- Checks the derived steps, each against the clauses of the steps before it:
    the clauses of the steps if they all pass, `none` otherwise. -/
def check : List Clause → List Step → Option (List Clause)
  | db, [] => some db
  | db, .derived c hints :: rest => if rup db c hints then check (db ++ [c]) rest else none
  | db, s :: rest => check (db ++ [s.clause]) rest

/-- The premises of a proof: its input and lemma steps. -/
def Step.premise : Step → Bool
  | .derived _ _ => false
  | _ => true

theorem check_sound {ρ : Assignment} :
    ∀ (steps : List Step) (db out : List Clause), (∀ c ∈ db, c.holds ρ) →
      (∀ s ∈ steps, s.premise = true → s.clause.holds ρ) →
      check db steps = some out → ∀ c ∈ out, c.holds ρ := by
  intro steps
  induction steps with
  | nil => intro db out hdb _ h; simp only [check, Option.some.injEq] at h; rw [← h]; exact hdb
  | cons s rest ih =>
    intro db out hdb hprem h
    have hrest : ∀ s ∈ rest, s.premise = true → s.clause.holds ρ :=
      fun s hs => hprem s (List.mem_cons_of_mem _ hs)
    have extend : ∀ c, c.holds ρ → ∀ d ∈ db ++ [c], d.holds ρ := by
      intro c hc d hd
      rcases List.mem_append.mp hd with hd | hd
      · exact hdb d hd
      · rw [List.mem_singleton.mp hd]; exact hc
    cases s with
    | derived c hints =>
      simp only [check] at h
      split at h
      · rename_i hr
        exact ih _ out (extend c (rup_sound hdb hr)) hrest h
      · simp at h
    | input c =>
      simp only [check, Step.clause] at h
      exact ih _ out (extend c (hprem _ (List.mem_cons_self ..) rfl)) hrest h
    | lemma c =>
      simp only [check, Step.clause] at h
      exact ih _ out (extend c (hprem _ (List.mem_cons_self ..) rfl)) hrest h

/-- A proof checks with a conclusion: the steps pass, and the conclusion is the
    clause of one of them. -/
def accepts (steps : List Step) (conclusion : Nat) (goal : Clause) : Bool :=
  match check [] steps with
  | some db => db[conclusion]? == some goal
  | none => false

/-- The conclusion of an accepted proof holds under every assignment that
    satisfies its premises. -/
theorem accepts_sound {ρ : Assignment} {steps : List Step} {conclusion : Nat} {goal : Clause}
    (hprem : ∀ s ∈ steps, s.premise = true → s.clause.holds ρ)
    (h : accepts steps conclusion goal = true) : goal.holds ρ := by
  unfold accepts at h
  split at h
  · rename_i db hdb
    have hall := check_sound steps [] db (by simp) hprem hdb
    simp only [beq_iff_eq] at h
    exact hall goal (List.mem_of_getElem? h)
  · simp at h

/-! ## A faster check

`check` looks up each hint in the clauses before its step, a list it extends
at each step: the kernel takes time quadratic in the steps. `checkT` looks
hints up in one tree of all the steps' clauses, bounded by the step's index,
and gives the same answer.
-/

/-- `propagate` over the first `k` clauses of `tab`. -/
def propagateT (tab : List Clause) (k : Nat) (τ : TT) : List Nat → Bool
  | [] => false
  | i :: hints =>
    match (if i < k then Tab.at tab i else none) with
    | none => false
    | some h =>
      match unit τ h with
      | some none => true
      | some (some u) => propagateT tab k (τ.set u.var u.pos) hints
      | none => false

theorem propagateT_eq (tab : List Clause) (k : Nat) :
    ∀ (hints : List Nat) (τ : TT), propagateT tab k τ hints = propagate (tab.take k) τ hints
  | [], _ => rfl
  | i :: hints, τ => by
    have e : (if i < k then Tab.at tab i else none) = (tab.take k)[i]? := by
      rw [List.getElem?_take, Tab.at_eq]
    simp only [propagateT, propagate, e]
    split <;> try rfl
    split <;> try rfl
    exact propagateT_eq tab k hints _

def rupT (tab : List Clause) (k : Nat) (c : Clause) (hints : List Nat) : Bool :=
  match negs .leaf c with
  | none => true
  | some t => propagateT tab k t hints

/-- Whether the steps from the `k`-th on pass, `tab` the clauses of all steps. -/
def checkT (tab : List Clause) : Nat → List Step → Bool
  | _, [] => true
  | k, .derived c hints :: rest => rupT tab k c hints && checkT tab (k + 1) rest
  | k, _ :: rest => checkT tab (k + 1) rest

theorem checkT_append (tab : List Clause) :
    ∀ (l₁ l₂ : List Step) (k : Nat), checkT tab k (l₁ ++ l₂) = (checkT tab k l₁ && checkT tab (k + l₁.length) l₂)
  | [], l₂, k => by simp [checkT]
  | .derived c hints :: l₁, l₂, k => by
    simp only [List.cons_append, checkT, checkT_append tab l₁ l₂ (k + 1), List.length_cons, Bool.and_assoc]
    rw [show k + 1 + l₁.length = k + (l₁.length + 1) by omega]
  | .input c :: l₁, l₂, k => by
    simp only [List.cons_append, checkT, checkT_append tab l₁ l₂ (k + 1), List.length_cons]
    rw [show k + 1 + l₁.length = k + (l₁.length + 1) by omega]
  | .lemma c :: l₁, l₂, k => by
    simp only [List.cons_append, checkT, checkT_append tab l₁ l₂ (k + 1), List.length_cons]
    rw [show k + 1 + l₁.length = k + (l₁.length + 1) by omega]

theorem checkT_sound (tab : List Clause) :
    ∀ (rest : List Step) (k : Nat), tab.drop k = rest.map Step.clause →
      checkT tab k rest = true → check (tab.take k) rest = some tab
  | [], k, hd, _ => by
    simp only [List.map_nil, List.drop_eq_nil_iff] at hd
    simp only [check, List.take_of_length_le hd]
  | s :: rest, k, hd, h => by
    have hk : tab[k]? = some s.clause := by
      have : (tab.drop k)[0]? = some s.clause := by rw [hd]; rfl
      rwa [List.getElem?_drop, Nat.add_zero] at this
    have ht : tab.take (k + 1) = tab.take k ++ [s.clause] := by
      rw [List.take_add_one, hk]; rfl
    have hd' : tab.drop (k + 1) = rest.map Step.clause := by
      rw [← List.drop_drop, hd]; rfl
    cases s with
    | derived c hints =>
      simp only [checkT, Bool.and_eq_true] at h
      have hr : rup (tab.take k) c hints = true := by
        have h1 := h.1
        unfold rupT at h1
        unfold rup
        split <;> rename_i e <;> rw [e] at h1
        all_goals first | rfl | (rw [← propagateT_eq]; simpa using h1)
      simp only [check, hr, ↓reduceIte]
      simp only [Step.clause] at ht
      rw [← ht]; exact checkT_sound tab rest (k + 1) hd' h.2
    | input c =>
      simp only [checkT] at h
      simp only [check, Step.clause]
      simp only [Step.clause] at ht
      rw [← ht]; exact checkT_sound tab rest (k + 1) hd' h
    | lemma c =>
      simp only [checkT] at h
      simp only [check, Step.clause]
      simp only [Step.clause] at ht
      rw [← ht]; exact checkT_sound tab rest (k + 1) hd' h

theorem check_of_checkT {steps : List Step} (h : checkT (steps.map Step.clause) 0 steps = true) :
    check [] steps = some (steps.map Step.clause) := by
  have := checkT_sound (steps.map Step.clause) steps 0 (by simp) h
  simpa using this

/-- In particular, an accepted proof of the empty clause leaves no assignment
    that satisfies its premises. -/
theorem refutes {steps : List Step} {conclusion : Nat} (h : accepts steps conclusion [] = true)
    (ρ : Assignment) : ¬ ∀ s ∈ steps, s.premise = true → s.clause.holds ρ := by
  intro hprem
  obtain ⟨_, hl, _⟩ := accepts_sound hprem h
  simp at hl

end Vik.Clausal
