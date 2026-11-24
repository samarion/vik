import Vik.Lowered
import Vik.Cert.Clausal
import Vik.Cert.Lia

/-!
# Input clauses

A checker for the input clauses of a proof (`InputClauses` in
`vik/ProofCheck.scala`), and its soundness: each clause it accepts holds under
the assignment that gives each variable the truth of the formula it stands
for, in any model of the problem.

A clause comes with its origin: a clause of the definition of a variable by
its formula (Tseitin), an assertion, possibly guarded by the literal of a
level, a level popped for good, or an axiom of the theories.
-/

set_option linter.unusedSectionVars false

namespace Vik.Low

open Lean.Grind Vik.Real Vik.Clausal

/-! ## Linear combinations -/

/-- `Σ a·u` with the pairs merged by unknown, when sorted. -/
def canon (f : Lia.Form) : Lia.Form := f.foldl (fun acc p => Lia.add acc [p]) []

/-- The node `i` as a linear combination of nodes and a constant. -/
def lin (nodes : List Node) (i : Nat) : Lia.Form × Int :=
  match Tab.at nodes i with
  | some (.num v) => ([], v)
  | some (.linear ts c) => (ts.map (fun p => (p.2, (p.1 : Rat))), c)
  | _ => ([(i, 1)], 0)

/-- `a - b`, if it is a constant. -/
def constant (nodes : List Node) (a b : Nat) : Option Int :=
  let (fa, ca) := lin nodes a
  let (fb, cb) := lin nodes b
  if canon (fa ++ Lia.neg fb) = [] then some (ca - cb) else none

/-! ## Literals and formulas -/

/-- What the checker of input clauses is given: the node table, the formula
    each variable stands for, the literal of `true`, the assertions, and the
    literals of levels with the formulas each guards. -/
structure Enc where
  nodes : List Node
  sortOf : List Nat
  sig : Sig
  meaning : List (Option Nat)
  trueLit : Lit
  inputs : List Nat
  levels : List (Nat × List Nat)
  /-- The variables of the conclusion: the levels assumed by the last check. -/
  assumed : List Nat
  /-- The datatypes: for each sort, its constructors with their testers and
      selectors, as symbols. -/
  datatypes : List (Nat × List (Nat × Nat × List Nat))
  /-- The symbols of array stores. -/
  stores : List Nat
  /-- The extensionality instances, in order: the equality `f = g`, the
      equality of `f` and `g` applied to the witnesses, and the witnesses. -/
  exts : List (Nat × Nat × List Nat)
  /-- The witnesses: those of the instances, and those that only come with a
      range. -/
  witnesses : List Nat
  /-- The sorts of bit-vector indices, with their widths. -/
  bvIndex : List (Nat × Nat)

def Enc.node (e : Enc) (i : Nat) : Option Node := Tab.at e.nodes i

def Enc.meaningOf (e : Enc) (v : Nat) : Option Nat := (Tab.at e.meaning v).getD none

@[simp] theorem Enc.node_eq (e : Enc) (i : Nat) : e.node i = e.nodes[i]? := Tab.at_eq _ _

@[simp] theorem Enc.meaningOf_eq (e : Enc) (v : Nat) : e.meaningOf v = (e.meaning[v]?).getD none := by
  simp [Enc.meaningOf]

def Enc.guarded (e : Enc) (v : Nat) : Option (List Nat) := e.levels.lookup v

/-- The width of witness `n`, if it is an index of bit-vectors. -/
def Enc.width (e : Enc) (n : Nat) : Option Nat :=
  if e.witnesses.contains n then
    match e.sig.decls[n]? with
    | some s => e.bvIndex.lookup s
    | none => none
  else none

def holdsLit (e : Enc) (b : Bool) : Lit := if b then e.trueLit else e.trueLit.neg

/-- Whether the literal `l` stands for formula `f`, as the encoder reads
    formulas: through negations, implications and constant comparisons. -/
def denotes (e : Enc) : Nat → Lit → Nat → Bool
  | 0, _, _ => false
  | fuel + 1, l, f =>
    let plain := l.pos && e.meaningOf l.var == some f
    match e.node f with
    | some (.not g) => denotes e fuel l.neg g
    | some .tt => l == e.trueLit
    | some .ff => l == e.trueLit.neg
    | some (.implies a b) =>
      l.pos &&
        match e.meaningOf l.var with
        | some m =>
          match e.node m with
          | some (.or [n, b']) => b' == b && e.node n == some (.not a)
          | _ => false
        | none => false
    | some (.eq a b) =>
      if a == b then l == e.trueLit
      else
        -- One atom stands for both orientations of an equality.
        plain || (l.pos && match e.meaningOf l.var with
          | some m => e.node m == some (.eq b a)
          | none => false)
    | some (.le a b) =>
      match constant e.nodes a b with
      | some v => l == holdsLit e (decide (v ≤ 0))
      | none => plain
    | some (.lt a b) =>
      match constant e.nodes a b with
      | some v => l == holdsLit e (decide (v < 0))
      | none => plain
    | _ => plain

/-- Whether a literal of `c` stands for `f`, or for its negation. -/
def has (e : Enc) (c : Clause) (f : Nat) : Bool := c.any (fun l => denotes e (f + 1) l f)
def hasNot (e : Enc) (c : Clause) (f : Nat) : Bool := c.any (fun l => denotes e (f + 1) l.neg f)

/-! ## Origins -/

inductive Origin where
  | definition
  | assertion (f : Nat)
  | retired
  /-- One of the testers of `t` holds: the disjunction `or`. -/
  | exhaustive (t or : Nat)
  /-- Two shared terms are equal or one is below the other, through the
      formulas `lt` and `le` on them. -/
  | sharedSplit (lt le : Nat)
  | numerals
  /-- `f ≠ g ∨ f(x) = g(x)`, with `eqfg` the equality `f = g`. -/
  | congruence (eqfg : Nat)
  | readOverWrite
  /-- `f = g ∨ f(w₁)…(wₙ) ≠ g(w₁)…(wₙ)`, the instance `k` of the answer. -/
  | extensionality (k : Nat)
  /-- `0 ≤ w` or `w ≤ 2ʷ - 1`, the formula `f`, for a witness `w` of a
      bit-vector index of width `w`. -/
  | witnessRange (f : Nat)
  /-- `0 ≤ t` or `t ≤ 2ʷ - 1`, the formula `f`, for a node `t` of a sort of
      bit-vectors of width `w`. -/
  | sortRange (f : Nat)
  /-- `f = g ∨ f(i₁) ≠ g(i₁) ∨ …`, the equality `eq`, for arrays `f` and `g`
      made by stores from the same base, the `iₖ` their indices, and the
      disequalities `ds`: arrays from one base differ only where written. -/
  | sameBase (eq : Nat) (ds : List Nat)
  deriving Repr

def Enc.numeric (e : Enc) (i : Nat) : Bool := i < e.nodes.length && e.sig.numeric ((Tab.at e.sortOf i).getD 0)

def defOk (e : Enc) (c : Clause) : Bool :=
  c.any fun d =>
    match e.meaningOf d.var with
    | some m =>
      match e.node m with
      | some .tt => d == e.trueLit
      | some (.and as) => if d.pos then as.all (hasNot e c) else as.any (has e c)
      | some (.or as) => if d.pos then as.any (hasNot e c) else as.all (has e c)
      | some (.iff x y) =>
        if d.pos then (has e c x && has e c y) || (hasNot e c x && hasNot e c y)
        else (hasNot e c x && has e c y) || (has e c x && hasNot e c y)
      | some (.ite x t f) =>
        if d.pos then (hasNot e c x && hasNot e c t) || (has e c x && hasNot e c f)
        else (hasNot e c x && has e c t) || (has e c x && has e c f)
      | some (.pred t) =>
        match e.node t with
        | some (.bterm inner) => if d.pos then hasNot e c inner else has e c inner
        | _ => false
      | _ => false
    | none => false

/-- The formula a positive literal of `c` stands for. -/
def positive (e : Enc) (l : Lit) : Option Nat := if l.pos then e.meaningOf l.var else none

/-- Whether the tests `ps` are those of the testers `cs` on `t`. -/
def testsOk (e : Enc) (t : Nat) : List Nat → List (Nat × Nat × List Nat) → Bool
  | [], [] => true
  | p :: ps, (_, tester, _) :: cs =>
    (match e.node p with
      | some (.pred q) =>
        match e.node q with
        | some (.app k [t']) => t' == t && e.node k == some (.const tester)
        | _ => false
      | _ => false) && testsOk e t ps cs
  | _, _ => false

/-- The two sides of an equality, as `=` or as two bounds. -/
def sides (e : Enc) (m : Nat) : Option (Nat × Nat) :=
  match e.node m with
  | some (.eq l r) => some (l, r)
  | some (.and [x, y]) =>
    match e.node x, e.node y with
    | some (.le l r), some (.le r' l') => if l == l' && r == r' then some (l, r) else none
    | _, _ => none
  | _ => none

def storeOk (e : Enc) (c : Clause) (r w : Nat) : Bool :=
  match e.node r with
  | some (.app s [j]) =>
    match e.node s with
    | some (.app k [a, i, v]) =>
      (match e.node k with
        | some (.const n) => e.stores.contains n
        | _ => false) &&
      ((j == i && w == v) ||
        (e.node w == some (.app a [j]) &&
          c.any fun l => match positive e l with
            | some m => sides e m == some (i, j) || sides e m == some (j, i)
            | none => false))
    | _ => false
  | _ => false

/-- The base of the stores that make `t`, with the indices they write,
    outermost first (`t` itself and none when it is no store). -/
def chain (e : Enc) : Nat → Nat → Option (Nat × List Nat)
  | 0, _ => none
  | fuel + 1, t =>
    match e.node t with
    | some (.app k [a, i, _]) =>
      match e.node k with
      | some (.const n) =>
        if e.stores.contains n then (chain e fuel a).map fun p => (p.1, i :: p.2) else some (t, [])
      | _ => some (t, [])
    | _ => some (t, [])

/-- A bound of the range of a witness `w` of a bit-vector index: `0 ≤ w` or
    `w ≤ 2ʷ - 1`. -/
def witnessLe (e : Enc) (f : Nat) : Bool :=
  match e.node f with
  | some (.le a b) =>
    match e.node a, e.node b with
    | some (.num z), some (.const n) => z == 0 && (e.width n).isSome
    | some (.const n), some (.num v) =>
      match e.width n with
      | some w => v == 2 ^ w - 1
      | none => false
    | _, _ => false
  | _ => false

/-- A bound of the range of a node `t` of a sort of bit-vectors: `0 ≤ t` or
    `t ≤ 2ʷ - 1`. -/
def rangeLe (e : Enc) (f : Nat) : Bool :=
  match e.node f with
  | some (.le a b) =>
    match e.node a, e.node b with
    | some (.num z), _ =>
      z == 0 && decide (b < e.nodes.length) && (e.bvIndex.lookup ((Tab.at e.sortOf b).getD 0)).isSome
    | _, some (.num v) =>
      decide (a < e.nodes.length) &&
        match e.bvIndex.lookup ((Tab.at e.sortOf a).getD 0) with
        | some w => v == 2 ^ w - 1
        | none => false
    | _, _ => false
  | _ => false

/-- A bound `p` accepts, or the conjunction of two. -/
def rangeOf (e : Enc) (p : Nat → Bool) (f : Nat) : Bool :=
  p f ||
    match e.node f with
    | some (.and [x, y]) => p x && p y
    | _ => false

def inputOk (e : Enc) (c : Clause) : Origin → Bool
  | .definition => defOk e c
  | .assertion f =>
    has e c f && (e.inputs.contains f || c.any fun l =>
      !l.pos && match e.guarded l.var with
        | some fs => fs.contains f
        | none => false)
  | .retired => c.any fun l => !l.pos && (e.guarded l.var).isSome && !e.assumed.contains l.var
  | .exhaustive t o =>
    t < e.nodes.length && has e c o &&
      match e.datatypes.lookup ((Tab.at e.sortOf t).getD 0), e.node o with
      | some cs, some (.or ps) => testsOk e t ps cs
      | _, _ => false
  | .sharedSplit lt le =>
    c.any fun l => match positive e l with
      | some m =>
        match e.node m with
        | some (.eq a b) =>
          e.numeric a && e.numeric b &&
            ((e.node lt == some (.lt a b) && e.node le == some (.le a b)) ||
              (e.node lt == some (.lt b a) && e.node le == some (.le b a)))
            && has e c lt && hasNot e c le
        | some (.le a b) => e.node lt == some (.lt a b) && hasNot e c lt
        | _ => false
      | none => false
  | .numerals =>
    c.any fun l => match e.meaningOf l.var with
      | some m =>
        match e.node m with
        | some (.eq a b) =>
          match constant e.nodes a b with
          | some v => (v == 0) == l.pos && (v != 0 || (e.numeric a && e.numeric b))
          | none => false
        | _ => false
      | none => false
  | .congruence eqfg =>
    c.any fun l => match positive e l with
      | some m =>
        match e.node m with
        | some (.eq p q) =>
          match e.node p, e.node q with
          | some (.app f xs), some (.app g ys) =>
            xs == ys && e.node eqfg == some (.eq f g) && hasNot e c eqfg
          | _, _ => false
        | _ => false
      | none => false
  | .readOverWrite =>
    c.any fun l => match positive e l with
      | some m =>
        match sides e m with
        | some (r, w) => storeOk e c r w || storeOk e c w r
        | none => false
      | none => false
  | .extensionality k =>
    match e.exts[k]? with
    | some (eq, eqw, _) => has e c eq && hasNot e c eqw
    | none => false
  | .witnessRange f => has e c f && rangeOf e (witnessLe e) f
  | .sortRange f => has e c f && rangeOf e (rangeLe e) f
  | .sameBase q ds =>
    has e c q &&
      match e.node q with
      | some (.eq f g) =>
        match chain e (f + 1) f, chain e (g + 1) g with
        | some (b, ws), some (b', ws') =>
          b == b' && (ws ++ ws').all fun i => ds.any fun d =>
            hasNot e c d && match e.node d with
              | some (.eq p r) => e.node p == some (.app f [i]) && e.node r == some (.app g [i])
              | _ => false
        | _, _ => false
      | _ => false

/-! ## Soundness of the readings -/

variable {R U : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R]
  [OrderedRing R] [IsCharP R 0]

attribute [local instance low] Lean.Grind.Ring.intCast

/-- The numeric values of the nodes, as unknowns of linear combinations. -/
noncomputable def nums (I : Interp R U) (nodes : List Node) (u : Nat) : R := (val I nodes u).toR

theorem rat_one : rat (1 : Rat) = (1 : R) := by
  have := Lia.rat_intCast (R := R) 1
  simp only [Ring.intCast_one] at this
  exact this

theorem eval_canon (ρ : Nat → R) (f : Lia.Form) : Lia.eval ρ (canon f) = Lia.eval ρ f := by
  unfold canon
  suffices ∀ acc, Lia.eval ρ (f.foldl (fun acc p => Lia.add acc [p]) acc) = Lia.eval ρ acc + Lia.eval ρ f by
    rw [this]; simp [Lia.eval]; grind
  induction f with
  | nil => intro acc; simp [Lia.eval]; grind
  | cons p f ih =>
    intro acc
    simp only [List.foldl_cons]
    rw [ih, Lia.eval_add]
    obtain ⟨u, a⟩ := p
    simp only [Lia.eval]; grind

theorem eval_append (ρ : Nat → R) (f g : Lia.Form) : Lia.eval ρ (f ++ g) = Lia.eval ρ f + Lia.eval ρ g := by
  induction f with
  | nil => simp [Lia.eval]; grind
  | cons p f ih => obtain ⟨u, a⟩ := p; simp only [List.cons_append, Lia.eval, ih]; grind

section
variable {I : Interp R U} {nodes : List Node} (hw : wellFormed nodes = true)
include hw

theorem lin_sound (i : Nat) :
    (val I nodes i).toR = Lia.eval (nums I nodes) (lin nodes i).1 + ((lin nodes i).2 : R) := by
  unfold lin
  rw [Tab.at_eq]
  split
  · rename_i v h
    rw [val_num hw h]; simp [Val.toR, Lia.eval]; grind
  · rename_i ts c h
    rw [val_linear hw h]
    simp only [Val.toR]
    congr 1
    clear h
    induction ts with
    | nil => rfl
    | cons p ts ih =>
      obtain ⟨a, t⟩ := p
      simp only [linSum, List.map_cons, Lia.eval, ih, Lia.rat_intCast, nums, val, get]
  · simp only [Lia.eval, nums, rat_one]; grind

theorem constant_sound {a b : Nat} {v : Int} (h : constant nodes a b = some v) :
    (val I nodes a).toR - (val I nodes b).toR = (v : R) := by
  unfold constant at h
  simp only at h
  split at h
  · rename_i hc
    cases h
    have e := congrArg (Lia.eval (nums I nodes)) hc
    rw [eval_canon, eval_append, Lia.eval_neg] at e
    simp only [Lia.eval] at e
    rw [lin_sound hw a, lin_sound hw b, Ring.intCast_sub]
    grind
  · cases h

end

theorem cast_le_zero_iff {v : Int} : (v : R) ≤ 0 ↔ v ≤ 0 := by
  constructor
  · intro h; apply Classical.byContradiction; intro h'
    have := cast_lt (R := R) (show (0 : Int) < v by omega)
    rw [Ring.intCast_zero] at this; grind
  · intro h; have := cast_le (R := R) h; rwa [Ring.intCast_zero] at this

theorem cast_lt_zero_iff {v : Int} : (v : R) < 0 ↔ v < 0 := by
  constructor
  · intro h; apply Classical.byContradiction; intro h'
    have := cast_le (R := R) (show (0 : Int) ≤ v by omega)
    rw [Ring.intCast_zero] at this; grind
  · intro h; have := cast_lt (R := R) h; rwa [Ring.intCast_zero] at this

section
variable {I : Interp R U} {e : Enc} (hw : wellFormed e.nodes = true) {ρ : Assignment}
  (hmean : ∀ v f, e.meaningOf v = some f → (ρ v = true ↔ holds I e.nodes f))
  (htrue : e.trueLit.holds ρ)
include hw hmean htrue

theorem trueLit_neg : ¬e.trueLit.neg.holds ρ := by
  rw [Lit.holds_neg]; exact fun h => h htrue

theorem holdsLit_sound (b : Bool) : (holdsLit e b).holds ρ ↔ b = true := by
  unfold holdsLit
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, iff_false]; exact trueLit_neg hw hmean htrue
  · simp only [↓reduceIte, iff_true]; exact htrue

/-- A literal that stands for a formula holds when the formula does. -/
theorem denotes_sound : ∀ (fuel : Nat) (l : Lit) (f : Nat), denotes e fuel l f = true →
    (l.holds ρ ↔ holds I e.nodes f)
  | 0, _, _, h => by simp [denotes] at h
  | fuel + 1, l, f, h => by
    have plain : (l.pos && e.meaningOf l.var == some f) = true → (l.holds ρ ↔ holds I e.nodes f) := by
      intro hp
      simp only [Bool.and_eq_true, beq_iff_eq] at hp
      unfold Lit.holds; rw [hp.1]; exact hmean _ _ hp.2
    unfold denotes at h
    simp only at h
    split at h
    · rename_i g hf
      rw [holds_not hw ((Enc.node_eq _ _).symm.trans hf), ← denotes_sound fuel l.neg g h, Lit.holds_neg]
      exact ⟨fun h n => n h, fun h => Classical.byContradiction h⟩
    · rename_i hf
      simp only [beq_iff_eq] at h; subst h
      exact ⟨fun _ => holds_tt hw ((Enc.node_eq _ _).symm.trans hf), fun _ => htrue⟩
    · rename_i hf
      simp only [beq_iff_eq] at h; subst h
      exact ⟨fun h' => absurd h' (trueLit_neg hw hmean htrue), fun h' => absurd h' (not_holds_ff hw ((Enc.node_eq _ _).symm.trans hf))⟩
    · rename_i a b hf
      simp only [Bool.and_eq_true] at h
      obtain ⟨hpos, h⟩ := h
      split at h
      · rename_i m hm
        split at h
        · rename_i n b' hn
          simp only [Bool.and_eq_true, beq_iff_eq] at h
          obtain ⟨rfl, hna⟩ := h
          unfold Lit.holds; rw [hpos, hmean _ _ hm, holds_or hw ((Enc.node_eq _ _).symm.trans hn), holds_implies hw ((Enc.node_eq _ _).symm.trans hf)]
          simp only [List.mem_cons, List.not_mem_nil, or_false,
            exists_eq_or_imp, exists_eq_left]
          rw [holds_not hw (by simpa using hna)]
          constructor
          · rintro (h | h) ha
            · exact absurd ha h
            · exact h
          · intro h; by_cases ha : holds I e.nodes a
            · exact Or.inr (h ha)
            · exact Or.inl ha
        · cases h
      · cases h
    · rename_i a b hf
      split at h
      · rename_i hab
        simp only [beq_iff_eq] at hab h; subst hab h
        rw [holds_eq hw ((Enc.node_eq _ _).symm.trans hf)]; exact ⟨fun _ => rfl, fun _ => htrue⟩
      · rw [Bool.or_eq_true] at h
        rcases h with h | h
        · exact plain h
        · simp only [Bool.and_eq_true] at h
          obtain ⟨hpos, h⟩ := h
          split at h
          · rename_i m hm
            simp only [beq_iff_eq] at h
            unfold Lit.holds
            rw [hpos, hmean _ _ hm, holds_eq hw ((Enc.node_eq _ _).symm.trans h),
              holds_eq hw ((Enc.node_eq _ _).symm.trans hf)]
            exact ⟨Eq.symm, Eq.symm⟩
          · cases h
    · rename_i a b hf
      split at h
      · rename_i v hv
        simp only [beq_iff_eq] at h; subst h
        rw [holdsLit_sound hw hmean htrue, holds_le hw ((Enc.node_eq _ _).symm.trans hf), decide_eq_true_iff]
        have := constant_sound (I := I) hw hv
        rw [← cast_le_zero_iff (R := R), ← this]
        grind
      · exact plain h
    · rename_i a b hf
      split at h
      · rename_i v hv
        simp only [beq_iff_eq] at h; subst h
        rw [holdsLit_sound hw hmean htrue, holds_lt hw ((Enc.node_eq _ _).symm.trans hf), decide_eq_true_iff]
        have := constant_sound (I := I) hw hv
        rw [← cast_lt_zero_iff (R := R), ← this]
        grind
      · exact plain h
    · exact plain h

theorem has_sound {c : Clause} {f : Nat} (h : has e c f = true) (hf : holds I e.nodes f) : c.holds ρ := by
  obtain ⟨l, hl, hd⟩ := List.any_eq_true.mp h
  exact ⟨l, hl, (denotes_sound hw hmean htrue _ _ _ hd).mpr hf⟩

theorem hasNot_sound {c : Clause} {f : Nat} (h : hasNot e c f = true) (hf : ¬holds I e.nodes f) :
    c.holds ρ := by
  obtain ⟨l, hl, hd⟩ := List.any_eq_true.mp h
  refine ⟨l, hl, ?_⟩
  have := denotes_sound hw hmean htrue _ _ _ hd
  rw [Lit.holds_neg] at this
  apply Classical.byContradiction; intro hn
  exact hf (this.mp hn)

theorem not_holds_of_has {c : Clause} {f : Nat} (hc : ¬c.holds ρ) (h : has e c f = true) :
    ¬holds I e.nodes f := fun hf => hc (has_sound hw hmean htrue h hf)

theorem holds_of_hasNot {c : Clause} {f : Nat} (hc : ¬c.holds ρ) (h : hasNot e c f = true) :
    holds I e.nodes f := Classical.byContradiction fun hf => hc (hasNot_sound hw hmean htrue h hf)

theorem positive_sound {l : Lit} {m : Nat} (h : positive e l = some m) : l.holds ρ ↔ holds I e.nodes m := by
  unfold positive at h
  split at h
  · rename_i hp; unfold Lit.holds; rw [hp]; exact hmean _ _ h
  · cases h

theorem sides_sound {m l r : Nat} (h : sides e m = some (l, r)) (hv : val I e.nodes l = val I e.nodes r) :
    holds I e.nodes m := by
  unfold sides at h
  split at h
  · rename_i a b hm
    cases h; exact (holds_eq hw ((Enc.node_eq _ _).symm.trans hm)).mpr hv
  · rename_i x y hm
    split at h
    · rename_i a b b' a' hx hy
      split at h
      · rename_i hc
        cases h
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        rw [holds_and hw ((Enc.node_eq _ _).symm.trans hm)]
        intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl
        · rw [holds_le hw ((Enc.node_eq _ _).symm.trans hx), hv]; exact Std.le_refl _
        · rw [holds_le hw ((Enc.node_eq _ _).symm.trans hy), hv]; exact Std.le_refl _
      · cases h
    · cases h
  · cases h

end

/-- What the checker of input clauses assumes of a model and an assignment:
    the assertions hold, the levels assumed hold, the others are false, and
    the axioms of numbers, datatypes and arrays hold. -/
structure Enc.Sound (e : Enc) (I : Interp R U) (ρ : Assignment) : Prop where
  meaning : ∀ v f, e.meaningOf v = some f → (ρ v = true ↔ holds I e.nodes f)
  trueLit : e.trueLit.holds ρ
  inputs : ∀ f ∈ e.inputs, holds I e.nodes f
  levels : ∀ s fs, e.guarded s = some fs → ρ s = true → ∀ f ∈ fs, holds I e.nodes f
  retired : ∀ s, (e.guarded s).isSome = true → s ∉ e.assumed → ρ s = false
  numeric : ∀ i, e.numeric i = true → ∃ r, val I e.nodes i = .num r
  exhaustive : ∀ t cs, t < e.nodes.length → e.datatypes.lookup (e.sortOf[t]?.getD 0) = some cs →
    ∃ ct ∈ cs, I.app (I.const ct.2.1) [val I e.nodes t] = .bool true
  store : ∀ r s k n a i v j, e.node r = some (.app s [j]) → e.node s = some (.app k [a, i, v]) →
    e.node k = some (.const n) → n ∈ e.stores →
    (val I e.nodes j = val I e.nodes i → val I e.nodes r = val I e.nodes v) ∧
    (val I e.nodes j ≠ val I e.nodes i → val I e.nodes r = I.app (val I e.nodes a) [val I e.nodes j])
  /-- The extensionality instances hold. -/
  ext : ∀ (k eq eqw : Nat) (ws : List Nat), e.exts[k]? = some (eq, eqw, ws) → holds I e.nodes eq ∨ ¬holds I e.nodes eqw
  /-- The witnesses of bit-vector indices are in their range. -/
  range : ∀ n w, e.width n = some w → ∃ k : Int, I.const n = .num (k : R) ∧ 0 ≤ k ∧ k < 2 ^ w
  /-- The nodes of bit-vector sorts are in their range. -/
  sortRange : ∀ t w, t < e.nodes.length → e.bvIndex.lookup (e.sortOf[t]?.getD 0) = some w →
    ∃ k : Int, val I e.nodes t = .num (k : R) ∧ 0 ≤ k ∧ k < 2 ^ w
  /-- Arrays made by stores from the same base that agree at the indices
      written are equal. -/
  sameBase : ∀ q f g fuel fuel' b ws ws', e.node q = some (.eq f g) →
    chain e fuel f = some (b, ws) → chain e fuel' g = some (b, ws') →
    (∀ i ∈ ws ++ ws', I.app (val I e.nodes f) [val I e.nodes i] = I.app (val I e.nodes g) [val I e.nodes i]) →
    val I e.nodes f = val I e.nodes g

theorem num_eq {I : Interp R U} {e : Enc} {ρ : Assignment} (hS : e.Sound I ρ) {a b : Nat}
    (ha : e.numeric a = true) (hb : e.numeric b = true)
    (h : (val I e.nodes a).toR = (val I e.nodes b).toR) : val I e.nodes a = val I e.nodes b := by
  obtain ⟨x, hx⟩ := hS.numeric a ha
  obtain ⟨y, hy⟩ := hS.numeric b hb
  rw [hx, hy] at h ⊢
  simp only [Val.toR] at h
  rw [h]

theorem testsOk_sound {I : Interp R U} {e : Enc} (hw : wellFormed e.nodes = true) {t : Nat} :
    ∀ {ps : List Nat} {cs : List (Nat × Nat × List Nat)}, testsOk e t ps cs = true →
      ∀ ct ∈ cs, I.app (I.const ct.2.1) [val I e.nodes t] = .bool true → ∃ p ∈ ps, holds I e.nodes p
  | [], [], _, _, m, _ => by simp at m
  | p :: ps, (c, tester, ss) :: cs, h, ct, m, hct => by
    simp only [testsOk, Bool.and_eq_true] at h
    obtain ⟨hp, h⟩ := h
    rcases List.mem_cons.mp m with rfl | m
    · refine ⟨p, by simp, ?_⟩
      split at hp
      · rename_i q hq
        split at hp
        · rename_i k t' hk
          simp only [Bool.and_eq_true, beq_iff_eq] at hp
          obtain ⟨rfl, hk'⟩ := hp
          rw [holds_pred hw ((Enc.node_eq _ _).symm.trans hq), val_app hw ((Enc.node_eq _ _).symm.trans hk), List.map_cons, List.map_nil, val_const hw ((Enc.node_eq _ _).symm.trans hk')]
          exact hct
        · cases hp
      · cases hp
    · obtain ⟨p', hp', hh⟩ := testsOk_sound hw h ct m hct
      exact ⟨p', by simp [hp'], hh⟩
  | [], _ :: _, h, _, _, _ | _ :: _, [], h, _, _, _ => by simp [testsOk] at h

theorem witnessLe_sound {I : Interp R U} {e : Enc} {ρ : Assignment} (hw : wellFormed e.nodes = true)
    (hS : e.Sound I ρ) {f : Nat} (h : witnessLe e f = true) : holds I e.nodes f := by
  unfold witnessLe at h
  split at h
  · rename_i a b hle
    rw [holds_le hw ((Enc.node_eq _ _).symm.trans hle)]
    split at h
    · rename_i z n ha hb
      simp only [Bool.and_eq_true, beq_iff_eq, Option.isSome_iff_exists] at h
      obtain ⟨rfl, w, hw'⟩ := h
      obtain ⟨k, hk, h0, _⟩ := hS.range n w hw'
      rw [val_num hw ((Enc.node_eq _ _).symm.trans ha), val_const hw ((Enc.node_eq _ _).symm.trans hb), hk]
      simp only [Val.toR]
      have := cast_le (R := R) h0
      rw [Ring.intCast_zero] at this
      simpa [Ring.intCast_zero] using this
    · rename_i n v ha hb
      split at h
      · rename_i w hw'
        simp only [beq_iff_eq] at h
        subst h
        obtain ⟨k, hk, _, h1⟩ := hS.range n w hw'
        rw [val_num hw ((Enc.node_eq _ _).symm.trans hb), val_const hw ((Enc.node_eq _ _).symm.trans ha), hk]
        simp only [Val.toR]
        exact cast_le (R := R) (by omega)
      · cases h
    · cases h
  · cases h

theorem rangeLe_sound {I : Interp R U} {e : Enc} {ρ : Assignment} (hw : wellFormed e.nodes = true)
    (hS : e.Sound I ρ) {f : Nat} (h : rangeLe e f = true) : holds I e.nodes f := by
  unfold rangeLe at h
  split at h
  · rename_i a b hle
    rw [holds_le hw ((Enc.node_eq _ _).symm.trans hle)]
    split at h
    · rename_i z _ ha
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Option.isSome_iff_exists, Tab.at_eq] at h
      obtain ⟨⟨rfl, hb⟩, w, hw'⟩ := h
      obtain ⟨k, hk, h0, _⟩ := hS.sortRange b w hb hw'
      rw [val_num hw ((Enc.node_eq _ _).symm.trans ha), hk]
      simp only [Val.toR]
      have := cast_le (R := R) h0
      rw [Ring.intCast_zero] at this
      simpa [Ring.intCast_zero] using this
    · rename_i _ v hb _
      simp only [Bool.and_eq_true, decide_eq_true_eq, Tab.at_eq] at h
      obtain ⟨ha, h⟩ := h
      split at h
      · rename_i w hw'
        simp only [beq_iff_eq] at h
        subst h
        obtain ⟨k, hk, _, h1⟩ := hS.sortRange a w ha hw'
        rw [val_num hw ((Enc.node_eq _ _).symm.trans hb), hk]
        simp only [Val.toR]
        exact cast_le (R := R) (by omega)
      · cases h
    · cases h
  · cases h

theorem rangeOf_sound {I : Interp R U} {e : Enc} (hw : wellFormed e.nodes = true) {p : Nat → Bool}
    (hp : ∀ g, p g = true → holds I e.nodes g) {f : Nat} (h : rangeOf e p f = true) : holds I e.nodes f := by
  unfold rangeOf at h
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · exact hp f h
  · split at h
    · rename_i x y hxy
      simp only [Bool.and_eq_true] at h
      rw [holds_and hw ((Enc.node_eq _ _).symm.trans hxy)]
      intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      · exact hp _ h.1
      · exact hp _ h.2
    · cases h

/-- A read over a write `r` is the value `w` that `storeOk` says it is, in a
    model where the clause is false. -/
theorem storeOk_sound {I : Interp R U} {e : Enc} {ρ : Assignment} (hw : wellFormed e.nodes = true)
    (hS : e.Sound I ρ) {c : Clause} {r w : Nat} (hc : ¬c.holds ρ) (h : storeOk e c r w = true) :
    val I e.nodes r = val I e.nodes w := by
  have hmean := hS.meaning
  have htrue := hS.trueLit
  have lfalse : ∀ l ∈ c, ¬l.holds ρ := fun l m hl => hc ⟨l, m, hl⟩
  unfold storeOk at h
  split at h
  · rename_i s j hr
    split at h
    · rename_i k a i v hs'
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
      obtain ⟨hk, h⟩ := h
      split at hk
      · rename_i n hk'
        have law := hS.store r s k n a i v j hr hs' hk' (List.contains_iff_mem.mp hk)
        rcases h with ⟨rfl, rfl⟩ | ⟨hw', h⟩
        · exact law.1 rfl
        · obtain ⟨l', hl', h⟩ := List.any_eq_true.mp h
          split at h
          · rename_i m' hm'
            simp only [Bool.or_eq_true, beq_iff_eq] at h
            have hij : val I e.nodes j ≠ val I e.nodes i := by
              intro hji
              apply lfalse l' hl'
              apply (positive_sound hw hmean htrue hm').mpr
              rcases h with h | h
              · exact sides_sound hw hmean htrue h hji.symm
              · exact sides_sound hw hmean htrue h hji
            rw [law.2 hij, val_app hw ((Enc.node_eq _ _).symm.trans hw')]; rfl
          · cases h
      · cases hk
    · cases h
  · cases h

/-- An input clause the checker accepts holds. -/
theorem inputOk_sound {I : Interp R U} {e : Enc} {ρ : Assignment} (hw : wellFormed e.nodes = true)
    (hS : e.Sound I ρ) {c : Clause} {o : Origin} (h : inputOk e c o = true) : c.holds ρ := by
  have hmean := hS.meaning
  have htrue := hS.trueLit
  apply Classical.byContradiction
  intro hc
  have lfalse : ∀ l ∈ c, ¬l.holds ρ := fun l m hl => hc ⟨l, m, hl⟩
  have nh := fun {f} => not_holds_of_has hw hmean htrue (f := f) hc
  have hn := fun {f} => holds_of_hasNot hw hmean htrue (f := f) hc
  cases o with
  | definition =>
    obtain ⟨d, hd, h⟩ := List.any_eq_true.mp h
    have hdf := lfalse d hd
    split at h
    · rename_i m hm
      have dm : (d.pos = true → ¬holds I e.nodes m) ∧ (d.pos = false → holds I e.nodes m) := by
        unfold Lit.holds at hdf
        constructor
        · intro hp hm'; exact hdf (by rw [hp]; exact (hmean _ _ hm).mpr hm')
        · intro hp; have : ρ d.var = true := by cases e' : ρ d.var <;> simp_all
          exact (hmean _ _ hm).mp this
      split at h
      · rename_i hn'
        simp only [beq_iff_eq] at h; subst h; exact hdf htrue
      · rename_i as hm'
        split at h
        · rename_i hp
          exact dm.1 hp ((holds_and hw ((Enc.node_eq _ _).symm.trans hm')).mpr fun a ma => hn (List.all_eq_true.mp h a ma))
        · rename_i hp
          obtain ⟨a, ma, ha⟩ := List.any_eq_true.mp h
          exact nh ha ((holds_and hw ((Enc.node_eq _ _).symm.trans hm')).mp (dm.2 (by simpa using hp)) a ma)
      · rename_i as hm'
        split at h
        · rename_i hp
          obtain ⟨a, ma, ha⟩ := List.any_eq_true.mp h
          exact dm.1 hp ((holds_or hw ((Enc.node_eq _ _).symm.trans hm')).mpr ⟨a, ma, hn ha⟩)
        · rename_i hp
          obtain ⟨a, ma, ha⟩ := (holds_or hw ((Enc.node_eq _ _).symm.trans hm')).mp (dm.2 (by simpa using hp))
          exact nh (List.all_eq_true.mp h a ma) ha
      · rename_i x y hm'
        rw [holds_iff hw ((Enc.node_eq _ _).symm.trans hm')] at dm
        split at h
        · rename_i hp
          simp only [Bool.or_eq_true, Bool.and_eq_true] at h
          have := dm.1 hp
          rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact this ⟨fun hx => absurd hx (nh h1), fun hy => absurd hy (nh h2)⟩
          · exact this ⟨fun _ => hn h2, fun _ => hn h1⟩
        · rename_i hp
          simp only [Bool.or_eq_true, Bool.and_eq_true] at h
          have := dm.2 (by simpa using hp)
          rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact nh h2 (this.mp (hn h1))
          · exact nh h1 (this.mpr (hn h2))
      · rename_i x t f hm'
        rw [holds_ite hw ((Enc.node_eq _ _).symm.trans hm')] at dm
        split at h
        · rename_i hp
          simp only [Bool.or_eq_true, Bool.and_eq_true] at h
          have := dm.1 hp
          rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact this (by rw [if_pos (hn h1)]; exact hn h2)
          · exact this (by rw [if_neg (nh h1)]; exact hn h2)
        · rename_i hp
          simp only [Bool.or_eq_true, Bool.and_eq_true] at h
          have := dm.2 (by simpa using hp)
          by_cases hx : holds I e.nodes x
          · rw [if_pos hx] at this
            rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact nh h2 this
            · exact nh h1 hx
          · rw [if_neg hx] at this
            rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact absurd (hn h1) hx
            · exact nh h2 this
      · rename_i t hm'
        rw [holds_pred hw ((Enc.node_eq _ _).symm.trans hm')] at dm
        split at h
        · rename_i inner ht
          rw [val_bterm hw ((Enc.node_eq _ _).symm.trans ht)] at dm
          simp only [Val.bool.injEq, decide_eq_true_iff] at dm
          split at h
          · rename_i hp; exact dm.1 hp (hn h)
          · rename_i hp; exact nh h (dm.2 (by simpa using hp))
        · cases h
      · cases h
    · cases h
  | assertion f =>
    simp only [inputOk, Bool.and_eq_true, Bool.or_eq_true, List.contains_iff_mem] at h
    obtain ⟨hf, h⟩ := h
    rcases h with h | h
    · exact nh hf (hS.inputs f h)
    · obtain ⟨l, hl, h⟩ := List.any_eq_true.mp h
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
      obtain ⟨hp, h⟩ := h
      split at h
      · rename_i fs hg
        have hlf := lfalse l hl
        unfold Lit.holds at hlf
        rw [hp] at hlf
        have : ρ l.var = true := by cases e' : ρ l.var <;> simp_all
        exact nh hf (hS.levels _ _ hg this f (List.contains_iff_mem.mp h))
      · cases h
  | retired =>
    obtain ⟨l, hl, h⟩ := List.any_eq_true.mp h
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨hp, hg⟩, ha⟩ := h
    apply lfalse l hl
    unfold Lit.holds; rw [hp]
    exact hS.retired _ hg (by simpa using ha)
  | exhaustive t o =>
    simp only [inputOk, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨ht, ho⟩, h⟩ := h
    rw [Tab.at_eq] at h
    split at h
    · rename_i cs ps hcs hno
      obtain ⟨ct, hct, happ⟩ := hS.exhaustive t cs ht hcs
      obtain ⟨p, hp, hh⟩ := testsOk_sound hw h ct hct happ
      exact nh ho ((holds_or hw ((Enc.node_eq _ _).symm.trans hno)).mpr ⟨p, hp, hh⟩)
    · cases h
  | sharedSplit lt le =>
    obtain ⟨l, hl, h⟩ := List.any_eq_true.mp h
    split at h
    · rename_i m hm
      have hlm := positive_sound hw hmean htrue hm
      have nm : ¬holds I e.nodes m := fun h' => lfalse l hl (hlm.mpr h')
      split at h
      · rename_i a b hab
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨⟨⟨⟨na, nb⟩, hor⟩, h1⟩, h2⟩ := h
        rw [holds_eq hw ((Enc.node_eq _ _).symm.trans hab)] at nm
        apply nm
        apply num_eq hS na nb
        rcases hor with ⟨hlt, hle⟩ | ⟨hlt, hle⟩
        · have := nh h1; rw [holds_lt hw ((Enc.node_eq _ _).symm.trans hlt)] at this
          have := hn h2; rw [holds_le hw ((Enc.node_eq _ _).symm.trans hle)] at this
          apply Std.le_antisymm <;> grind
        · have := nh h1; rw [holds_lt hw ((Enc.node_eq _ _).symm.trans hlt)] at this
          have := hn h2; rw [holds_le hw ((Enc.node_eq _ _).symm.trans hle)] at this
          apply Std.le_antisymm <;> grind
      · rename_i a b hab
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨hlt, h1⟩ := h
        rw [holds_le hw ((Enc.node_eq _ _).symm.trans hab)] at nm
        have := hn h1; rw [holds_lt hw ((Enc.node_eq _ _).symm.trans hlt)] at this
        exact nm (Std.le_of_lt this)
      · cases h
    · cases h
  | numerals =>
    obtain ⟨l, hl, h⟩ := List.any_eq_true.mp h
    split at h
    · rename_i m hm
      split at h
      · rename_i a b hab
        split at h
        · rename_i v hv
          have hd := constant_sound (I := I) hw hv
          simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
          obtain ⟨hpos, hnum⟩ := h
          have hlf := lfalse l hl
          unfold Lit.holds at hlf
          by_cases v0 : v = 0
          · subst v0
            have hp : l.pos = true := by simpa using hpos.symm
            rcases hnum with hnum | ⟨na, nb⟩
            · exact hnum rfl
            · apply hlf; rw [hp, hmean _ _ hm, holds_eq hw ((Enc.node_eq _ _).symm.trans hab)]
              apply num_eq hS na nb
              rw [Ring.intCast_zero] at hd; grind
          · have hp : l.pos = false := by
              cases hl' : l.pos
              · rfl
              · rw [hl'] at hpos; simp at hpos; exact absurd hpos v0
            have : ρ l.var = true := by cases e' : ρ l.var <;> simp_all
            rw [hmean _ _ hm, holds_eq hw ((Enc.node_eq _ _).symm.trans hab)] at this
            rw [this] at hd
            have := cast_inj (R := R) (a := v) (b := 0) (by rw [Ring.intCast_zero]; grind)
            exact v0 this
        · cases h
      · cases h
    · cases h
  | congruence eqfg =>
    obtain ⟨l, hl, h⟩ := List.any_eq_true.mp h
    split at h
    · rename_i m hm
      have hlm := positive_sound hw hmean htrue hm
      split at h
      · rename_i p q hpq
        split at h
        · rename_i f xs g ys hp hq
          simp only [Bool.and_eq_true, beq_iff_eq] at h
          obtain ⟨⟨rfl, he⟩, h1⟩ := h
          have hfg := hn h1
          rw [holds_eq hw ((Enc.node_eq _ _).symm.trans he)] at hfg
          apply lfalse l hl
          rw [hlm, holds_eq hw ((Enc.node_eq _ _).symm.trans hpq), val_app hw ((Enc.node_eq _ _).symm.trans hp), val_app hw ((Enc.node_eq _ _).symm.trans hq), hfg]
        · cases h
      · cases h
    · cases h
  | readOverWrite =>
    obtain ⟨l, hl, h⟩ := List.any_eq_true.mp h
    split at h
    · rename_i m hm
      have hlm := positive_sound hw hmean htrue hm
      split at h
      · rename_i r w hs
        apply lfalse l hl
        rw [hlm]
        apply sides_sound hw hmean htrue hs
        rw [Bool.or_eq_true] at h
        rcases h with h | h
        · exact storeOk_sound hw hS hc h
        · exact (storeOk_sound hw hS hc h).symm
      · cases h
    · cases h
  | extensionality k =>
    simp only [inputOk] at h
    split at h
    · rename_i eq eqw ws hk
      simp only [Bool.and_eq_true] at h
      rcases hS.ext k eq eqw ws hk with h1 | h1
      · exact nh h.1 h1
      · exact h1 (hn h.2)
    · cases h
  | witnessRange f =>
    simp only [inputOk, Bool.and_eq_true] at h
    exact nh h.1 (rangeOf_sound hw (fun g hg => witnessLe_sound hw hS hg) h.2)
  | sortRange f =>
    simp only [inputOk, Bool.and_eq_true] at h
    exact nh h.1 (rangeOf_sound hw (fun g hg => rangeLe_sound hw hS hg) h.2)
  | sameBase q ds =>
    simp only [inputOk, Bool.and_eq_true] at h
    obtain ⟨hq, h⟩ := h
    split at h
    · rename_i f g hfg
      split at h
      · rename_i b ws b' ws' hf hg
        simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
        obtain ⟨rfl, hall⟩ := h
        apply nh hq
        rw [holds_eq hw ((Enc.node_eq _ _).symm.trans hfg)]
        apply hS.sameBase q f g _ _ b ws ws' hfg hf hg
        intro i hi
        obtain ⟨d, -, hd⟩ := List.any_eq_true.mp (hall i hi)
        simp only [Bool.and_eq_true] at hd
        obtain ⟨hnd, hd⟩ := hd
        have hdh := hn hnd
        split at hd
        · rename_i p r hpr
          simp only [Bool.and_eq_true, beq_iff_eq] at hd
          rw [holds_eq hw ((Enc.node_eq _ _).symm.trans hpr), val_app hw ((Enc.node_eq _ _).symm.trans hd.1),
            val_app hw ((Enc.node_eq _ _).symm.trans hd.2)] at hdh
          simpa using hdh
        · cases hd
      · cases h
    · cases h

end Vik.Low
