import Vik.Cert.Inputs
import Vik.Cert.Uf
import Vik.Cert.Witnesses

/-!
# Proofs of unsatisfiability

The checker of a whole proof, and its soundness: when it accepts the answer to
a problem, the lowered assertions have no model in which the assumed levels
hold.

A problem is the table of lowered terms and formulas, with their sorts, the
assertions, the datatypes and the array stores. An answer is a clausal proof
whose steps come with their justifications: an input clause with its origin, a
lemma with its certificate (equality proof or cutting planes), or a derived
clause; with what its variables and theory atoms stand for.
-/

set_option linter.unusedSectionVars false

namespace Vik.Low

open Lean.Grind Vik.Real Vik.Clausal

structure Problem where
  sig : Sig
  nodes : List Node
  sortOf : List Nat
  inputs : List Nat
  /-- For each datatype sort, its constructors, with tester and selectors. -/
  datatypes : List (Nat × List (Nat × Nat × List Nat))
  stores : List Nat
  /-- The sorts of bit-vectors, integers to the lowering, with their widths. -/
  bvIndex : List (Nat × Nat)

/-- A bound `x ≤ c` (`x < c` if strict) on an LIA variable, or `x = c`. -/
inductive LiaAtom where
  | bound (x : Nat) (c : Int) (strict : Bool)
  | equal (x : Nat) (c : Int)
  deriving DecidableEq, Repr

inductive Just where
  | input (o : Origin)
  | uf (proof : List Uf.Step) (cert : Uf.Cert)
  | lia (nodes : List Lia.Node)
  | derived

structure Answer where
  /-- The formula each variable stands for. -/
  meaning : List (Option Nat)
  trueLit : Lit
  /-- The literals of levels and named assertions, with the formulas each
      guards. -/
  levels : List (Nat × List Nat)
  /-- The levels the last check assumed. -/
  assumed : List Nat
  /-- The equality of classes each variable stands for, in the UF theory. -/
  ufAtoms : List (Option (Nat × Nat))
  trueClass : Nat
  falseClass : Nat
  /-- The constructor classes with their selectors' classes, and the tester
      classes with their constructors'. -/
  ufCtors : List (Nat × List Nat)
  ufTesters : List (Nat × Nat)
  /-- The bound each variable stands for, in the LIA theory, and the
      expression of each LIA variable over the nodes. -/
  liaAtoms : List (Option LiaAtom)
  liaForms : List Lia.Form
  steps : List Step
  justs : List Just
  conclusion : Nat
  /-- The extensionality instances, in the order their witnesses take values:
      the equality `f = g`, the equality of `f` and `g` applied to the
      witnesses, and the witnesses. -/
  exts : List (Nat × Nat × List Nat)
  /-- The witnesses: those of the instances, and those of a range alone. -/
  witnesses : List Nat

section Checker
variable (P : Problem) (A : Answer)

def Answer.ufAtom (v : Nat) : Option (Nat × Nat) := (Tab.at A.ufAtoms v).getD none
def Answer.liaAtom (v : Nat) : Option LiaAtom := (Tab.at A.liaAtoms v).getD none
def Answer.liaForm (x : Nat) : Lia.Form := (Tab.at A.liaForms x).getD []
def Answer.meaningOf (v : Nat) : Option Nat := (Tab.at A.meaning v).getD none

def Problem.node (i : Nat) : Option Node := Tab.at P.nodes i
def Problem.sort (i : Nat) : Nat := P.sortOf[i]?.getD 0

theorem Answer.ufAtom_eq (v : Nat) : A.ufAtom v = (A.ufAtoms[v]?).getD none := by simp [Answer.ufAtom]
theorem Answer.liaAtom_eq (v : Nat) : A.liaAtom v = (A.liaAtoms[v]?).getD none := by simp [Answer.liaAtom]
theorem Answer.liaForm_eq (x : Nat) : A.liaForm x = (A.liaForms[x]?).getD [] := by simp [Answer.liaForm]
theorem Answer.meaningOf_eq (v : Nat) : A.meaningOf v = (A.meaning[v]?).getD none := by simp [Answer.meaningOf]
theorem Problem.node_eq (i : Nat) : P.node i = P.nodes[i]? := by simp [Problem.node]
theorem Problem.sort_eq (i : Nat) : P.sort i = P.sortOf[i]?.getD 0 := rfl
theorem Problem.node_some {P : Problem} {i : Nat} {n : Node} (h : P.node i = some n) : P.nodes[i]? = some n := by
  rw [← Problem.node_eq]; exact h
def Problem.symOf (i : Nat) : Option Nat :=
  match P.node i with
  | some (.const n) => some n
  | _ => none

/-- The datatype of constructor `C`, with its tester and selectors. -/
def Problem.ctorEntry (C : Nat) : Option (Nat × Nat × List Nat) :=
  P.datatypes.findSome? fun (d, cs) =>
    (cs.find? (·.1 == C)).map fun (_, T, Ss) => (d, T, Ss)

def Problem.isInt (u : Nat) : Bool := u < P.nodes.length && P.sig.is ((Tab.at P.sortOf u).getD 0) .int

def Problem.enc : Enc where
  nodes := P.nodes
  sortOf := P.sortOf
  sig := P.sig
  meaning := A.meaning
  trueLit := A.trueLit
  inputs := P.inputs
  levels := A.levels
  assumed := A.assumed
  datatypes := P.datatypes
  stores := P.stores
  exts := A.exts
  witnesses := A.witnesses
  bvIndex := P.bvIndex

def Problem.ufEnv : Uf.Env where
  atom := A.ufAtom
  node x :=
    match P.node x with
    | some (.app f args) => some (f, args)
    | _ => none
  trueClass := A.trueClass
  falseClass := A.falseClass
  trueLit := A.trueLit
  ctors c := A.ufCtors.lookup c
  tester t := A.ufTesters.lookup t
  sameType c d :=
    match P.symOf c, P.symOf d with
    | some C, some D =>
      C != D &&
        match P.ctorEntry C, P.ctorEntry D with
        | some (s, _), some (s', _) => s == s'
        | _, _ => false
    | _, _ => false

/-- The literal of reason `r`, as `cdclt` numbers literals. -/
def litOf (r : Int) : Lit := ⟨r.toNat / 2, r.toNat % 2 == 0⟩

/-- Whether a hypothesis of a cutting-planes certificate is the bound of a
    hypothesis of the lemma `c`: the negation of one of its literals. -/
def hypOk (c : Clause) (h : Lia.Hyp) : Bool :=
  let l := litOf h.reason
  (c.map Lit.neg).contains l &&
    match A.liaAtom l.var with
    | some (.bound x k strict) =>
      h.x == x && h.c == k && h.strict == (if l.pos then strict else !strict) && h.upper == l.pos
    | some (.equal x k) => l.pos && h.x == x && h.c == k && !h.strict
    | none => false

def Problem.liaEnv (c : Clause) : Lia.Env where
  form := A.liaForm
  isInt := P.isInt
  hypOk := hypOk A c
  distinct _ _ _ := false

/-- Whether `l - r ≤ c` is the bound `x ≤ c`: `x` stands for `l - r` up to a
    constant. -/
def Problem.on (l r x : Nat) (c : Int) : Bool :=
  let (fl, cl) := lin P.nodes l
  let (fr, cr) := lin P.nodes r
  canon (fl ++ Lia.neg fr) == canon (A.liaForm x) && c == cr - cl

/-- Whether the theory atoms of a variable are those of its formula. -/
def Problem.atomOk (v : Nat) : Bool :=
  let uf := match A.ufAtom v with
    | none => true
    | some (a, b) =>
      (b != A.trueClass || (a < P.nodes.length && P.sig.is ((Tab.at P.sortOf a).getD 0) .bool)) &&
        match A.meaningOf v with
        | none => (A.liaAtom v).isNone
        | some m =>
          match P.node m with
          | some (.eq l r) => l == a && r == b
          | some (.pred t) => t == a && b == A.trueClass
          | _ => false
  let lia := match A.liaAtom v with
    | none => true
    | some atom =>
      match A.meaningOf v with
      | none => true
      | some m =>
        match atom, P.node m with
        | .bound x c strict, some (.le l r) => !strict && P.on A l r x c
        | .bound x c strict, some (.lt l r) =>
          if strict then P.on A l r x c
          else Lia.integral P.isInt (A.liaForm x) && P.on A l r x (c + 1)
        | .equal x c, some (.eq l r) =>
          P.on A l r x c && (P.enc A).numeric l && (P.enc A).numeric r
        | _, _ => false
  uf && lia

def nodupB : List Nat → Bool
  | [] => true
  | x :: xs => !xs.contains x && nodupB xs

/-- Whether the stores are declared as such: `store(a, i, v)` of an array sort
    `a` from the index sort of `i` to the element sort of `v`. -/
def Problem.storesOk : Bool :=
  P.stores.all fun n =>
    match P.sig.decls[n]? with
    | some s =>
      match P.sig.sorts[s]? with
      | some (.fn [arr, idx, el] arr') =>
        arr' == arr && P.sig.sorts[arr]? == some (.fn [idx] el)
      | _ => false
    | none => false

/-- Whether the datatypes are declared as such: a constructor of the sort, its
    tester a predicate of the sort, its selectors functions of the sort. -/
def Problem.dtOk : Bool :=
  nodupB (P.datatypes.map (·.1)) && P.datatypes.all fun (d, cs) =>
    P.sig.is d .user && cs.all fun (C, T, Ss) =>
      (match P.sig.decls[C]? with
        | some s =>
          if Ss.isEmpty then s == d
          else match P.sig.sorts[s]? with
            | some (.fn as r) => r == d && as.length == Ss.length
            | _ => false
        | none => false) &&
      (match P.sig.decls[T]? with
        | some s =>
          match P.sig.sorts[s]? with
          | some (.fn [d'] b) => d' == d && P.sig.is b .bool
          | _ => false
        | none => false) &&
      Ss.all fun S =>
        match P.sig.decls[S]? with
        | some s =>
          match P.sig.sorts[s]? with
          | some (.fn [d'] _) => d' == d
          | _ => false
        | none => false

/-- Whether the classes of constructors and testers are those of their symbols. -/
def Problem.classesOk : Bool :=
  A.ufCtors.all (fun (c, ss) =>
    match P.symOf c with
    | some C =>
      match P.ctorEntry C with
      | some (_, _, Ss) => ss.map P.symOf == Ss.map some
      | none => false
    | none => false) &&
  A.ufTesters.all fun (t, c) =>
    match P.symOf t, P.symOf c with
    | some T, some C =>
      (A.ufCtors.lookup c).isSome &&
        match P.ctorEntry C with
        | some (_, T', _) => T' == T
        | none => false
    | _, _ => false

/-- The symbols of the datatypes: constructors, testers and selectors. -/
def Problem.dtSyms : List Nat := P.datatypes.flatMap fun (_, cs) => cs.flatMap fun (C, T, Ss) => C :: T :: Ss

/-- The rank of each symbol (see `rankOf`). -/
def Answer.rank (n : Nat) : Nat := rankOf A.exts A.witnesses n

/-- Whether the witnesses are fresh, in the order of the instances: the
    symbols of datatypes and stores, the inputs and the levels depend on no
    witness; the functions of an instance only on the witnesses of earlier
    instances, or of ranges alone; and each instance is its two functions
    applied to its witnesses. A node of a bit-vector index that depends on a
    witness is a witness or an application. -/
def Problem.witnessesOk : Bool :=
  let ds := depths A.rank P.nodes
  P.bvIndex.all (fun p => P.sig.is p.1 .int) &&
  P.stores.all (fun n => A.rank n == 0) && P.dtSyms.all (fun n => A.rank n == 0) &&
  P.inputs.all (fun f => depthOf ds f == 0) &&
  A.levels.all (fun l => l.2.all fun f => depthOf ds f == 0) &&
  (List.range P.nodes.length).all (fun i =>
    depthOf ds i == 0 || (P.bvIndex.lookup ((Tab.at P.sortOf i).getD 0)).isNone ||
      match P.node i with
      | some (.const n) => A.witnesses.contains n
      | some (.app _ _) => true
      | _ => false) &&
  (List.range A.exts.length).all fun k =>
    match A.exts[k]? with
    | some (eq, eqw, ws) =>
      nodupB ws && ws.all (fun n => A.rank n == k + 2) &&
        match P.node eq, P.node eqw with
        | some (.eq f g), some (.eq F G) =>
          depthOf ds f < k + 2 && depthOf ds g < k + 2 &&
            chainRev P.nodes f F ws.reverse && chainRev P.nodes g G ws.reverse &&
            chainExact P.sig P.nodes P.sortOf F ws.reverse
        | _, _ => false
    | none => false

theorem all_fun_true {α : Type} (l : List α) : (l.all fun _ => true) = true := by
  induction l <;> simp_all

theorem foldl_max_zero : ∀ (l : List Nat) (acc : Nat), (∀ x ∈ l, x = 0) → l.foldl max acc = acc
  | [], _, _ => rfl
  | x :: l, acc, h => by
    simp only [List.foldl_cons, h x List.mem_cons_self, Nat.max_zero]
    exact foldl_max_zero l acc (fun y m => h y (List.mem_cons_of_mem x m))

theorem foldl_scan_zero (F : List Nat → Node → Nat) (hF : ∀ ds n, (∀ x ∈ ds, x = 0) → F ds n = 0) :
    ∀ (nodes : List Node) (acc : List Nat), (∀ x ∈ acc, x = 0) →
      ∀ x ∈ nodes.foldl (fun ds n => ds ++ [F ds n]) acc, x = 0
  | [], _, h => h
  | n :: nodes, acc, h => by
    simp only [List.foldl_cons]
    refine foldl_scan_zero F hF nodes _ (fun x m => ?_)
    rcases List.mem_append.mp m with m | m
    · exact h x m
    · simp only [List.mem_singleton] at m; subst m; exact hF acc n h

/-- With no witnesses, every node has depth 0. -/
theorem depthOf_zero {rank : Nat → Nat} (hr : ∀ n, rank n = 0) (nodes : List Node) (i : Nat) :
    depthOf (depths rank nodes) i = 0 := by
  have hz : ∀ x ∈ depths rank nodes, x = 0 := by
    rw [depths_eq_scan]
    refine foldl_scan_zero _ (fun ds n h => ?_) nodes [] (by simp)
    unfold depthNode maxOf
    have ho : n.own rank = 0 := by cases n <;> simp [Node.own, hr]
    rw [ho, foldl_max_zero]
    · rfl
    · intro x m
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp m
      cases hj : ds[j]? with
      | none => rfl
      | some y => exact h y (List.mem_of_getElem? hj)
  rw [depthOf_eq]
  cases hi : (depths rank nodes)[i]? with
  | none => rfl
  | some y => exact hz y (List.mem_of_getElem? hi)

/-- `witnessesOk`, short when the answer has no witnesses. -/
def Problem.witnessesOkF : Bool :=
  if A.exts.isEmpty && A.witnesses.isEmpty then P.bvIndex.all (fun p => P.sig.is p.1 .int)
  else P.witnessesOk A

theorem Problem.witnessesOkF_eq : P.witnessesOkF A = P.witnessesOk A := by
  unfold Problem.witnessesOkF
  split
  · rename_i h
    simp only [Bool.and_eq_true, List.isEmpty_iff] at h
    obtain ⟨he, hw⟩ := h
    have hr : ∀ n, A.rank n = 0 := by
      intro n
      simp [Answer.rank, rankOf, extIndex, he, hw]
    unfold Problem.witnessesOk
    simp [hr, depthOf_zero hr, he, all_fun_true]
  · rfl

def Problem.justOk (s : Step) (j : Just) : Bool :=
  match s, j with
  | .input c, .input o => inputOk (P.enc A) c o
  | .lemma c, .uf proof cert => Uf.accepts (P.ufEnv A) c proof cert
  | .lemma c, .lia nodes => Lia.accepts (P.liaEnv A c) nodes
  | .derived _ _, .derived => true
  | _, _ => false

def Problem.accepts : Bool :=
  P.witnessesOkF A && wellFormed P.nodes && typed P.sig P.nodes P.sortOf && P.dtOk && P.storesOk && P.classesOk A &&
    -- `true`, its literal and classes
    (match A.meaningOf A.trueLit.var with
      | some t => A.trueLit.pos && P.node t == some .tt
      | none => false) &&
    (match P.node A.trueClass, P.node A.falseClass with
      | some (.bterm t), some (.bterm f) => P.node t == some .tt && P.node f == some .ff
      | _, _ => false) &&
    -- levels stand for no formula and no atom
    A.levels.all (fun (s, _) =>
      (A.meaningOf s).isNone && (A.ufAtom s).isNone && (A.liaAtom s).isNone) &&
    (List.range (max A.ufAtoms.length A.liaAtoms.length)).all (P.atomOk A) &&
    A.steps.length == A.justs.length &&
    (A.steps.zip A.justs).all (fun (s, j) => P.justOk A s j) &&
    (Clausal.checkT (A.steps.map Clausal.Step.clause) 0 A.steps &&
      match Tab.at (A.steps.map Clausal.Step.clause) A.conclusion with
      | some goal => goal.all fun l => !l.pos && A.assumed.contains l.var && (A.levels.lookup l.var).isSome
      | none => false)

/-! ### The checker in slices

The kernel checks a large answer faster, and on a smaller stack, in slices
that Lean checks in parallel: the justifications and the derived steps from
`a` to `a + n`, and the rest of `accepts` once. -/

/-- `accepts` but the justifications and the derived steps. -/
def Problem.acceptsBase : Bool :=
  P.witnessesOkF A && wellFormed P.nodes && typed P.sig P.nodes P.sortOf && P.dtOk && P.storesOk && P.classesOk A &&
    (match A.meaningOf A.trueLit.var with
      | some t => A.trueLit.pos && P.node t == some .tt
      | none => false) &&
    (match P.node A.trueClass, P.node A.falseClass with
      | some (.bterm t), some (.bterm f) => P.node t == some .tt && P.node f == some .ff
      | _, _ => false) &&
    A.levels.all (fun (s, _) =>
      (A.meaningOf s).isNone && (A.ufAtom s).isNone && (A.liaAtom s).isNone) &&
    (List.range (max A.ufAtoms.length A.liaAtoms.length)).all (P.atomOk A) &&
    A.steps.length == A.justs.length &&
    match Tab.at (A.steps.map Clausal.Step.clause) A.conclusion with
    | some goal => goal.all fun l => !l.pos && A.assumed.contains l.var && (A.levels.lookup l.var).isSome
    | none => false

/-- The justifications from the `a`-th on. -/
def Problem.justsFrom (a : Nat) : Bool :=
  ((A.steps.zip A.justs).drop a).all (fun (s, j) => P.justOk A s j)

/-- The justifications from the `a`-th to the `a + n`-th. -/
def Problem.justsSlice (a n : Nat) : Bool :=
  (((A.steps.zip A.justs).drop a).take n).all (fun (s, j) => P.justOk A s j)

/-- The derived steps from the `a`-th on. -/
def Answer.rupFrom (a : Nat) : Bool :=
  Clausal.checkT (A.steps.map Clausal.Step.clause) a (A.steps.drop a)

/-- The derived steps from the `a`-th to the `a + n`-th. -/
def Answer.rupSlice (a n : Nat) : Bool :=
  a + n ≤ A.steps.length && Clausal.checkT (A.steps.map Clausal.Step.clause) a ((A.steps.drop a).take n)

theorem Problem.justsFrom_slice {a n : Nat} (h₁ : P.justsSlice A a n = true) (h₂ : P.justsFrom A (a + n) = true) :
    P.justsFrom A a = true := by
  unfold Problem.justsSlice at h₁
  unfold Problem.justsFrom at h₂ ⊢
  rw [← List.take_append_drop n ((A.steps.zip A.justs).drop a), List.all_append, h₁, List.drop_drop, h₂]
  rfl

theorem Problem.justsFrom_end {a : Nat} (h : A.steps.length ≤ a) : P.justsFrom A a = true := by
  unfold Problem.justsFrom
  rw [List.drop_eq_nil_of_le (by simp; omega)]
  rfl

theorem Answer.rupFrom_slice {a n : Nat} (h₁ : A.rupSlice a n = true) (h₂ : A.rupFrom (a + n) = true) :
    A.rupFrom a = true := by
  unfold Answer.rupSlice at h₁
  unfold Answer.rupFrom at h₂ ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h₁
  obtain ⟨hn, h₁⟩ := h₁
  have hl : ((A.steps.drop a).take n).length = n := by simp; omega
  rw [← List.take_append_drop n (A.steps.drop a), Clausal.checkT_append, h₁, hl, List.drop_drop, h₂]
  rfl

theorem Answer.rupFrom_end {a : Nat} (h : A.steps.length ≤ a) : A.rupFrom a = true := by
  unfold Answer.rupFrom
  rw [List.drop_eq_nil_of_le h]
  rfl

theorem Problem.accepts_of_slices (hb : P.acceptsBase A = true) (hj : P.justsFrom A 0 = true)
    (hr : A.rupFrom 0 = true) : P.accepts A = true := by
  unfold Problem.acceptsBase at hb
  unfold Problem.justsFrom at hj
  unfold Answer.rupFrom at hr
  unfold Problem.accepts
  simp only [List.drop_zero] at hj hr
  simp only [hj, hr, Bool.and_true, Bool.true_and]
  exact hb

end Checker

/-! ## Models -/

variable {R U : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R]
  [OrderedRing R] [IsCharP R 0]

attribute [local instance low] Lean.Grind.Ring.intCast

/-- The value of constructor `C` applied to `xs`. -/
def ctorVal (M : Model R U) (C : Nat) (xs : List (Val R U)) : Val R U :=
  if xs.isEmpty then M.const C else M.app (M.const C) xs

/-- The sorts of the arguments of symbol `C`. -/
def Problem.argSorts (P : Problem) (C : Nat) : List Nat :=
  match P.sig.decls[C]? with
  | some s =>
    match P.sig.sorts[s]? with
    | some (.fn as _) => as
    | _ => []
  | none => []

/-- What a model of a problem satisfies: its sorts and symbols, the laws of
    datatypes (as a term algebra: `size` decreases from a constructor term to
    its arguments), those of array stores, and extensionality: two functions
    are equal when they agree on all arguments. Arguments of bit-vector sorts
    only range over their values in range. -/
structure Problem.Laws (P : Problem) (M : Model R U) (size : Val R U → Nat) : Prop where
  sound : M.Sound P.sig P.bvIndex
  sel : ∀ d cs C T Ss, (d, cs) ∈ P.datatypes → (C, T, Ss) ∈ cs →
    ∀ xs (i : Nat) S x, Forall2 (fun a x => M.dom a x ∧ inRange P.bvIndex a x) (P.argSorts C) xs → Ss[i]? = some S → xs[i]? = some x →
      M.app (M.const S) [ctorVal M C xs] = x
  test : ∀ d cs C T Ss, (d, cs) ∈ P.datatypes → (C, T, Ss) ∈ cs →
    ∀ xs, Forall2 (fun a x => M.dom a x ∧ inRange P.bvIndex a x) (P.argSorts C) xs → M.app (M.const T) [ctorVal M C xs] = .bool true
  testOther : ∀ d cs C T Ss C' T' Ss', (d, cs) ∈ P.datatypes → (C, T, Ss) ∈ cs → (C', T', Ss') ∈ cs →
    C ≠ C' → ∀ ys, Forall2 (fun a x => M.dom a x ∧ inRange P.bvIndex a x) (P.argSorts C') ys → M.app (M.const T) [ctorVal M C' ys] ≠ .bool true
  inj : ∀ d cs C T Ss, (d, cs) ∈ P.datatypes → (C, T, Ss) ∈ cs →
    ∀ xs ys, Forall2 (fun a x => M.dom a x ∧ inRange P.bvIndex a x) (P.argSorts C) xs → Forall2 (fun a x => M.dom a x ∧ inRange P.bvIndex a x) (P.argSorts C) ys →
      ctorVal M C xs = ctorVal M C ys → xs = ys
  distinct : ∀ d cs C T Ss C' T' Ss', (d, cs) ∈ P.datatypes → (C, T, Ss) ∈ cs → (C', T', Ss') ∈ cs →
    C ≠ C' → ∀ xs ys, Forall2 (fun a x => M.dom a x ∧ inRange P.bvIndex a x) (P.argSorts C) xs → Forall2 (fun a x => M.dom a x ∧ inRange P.bvIndex a x) (P.argSorts C') ys →
      ctorVal M C xs ≠ ctorVal M C' ys
  expand : ∀ d cs C T Ss, (d, cs) ∈ P.datatypes → (C, T, Ss) ∈ cs →
    ∀ v, M.dom d v → M.app (M.const T) [v] = .bool true →
      v = ctorVal M C (Ss.map fun S => M.app (M.const S) [v])
  smaller : ∀ d cs C T Ss, (d, cs) ∈ P.datatypes → (C, T, Ss) ∈ cs →
    ∀ xs x, Forall2 (fun a x => M.dom a x ∧ inRange P.bvIndex a x) (P.argSorts C) xs → x ∈ xs → size x < size (ctorVal M C xs)
  exhaust : ∀ d cs, (d, cs) ∈ P.datatypes → ∀ v, M.dom d v →
    ∃ ct ∈ cs, M.app (M.const ct.2.1) [v] = .bool true
  store : ∀ n ∈ P.stores, ∀ s arr idx el, P.sig.decls[n]? = some s →
    P.sig.sorts[s]? = some (.fn [arr, idx, el] arr) → P.sig.sorts[arr]? = some (.fn [idx] el) →
    ∀ a i v j, M.dom arr a → M.dom idx i → M.dom el v → M.dom idx j →
      inRange P.bvIndex idx i → inRange P.bvIndex idx j → inRange P.bvIndex el v →
      (j = i → M.app (M.app (M.const n) [a, i, v]) [j] = v) ∧
      (j ≠ i → M.app (M.app (M.const n) [a, i, v]) [j] = M.app a [j])
  ext : ∀ s as r f g, P.sig.sorts[s]? = some (.fn as r) → M.dom s f → M.dom s g →
    (∀ xs, Forall2 (fun a x => M.dom a x ∧ inRange P.bvIndex a x) as xs → M.app f xs = M.app g xs) → f = g

/-- The value of an LIA variable. -/
noncomputable def liaVal (P : Problem) (A : Answer) (I : Interp R U) (x : Nat) : R :=
  Lia.eval (nums I P.nodes) (A.liaForm x)

/-- What an LIA atom says. -/
def liaHolds (P : Problem) (A : Answer) (I : Interp R U) : LiaAtom → Prop
  | .bound x c strict => if strict then liaVal P A I x < (c : R) else liaVal P A I x ≤ (c : R)
  | .equal x c => liaVal P A I x = (c : R)

open Classical in
/-- The assignment of a model: a level holds when it is assumed and its
    formulas hold; a variable takes the truth of its formula, or of its atom. -/
noncomputable def assign (P : Problem) (A : Answer) (I : Interp R U) : Assignment := fun v =>
  match A.levels.lookup v with
  | some fs => decide (v ∈ A.assumed ∧ ∀ f ∈ fs, holds I P.nodes f)
  | none =>
    match (A.meaning[v]?).getD none with
    | some f => decide (holds I P.nodes f)
    | none =>
      match A.liaAtom v with
      | some a => decide (liaHolds P A I a)
      | none =>
        match A.ufAtom v with
        | some (a, b) => decide (val I P.nodes a = val I P.nodes b)
        | none => false

theorem lt_of_node {nodes : List Node} {i : Nat} {n : Node} (h : nodes[i]? = some n) : i < nodes.length := by
  apply Classical.byContradiction; intro hn
  rw [List.getElem?_eq_none (by omega)] at h; cases h

theorem child_lt {nodes : List Node} (hw : wellFormed nodes = true) {i : Nat} {n : Node}
    (h : nodes[i]? = some n) {j : Nat} (m : j ∈ n.children) : j < i := by
  have := List.all_eq_true.mp hw i (List.mem_range.mpr (lt_of_node h))
  rw [Tab.at_eq, h] at this
  simp only [List.all_eq_true, decide_eq_true_eq] at this
  exact this j m

theorem typed_node {sig : Sig} {nodes : List Node} {sortOf : List Nat} (ht : typed sig nodes sortOf = true)
    {i : Nat} {n : Node} (h : nodes[i]? = some n) : nodeTyped sig sortOf n (sortOf[i]?.getD 0) = true := by
  simp only [typed, Tab.at_eq, Bool.and_eq_true, List.all_eq_true, List.mem_range] at ht
  have := ht.2 i (lt_of_node h)
  rw [h] at this
  exact this

theorem lookup_mem {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ {l : List (α × β)} {a : α} {b : β}, l.lookup a = some b → (a, b) ∈ l
  | [], _, _, h => by simp [List.lookup] at h
  | (k, v) :: l, a, b, h => by
    simp only [List.lookup] at h
    split at h
    · rename_i e; cases h; simp only [beq_iff_eq] at e; subst e; simp
    · exact List.mem_cons_of_mem _ (lookup_mem h)

theorem mem_zip_of_mem {α β : Type} {a : α} :
    ∀ {l : List α} {l' : List β}, l.length = l'.length → a ∈ l → ∃ b, (a, b) ∈ l.zip l'
  | [], _, _, h => by simp at h
  | _ :: _, [], e, _ => by simp at e
  | x :: l, y :: l', e, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨y, by simp⟩
    · obtain ⟨b, hb⟩ := mem_zip_of_mem (by simpa using e) h
      exact ⟨b, by simp [hb]⟩

theorem lookup_isSome {α β : Type} [BEq α] [LawfulBEq α] {l : List (α × β)} {a : α} {b : β}
    (h : (a, b) ∈ l) : (l.lookup a).isSome = true := by
  induction l with
  | nil => simp at h
  | cons p l ih =>
    obtain ⟨k, v⟩ := p
    simp only [List.lookup]
    split
    · rfl
    · rename_i e
      rcases List.mem_cons.mp h with h | h
      · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp at e
      · exact ih h

section
variable {P : Problem} {A : Answer}

/-- The facts of an accepted answer. -/
structure Accepted (P : Problem) (A : Answer) : Prop where
  wits : P.witnessesOk A = true
  wf : wellFormed P.nodes = true
  typed : typed P.sig P.nodes P.sortOf = true
  dt : P.dtOk = true
  stores : P.storesOk = true
  classes : P.classesOk A = true
  trueLit : ∃ t, (A.meaning[A.trueLit.var]?).getD none = some t ∧ A.trueLit.pos = true ∧ P.nodes[t]? = some .tt
  trueClass : ∃ t f, P.nodes[A.trueClass]? = some (.bterm t) ∧ P.nodes[A.falseClass]? = some (.bterm f) ∧
    P.nodes[t]? = some .tt ∧ P.nodes[f]? = some .ff
  levels : ∀ s fs, (s, fs) ∈ A.levels →
    (A.meaning[s]?).getD none = none ∧ A.ufAtom s = none ∧ A.liaAtom s = none
  atoms : ∀ v, v < max A.ufAtoms.length A.liaAtoms.length → P.atomOk A v = true
  justs : ∀ s j, (s, j) ∈ A.steps.zip A.justs → P.justOk A s j = true
  length : A.steps.length = A.justs.length
  conclusion : ∃ db goal, Clausal.check [] A.steps = some db ∧ db[A.conclusion]? = some goal ∧
    ∀ l ∈ goal, l.pos = false ∧ l.var ∈ A.assumed ∧ (A.levels.lookup l.var).isSome = true

theorem accepted (h : P.accepts A = true) : Accepted P A := by
  unfold Problem.accepts at h
  simp only [Problem.witnessesOkF_eq, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, Problem.node_eq,
    Tab.at_eq, Answer.meaningOf_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hwit, hw⟩, ht⟩, hdt⟩, hst⟩, hcl⟩, htl⟩, htc⟩, hlv⟩, hat⟩, hlen⟩, hj⟩, hc⟩ := h
  refine ⟨hwit, hw, ht, hdt, hst, hcl, ?_, ?_, ?_, hat, fun s j m => hj (s, j) m, hlen, ?_⟩
  · split at htl
    · rename_i t ht'
      simp only [Bool.and_eq_true, beq_iff_eq] at htl
      exact ⟨t, ht', htl.1, htl.2⟩
    · cases htl
  · split at htc
    · rename_i t f h1 h2
      simp only [Bool.and_eq_true, beq_iff_eq] at htc
      exact ⟨t, f, h1, h2, htc.1, htc.2⟩
    · cases htc
  · intro s fs m
    have := hlv (s, fs) m
    simp only [Option.isNone_iff_eq_none] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  · obtain ⟨hck, hc⟩ := hc
    split at hc
    · rename_i goal hg
      refine ⟨_, goal, Clausal.check_of_checkT hck, hg, fun l m => ?_⟩
      have := List.all_eq_true.mp hc l m
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_iff_mem] at this
      exact ⟨this.1.1, this.1.2, this.2⟩
    · cases hc

variable (hA : Accepted P A) {I : Interp R U}
include hA

theorem level_none {v : Nat} (h : ((A.meaning[v]?).getD none).isSome ∨ (A.ufAtom v).isSome ∨
    (A.liaAtom v).isSome) : A.levels.lookup v = none := by
  cases e : A.levels.lookup v with
  | none => rfl
  | some fs =>
    obtain ⟨h1, h2, h3⟩ := hA.levels _ _ (lookup_mem e)
    simp [h1, h2, h3] at h

theorem assign_meaning {v f : Nat} (h : (A.meaning[v]?).getD none = some f) :
    assign P A I v = true ↔ holds I P.nodes f := by
  unfold assign
  rw [level_none hA (Or.inl (by simp [h]))]
  simp only [h, decide_eq_true_eq]

theorem val_trueClass : val I P.nodes A.trueClass = .bool true := by
  obtain ⟨t, f, h1, _, h3, _⟩ := hA.trueClass
  rw [val_bterm hA.wf h1]
  simp [holds_tt hA.wf h3]

theorem val_falseClass : val I P.nodes A.falseClass = .bool false := by
  obtain ⟨t, f, _, h2, _, h4⟩ := hA.trueClass
  rw [val_bterm hA.wf h2]
  simp [not_holds_ff hA.wf h4]

theorem atomOk_of {v : Nat} (h : (A.ufAtom v).isSome ∨ (A.liaAtom v).isSome) : P.atomOk A v = true := by
  apply hA.atoms
  rcases h with h | h
  · have : v < A.ufAtoms.length := by
      apply Classical.byContradiction; intro hn
      simp [Answer.ufAtom, List.getElem?_eq_none (show A.ufAtoms.length ≤ v by omega)] at h
    omega
  · have : v < A.liaAtoms.length := by
      apply Classical.byContradiction; intro hn
      simp [Answer.liaAtom, List.getElem?_eq_none (show A.liaAtoms.length ≤ v by omega)] at h
    omega

theorem assign_uf {v a b : Nat} (h : A.ufAtom v = some (a, b)) :
    assign P A I v = true ↔ val I P.nodes a = val I P.nodes b := by
  have hok := atomOk_of hA (v := v) (Or.inl (by simp [h]))
  unfold Problem.atomOk at hok
  simp only [Problem.node_eq, Answer.meaningOf_eq, h, Bool.and_eq_true] at hok
  obtain ⟨⟨_, hm⟩, _⟩ := hok
  unfold assign
  rw [level_none hA (Or.inr (Or.inl (by simp [h])))]
  simp only
  split at hm
  · rename_i hn
    rw [hn]
    simp only [Option.isNone_iff_eq_none] at hm
    simp only [hm, h, decide_eq_true_eq]
  · rename_i m hn
    rw [hn]
    simp only [decide_eq_true_eq]
    split at hm
    · rename_i l r hnode
      simp only [Bool.and_eq_true, beq_iff_eq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      exact holds_eq hA.wf hnode
    · rename_i t hnode
      simp only [Bool.and_eq_true, beq_iff_eq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      rw [holds_pred hA.wf hnode, val_trueClass hA]
    · cases hm

theorem on_sound {l r x : Nat} {c : Int} (h : P.on A l r x c = true) :
    (val I P.nodes l).toR - (val I P.nodes r).toR = liaVal P A I x - (c : R) := by
  unfold Problem.on at h
  simp only [Problem.node_eq, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hf, rfl⟩ := h
  have e := congrArg (Lia.eval (nums I P.nodes)) hf
  rw [eval_canon, eval_canon, eval_append, Lia.eval_neg] at e
  rw [lin_sound hA.wf l, lin_sound hA.wf r]
  unfold liaVal
  rw [← e, Ring.intCast_sub]
  grind

end

section
variable {P : Problem} {A : Answer} (hA : Accepted P A) {M : Model R U} (hM : M.Sound P.sig P.bvIndex)
  (hrng : ∀ i < P.nodes.length, inRange P.bvIndex (P.sort i) (val M.toInterp P.nodes i))
include hA hM hrng

theorem nums_int {u : Nat} (h : P.isInt u = true) : ∃ n : Int, nums M.toInterp P.nodes u = (n : R) := by
  unfold Problem.isInt at h
  simp only [Tab.at_eq, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨k, hk⟩ := val_int hM hA.wf hA.typed hrng h.1 h.2
  exact ⟨k, by simp [nums, hk, Val.toR]⟩

/-- The environment of integer unknowns alone. -/
def intEnv (P : Problem) (A : Answer) : Lia.Env where
  form := A.liaForm
  isInt := P.isInt
  hypOk _ := false
  distinct _ _ _ := false

theorem intEnv_sound : (intEnv P A).Sound (nums M.toInterp P.nodes) where
  hyp _ _ h := by simp [intEnv] at h
  distinct _ _ _ _ h := by simp [intEnv] at h
  int _ h := nums_int hA hM hrng h

theorem assign_lia {v : Nat} {a : LiaAtom} (h : A.liaAtom v = some a) :
    assign P A M.toInterp v = true ↔ liaHolds P A M.toInterp a := by
  have hok := atomOk_of hA (v := v) (Or.inr (by simp [h]))
  unfold Problem.atomOk at hok
  simp only [Problem.node_eq, Answer.meaningOf_eq, h, Bool.and_eq_true] at hok
  obtain ⟨huf, hm⟩ := hok
  clear huf
  unfold assign
  rw [level_none hA (Or.inr (Or.inr (by simp [h])))]
  simp only
  split at hm
  · rename_i hn; rw [hn]; simp only [h, decide_eq_true_eq]
  · rename_i m hn
    rw [hn]
    simp only [decide_eq_true_eq]
    split at hm
    · rename_i x c strict l r hnode
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hm
      obtain ⟨rfl, hon⟩ := hm
      have := on_sound hA (I := M.toInterp) hon
      rw [holds_le hA.wf hnode]
      simp only [liaHolds, Bool.false_eq_true, ↓reduceIte]
      constructor <;> intro <;> grind
    · rename_i x c strict l r hnode
      rw [holds_lt hA.wf hnode]
      simp only [liaHolds]
      split at hm
      · rename_i hs
        subst hs
        have := on_sound hA (I := M.toInterp) hm
        simp only [↓reduceIte]
        constructor <;> intro <;> grind
      · rename_i hs
        simp only [Bool.not_eq_true] at hs
        subst hs
        simp only [Bool.and_eq_true] at hm
        obtain ⟨hint, hon⟩ := hm
        have := on_sound hA (I := M.toInterp) hon
        obtain ⟨n, hn'⟩ := Lia.eval_integral (intEnv P A) (nums M.toInterp P.nodes)
          (intEnv_sound hA hM hrng) _ hint
        have hv : liaVal P A M.toInterp x = (n : R) := hn'
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [Ring.intCast_add, Ring.intCast_one] at this
        rw [hv] at this ⊢
        constructor
        · intro hlt
          have : (n : R) < ((c + 1 : Int) : R) := by rw [Ring.intCast_add, Ring.intCast_one]; grind
          have := cast_le (R := R) (show n ≤ c by
            apply Classical.byContradiction; intro hc
            have := cast_le (R := R) (show c + 1 ≤ n by omega); grind)
          exact this
        · intro hle
          have := OrderedRing.zero_lt_one (R := R)
          grind
    · rename_i x c l r hnode
      simp only [Bool.and_eq_true] at hm
      obtain ⟨⟨hon, hl⟩, hr⟩ := hm
      have := on_sound hA (I := M.toInterp) hon
      rw [holds_eq hA.wf hnode]
      simp only [liaHolds]
      have nl : ∃ x, val M.toInterp P.nodes l = .num x := by
        unfold Enc.numeric at hl; simp only [Tab.at_eq, Bool.and_eq_true, decide_eq_true_eq] at hl
        exact dom_num_of_numeric hM hl.2 (val_dom hM hA.wf hA.typed hrng l hl.1)
      have nr : ∃ x, val M.toInterp P.nodes r = .num x := by
        unfold Enc.numeric at hr; simp only [Tab.at_eq, Bool.and_eq_true, decide_eq_true_eq] at hr
        exact dom_num_of_numeric hM hr.2 (val_dom hM hA.wf hA.typed hrng r hr.1)
      obtain ⟨a, ha⟩ := nl
      obtain ⟨b, hb⟩ := nr
      rw [ha, hb] at this ⊢
      simp only [Val.toR] at this
      constructor
      · intro e; cases e; grind
      · intro e; have : a = b := by grind
        rw [this]
    · cases hm

end

theorem lookup_some_mem {d : Nat} {cs : List (Nat × Nat × List Nat)}
    {l : List (Nat × List (Nat × Nat × List Nat))} (h : l.lookup d = some cs) : (d, cs) ∈ l :=
  lookup_mem h

section
variable {P : Problem} {A : Answer} (hA : Accepted P A) {M : Model R U} {size : Val R U → Nat}
  (hL : P.Laws M size) (hin : ∀ f ∈ P.inputs, holds M.toInterp P.nodes f)
  (hrng : ∀ i < P.nodes.length, inRange P.bvIndex (P.sort i) (val M.toInterp P.nodes i))
  (hext : ∀ (k eq eqw : Nat) (ws : List Nat), A.exts[k]? = some (eq, eqw, ws) →
    holds M.toInterp P.nodes eq ∨ ¬holds M.toInterp P.nodes eqw)
  (hwr : ∀ n w, (P.enc A).width n = some w → ∃ k : Int, M.const n = .num (k : R) ∧ 0 ≤ k ∧ k < 2 ^ w)
include hA hL hrng

theorem dom_of {i : Nat} (hi : i < P.nodes.length) : M.dom (P.sort i) (val M.toInterp P.nodes i) :=
  val_dom hL.sound hA.wf hA.typed hrng i hi

include hin hext hwr in
theorem enc_sound : (P.enc A).Sound M.toInterp (assign P A M.toInterp) where
  meaning v f h := assign_meaning hA ((Enc.meaningOf_eq _ _).symm.trans h)
  trueLit := by
    obtain ⟨t, ht, hp, hn⟩ := hA.trueLit
    unfold Lit.holds; simp only [Problem.enc]; rw [hp]
    exact (assign_meaning hA ht).mpr (holds_tt hA.wf hn)
  inputs := hin
  levels s fs h hs := by
    unfold assign at hs
    simp only [Enc.guarded, Problem.enc] at h
    rw [h] at hs
    simp only [decide_eq_true_eq] at hs
    exact hs.2
  retired s h hn := by
    simp only [Enc.guarded, Problem.enc, Option.isSome_iff_exists] at h
    obtain ⟨fs, h⟩ := h
    unfold assign
    rw [h]
    simp only [decide_eq_false_iff_not]
    intro hs; exact absurd hs.1 (by simpa [Problem.enc] using hn)
  numeric i h := by
    simp only [Enc.numeric, Problem.enc, Tab.at_eq, Bool.and_eq_true, decide_eq_true_eq] at h
    exact dom_num_of_numeric hL.sound h.2 (dom_of hA hL hrng h.1)
  exhaustive t cs ht h := by
    simp only [Problem.enc] at h ht
    exact hL.exhaust _ _ (lookup_mem h) _ (dom_of hA hL hrng ht)
  store r s k n a i v j hr hs hk hn := by
    simp only [Enc.node_eq, Problem.enc] at hr hs hk ⊢
    simp only [Problem.enc] at hn
    -- the declarations of the store
    have hst := List.all_eq_true.mp hA.stores n hn
    split at hst
    · rename_i s0 hd
      split at hst
      · rename_i arr idx el arr' hs0
        simp only [Bool.and_eq_true, beq_iff_eq] at hst
        obtain ⟨rfl, harr⟩ := hst
        -- the sorts of the nodes
        have tk := typed_node hA.typed hk
        simp only [Tab.at_eq, nodeTyped, beq_iff_eq] at tk
        rw [hd] at tk
        have ts := typed_node hA.typed hs
        simp only [Tab.at_eq, nodeTyped] at ts
        rw [← Option.some.inj tk, hs0] at ts
        simp only [Sig.allFit, Bool.and_true, Bool.and_eq_true, beq_iff_eq, List.map_cons, List.map_nil] at ts
        obtain ⟨hsort, ha, hi, hv⟩ := ts
        have tr := typed_node hA.typed hr
        simp only [Tab.at_eq, nodeTyped] at tr
        rw [← hsort, harr] at tr
        simp only [Sig.allFit, Bool.and_true, Bool.and_eq_true, beq_iff_eq, List.map_cons, List.map_nil] at tr
        obtain ⟨-, hj⟩ := tr
        have lr := lt_of_node hr
        have ls := child_lt hA.wf hr (j := s) (by simp [Node.children])
        have lj := child_lt hA.wf hr (j := j) (by simp [Node.children])
        have lk := child_lt hA.wf hs (j := k) (by simp [Node.children])
        have la := child_lt hA.wf hs (j := a) (by simp [Node.children])
        have li := child_lt hA.wf hs (j := i) (by simp [Node.children])
        have lv := child_lt hA.wf hs (j := v) (by simp [Node.children])
        have da := dom_of hA hL hrng (i := a) (by omega)
        have di := dom_of hA hL hrng (i := i) (by omega)
        have dv := dom_of hA hL hrng (i := v) (by omega)
        have dj := dom_of hA hL hrng (i := j) (by omega)
        have ra := hrng a (by omega)
        have ri := hrng i (by omega)
        have rj := hrng j (by omega)
        have rv := hrng v (by omega)
        simp only [Problem.sort_eq] at da di dv dj ra ri rj rv
        obtain ⟨da, -⟩ := dom_fit hL.sound ha da ra
        obtain ⟨di, ri⟩ := dom_fit hL.sound hi di ri
        obtain ⟨dv, rv⟩ := dom_fit hL.sound hv dv rv
        obtain ⟨dj, rj⟩ := dom_fit hL.sound hj dj rj
        have law := hL.store n hn s0 _ idx el hd hs0 harr _ _ _ _ da di dv dj ri rj rv
        rw [val_app hA.wf hr, val_app hA.wf hs, val_const hA.wf hk]
        simp only [List.map_cons, List.map_nil]
        exact law
      · cases hst
    · cases hst
  ext k eq eqw ws h := hext k eq eqw ws h
  range n w h := hwr n w h

end

theorem ctorEntry_mem {P : Problem} {C d T : Nat} {Ss : List Nat} (h : P.ctorEntry C = some (d, T, Ss)) :
    ∃ cs, (d, cs) ∈ P.datatypes ∧ (C, T, Ss) ∈ cs := by
  unfold Problem.ctorEntry at h
  generalize P.datatypes = l at h ⊢
  induction l with
  | nil => simp at h
  | cons e es ih =>
    obtain ⟨d', cs⟩ := e
    simp only [List.findSome?_cons] at h
    split at h
    · rename_i r hr
      cases h
      cases hf : cs.find? (·.1 == C) with
      | none => rw [hf] at hr; cases hr
      | some ct =>
        rw [hf] at hr
        obtain ⟨C', T', Ss'⟩ := ct
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl, rfl⟩ := hr
        have := List.find?_some hf
        simp only [beq_iff_eq] at this
        subst this
        exact ⟨cs, by simp, List.mem_of_find?_eq_some hf⟩
    · obtain ⟨cs', h1, h2⟩ := ih h
      exact ⟨cs', List.mem_cons_of_mem _ h1, h2⟩

theorem nodupB_unique {l : List (Nat × List (Nat × Nat × List Nat))} (h : nodupB (l.map (·.1)) = true)
    {d : Nat} {cs cs' : List (Nat × Nat × List Nat)} (h1 : (d, cs) ∈ l) (h2 : (d, cs') ∈ l) : cs = cs' := by
  induction l with
  | nil => simp at h1
  | cons e l ih =>
    simp only [List.map_cons, nodupB, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_any_beq,
      List.any_eq_false, beq_iff_eq] at h
    rcases List.mem_cons.mp h1 with e1 | h1 <;> rcases List.mem_cons.mp h2 with e2 | h2
    · rw [← e1] at e2; simp only [Prod.mk.injEq] at e2; exact e2.2.symm
    · exfalso; rw [← e1] at h; exact h.1 d (List.mem_map.mpr ⟨_, h2, rfl⟩) rfl
    · exfalso; rw [← e2] at h; exact h.1 d (List.mem_map.mpr ⟨_, h1, rfl⟩) rfl
    · exact ih h.2 h1 h2

section
variable {P : Problem} {A : Answer} (hA : Accepted P A) {M : Model R U} {size : Val R U → Nat}
  (hL : P.Laws M size) (hin : ∀ f ∈ P.inputs, holds M.toInterp P.nodes f)
  (hrng : ∀ i < P.nodes.length, inRange P.bvIndex (P.sort i) (val M.toInterp P.nodes i))
  (hext : ∀ (k eq eqw : Nat) (ws : List Nat), A.exts[k]? = some (eq, eqw, ws) →
    holds M.toInterp P.nodes eq ∨ ¬holds M.toInterp P.nodes eqw)
  (hwr : ∀ n w, (P.enc A).width n = some w → ∃ k : Int, M.const n = .num (k : R) ∧ 0 ≤ k ∧ k < 2 ^ w)
include hA hL hrng

theorem symOf_val {c C : Nat} (h : P.symOf c = some C) : val M.toInterp P.nodes c = M.const C := by
  unfold Problem.symOf at h
  split at h
  · rename_i n hn; cases h; exact val_const hA.wf (Problem.node_some hn)
  · cases h

theorem symOf_node {c C : Nat} (h : P.symOf c = some C) : P.nodes[c]? = some (.const C) := by
  unfold Problem.symOf at h
  split at h
  · rename_i n hn; cases h; exact Problem.node_some hn
  · cases h

/-- What a constructor class stands for. -/
theorem ufCtor_info {c : Nat} {ss : List Nat} (h : A.ufCtors.lookup c = some ss) :
    ∃ C d T Ss, P.symOf c = some C ∧ P.ctorEntry C = some (d, T, Ss) ∧ ss.map P.symOf = Ss.map some := by
  have := List.all_eq_true.mp (by have := hA.classes; simp only [Problem.classesOk, Bool.and_eq_true] at this; exact this.1)
    (c, ss) (lookup_mem h)
  simp only at this
  split at this
  · rename_i C hC
    split at this
    · rename_i d T Ss he
      simp only [beq_iff_eq] at this
      exact ⟨C, d, T, Ss, hC, he, this⟩
    · cases this
  · cases this

theorem map_symOf_length {ss Ss : List Nat} (h : ss.map P.symOf = Ss.map some) : ss.length = Ss.length := by
  have := congrArg List.length h; simpa using this

/-- What `ctorOf` finds: a constructor term, its arguments of the constructor's
    sorts. -/
theorem ctorOf_info {x c : Nat} {args : List Nat} (h : Uf.ctorOf (P.ufEnv A) x = some (c, args)) :
    ∃ C d T Ss ss, P.symOf c = some C ∧ P.ctorEntry C = some (d, T, Ss) ∧ A.ufCtors.lookup c = some ss ∧
      ss.map P.symOf = Ss.map some ∧ args.length = Ss.length ∧
      val M.toInterp P.nodes x = ctorVal M C (args.map (val M.toInterp P.nodes)) ∧
      Forall2 (fun a x => M.dom a x ∧ inRange P.bvIndex a x) (P.argSorts C) (args.map (val M.toInterp P.nodes)) := by
  unfold Uf.ctorOf at h
  split at h
  · rename_i hx
    cases h
    obtain ⟨C, d, T, Ss, hC, he, hm⟩ := ufCtor_info hA hL hrng hx
    have hSs : Ss = [] := by cases Ss with
      | nil => rfl
      | cons _ _ => simp at hm
    subst hSs
    refine ⟨C, d, T, [], [], hC, he, hx, hm, rfl, ?_, ?_⟩
    · simp [ctorVal, symOf_val hA hL hrng hC]
    · -- a constant constructor has no argument sorts
      obtain ⟨cs, hd, hct⟩ := ctorEntry_mem he
      have hdt := hA.dt
      simp only [Problem.dtOk, Bool.and_eq_true, List.all_eq_true] at hdt
      have := (hdt.2 _ hd)
      have hc := (this.2 _ hct).1.1
      simp only [List.isEmpty_nil, ↓reduceIte] at hc
      split at hc
      · rename_i s hs
        simp only [beq_iff_eq] at hc
        simp only [Sig.is, beq_iff_eq] at this
        have hu : P.sig.sorts[s]? = some .user := by rw [hc]; exact this.1
        simp only [List.map_nil, Problem.argSorts, hs, hu]
        trivial
      · cases hc
  · split at h
    · rename_i f as hn
      split at h
      · rename_i ss hf
        split at h
        · rename_i hc
          cases h
          simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hc
          obtain ⟨C, d, T, Ss, hC, he, hm⟩ := ufCtor_info hA hL hrng hf
          have hn' : P.nodes[x]? = some (.app c args) := by
            simp only [Problem.ufEnv, Problem.node_eq] at hn
            split at hn
            · rename_i f' args' h'; cases hn; exact h'
            · cases hn
          refine ⟨C, d, T, Ss, ss, hC, he, hf, hm, by rw [hc.1, map_symOf_length hA hL hrng hm], ?_, ?_⟩
          · rw [val_app hA.wf hn', symOf_val hA hL hrng hC]
            have : (args.map (val M.toInterp P.nodes)).isEmpty = false := by
              cases args with
              | nil => cases ss with
                | nil => exact absurd rfl hc.2
                | cons _ _ => simp at hc
              | cons _ _ => rfl
            simp [ctorVal, this]
          · have tx := typed_node hA.typed hn'
            have tc := typed_node hA.typed (symOf_node hA hL hrng hC)
            simp only [Tab.at_eq, nodeTyped, beq_iff_eq] at tx tc
            split at tx
            · rename_i as' r hs
              simp only [Bool.and_eq_true, beq_iff_eq] at tx
              simp only [Problem.argSorts, tc, hs]
              exact forall2_fit hL.sound args as' tx.2 fun j m =>
                have hj := Nat.lt_trans (child_lt hA.wf hn' (by simp [Node.children, m])) (lt_of_node hn')
                ⟨dom_of hA hL hrng hj, hrng j hj⟩
            · cases tx
        · cases h
      · cases h
    · cases h

theorem ufTester_info {t c : Nat} (h : A.ufTesters.lookup t = some c) :
    ∃ T C d Ss, P.symOf t = some T ∧ P.symOf c = some C ∧ P.ctorEntry C = some (d, T, Ss) := by
  have := List.all_eq_true.mp (by have := hA.classes; simp only [Problem.classesOk, Bool.and_eq_true] at this; exact this.2)
    (t, c) (lookup_mem h)
  simp only at this
  split at this
  · rename_i T C hT hC
    simp only [Bool.and_eq_true] at this
    split at this
    · rename_i d T' Ss he
      simp only [beq_iff_eq] at this
      obtain ⟨_, hTT⟩ := this
      exact ⟨T, C, d, Ss, hT, hC, by rw [he, hTT]⟩
    · simp at this
  · cases this

theorem ufEnv_node {p f : Nat} {args : List Nat} (h : (P.ufEnv A).node p = some (f, args)) :
    P.nodes[p]? = some (.app f args) := by
  simp only [Problem.ufEnv, Problem.node_eq] at h
  split at h
  · rename_i f' args' h'; cases h; exact h'
  · cases h

omit hA hL hrng in
theorem sel_get {ss Ss : List Nat} (hm : ss.map P.symOf = Ss.map some) {i s : Nat} (h : ss[i]? = some s) :
    ∃ S, Ss[i]? = some S ∧ P.symOf s = some S := by
  have := congrArg (·[i]?) hm
  simp only [List.getElem?_map, h, Option.map_some] at this
  cases e : Ss[i]? with
  | none => rw [e] at this; cases this
  | some S => rw [e] at this; simp only [Option.map_some, Option.some.injEq] at this; exact ⟨S, rfl, this⟩

theorem sel_map {ss Ss : List Nat} (hm : ss.map P.symOf = Ss.map some) (v : Val R U) :
    ss.map (fun s => M.app (val M.toInterp P.nodes s) [v]) = Ss.map (fun S => M.app (M.const S) [v]) := by
  induction ss generalizing Ss with
  | nil => cases Ss with
    | nil => rfl
    | cons _ _ => simp at hm
  | cons s ss ih =>
    cases Ss with
    | nil => simp at hm
    | cons S Ss =>
      simp only [List.map_cons, List.cons.injEq] at hm ⊢
      exact ⟨by rw [symOf_val hA hL hrng hm.1], ih hm.2⟩

/-- The tester `T` of a sort `d` applies to the sort's values. -/
theorem tester_arg {p t a T C d : Nat} {Ss : List Nat} (hp : P.nodes[p]? = some (.app t [a]))
    (hT : P.symOf t = some T) (he : P.ctorEntry C = some (d, T, Ss)) :
    M.dom d (val M.toInterp P.nodes a) := by
  obtain ⟨cs, hd, hct⟩ := ctorEntry_mem he
  have hdt := hA.dt
  simp only [Problem.dtOk, Bool.and_eq_true, List.all_eq_true] at hdt
  have := (hdt.2 _ hd)
  have hT' := (this.2 _ hct).1.2
  have tp := typed_node hA.typed hp
  have tt := typed_node hA.typed (symOf_node hA hL hrng hT)
  simp only [Tab.at_eq, nodeTyped, beq_iff_eq] at tp tt
  split at hT'
  · rename_i s hs
    rw [hs] at tt
    split at hT'
    · rename_i d' b hs'
      simp only [Bool.and_eq_true, beq_iff_eq] at hT'
      have hst : P.sortOf[t]?.getD 0 = s := (Option.some.inj tt).symm
      simp only [hst, hs', Sig.allFit, Bool.and_true, Bool.and_eq_true, beq_iff_eq, List.map_cons,
        List.map_nil] at tp
      have la := Nat.lt_trans (child_lt hA.wf hp (j := a) (by simp [Node.children])) (lt_of_node hp)
      have := dom_of hA hL hrng (i := a) la
      have ra := hrng a la
      simp only [Problem.sort_eq] at this ra
      rw [← hT'.1]
      exact (dom_fit hL.sound tp.2 this ra).1
    · cases hT'
  · cases hT'

/-- The classes as values of the model. -/
noncomputable def ufModel (P : Problem) (M : Model R U) (size : Val R U → Nat) : Uf.Model (Val R U) where
  val := val M.toInterp P.nodes
  app := M.app
  size := size

theorem trueLit_holds : A.trueLit.holds (assign P A M.toInterp) := by
  obtain ⟨t, ht, hp, hn⟩ := hA.trueLit
  unfold Lit.holds; rw [hp]
  exact (assign_meaning hA ht).mpr (holds_tt hA.wf hn)

/-- Two constructors of the same datatype, by `sameType`. -/
theorem sameType_info {c d : Nat} (h : (P.ufEnv A).sameType c d = true) :
    ∃ C D e cs T Ss T' Ss', P.symOf c = some C ∧ P.symOf d = some D ∧ C ≠ D ∧ (e, cs) ∈ P.datatypes ∧
      (C, T, Ss) ∈ cs ∧ (D, T', Ss') ∈ cs ∧ P.ctorEntry C = some (e, T, Ss) ∧
      P.ctorEntry D = some (e, T', Ss') := by
  simp only [Problem.ufEnv] at h
  split at h
  · rename_i C D hC hD
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨hne, h⟩ := h
    split at h
    · rename_i e p e' p' he he'
      obtain ⟨T, Ss⟩ := p
      obtain ⟨T', Ss'⟩ := p'
      simp only [beq_iff_eq] at h; subst h
      obtain ⟨cs, hd, hc⟩ := ctorEntry_mem he
      obtain ⟨cs', hd', hc'⟩ := ctorEntry_mem he'
      have hdt := hA.dt
      simp only [Problem.dtOk, Bool.and_eq_true] at hdt
      have := nodupB_unique hdt.1 hd hd'
      subst this
      exact ⟨C, D, e, cs, T, Ss, T', Ss', hC, hD, hne, hd, hc, hc', he, he'⟩
    · cases h
  · cases h

theorem uf_sound : (P.ufEnv A).Sound (ufModel P M size) (assign P A M.toInterp) where
  node x f args h := by
    simp only [ufModel]; rw [val_app hA.wf (ufEnv_node hA hL hrng h)]
  atom v a b h := assign_uf hA h
  trueLit := trueLit_holds hA hL hrng
  trueFalse := by
    simp only [ufModel, Problem.ufEnv]; rw [val_trueClass hA, val_falseClass hA]; simp
  bool v x h := by
    have hok := atomOk_of hA (v := v) (Or.inl (by simp [Problem.ufEnv] at h; simp [h]))
    simp only [Problem.ufEnv] at h
    unfold Problem.atomOk at hok
    simp only [Problem.node_eq, Tab.at_eq, h, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, not_true_eq_false,
      false_or, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨hx, hb⟩, _⟩, _⟩ := hok
    have := dom_of hA hL hrng hx
    simp only [Sig.is, beq_iff_eq] at hb
    obtain ⟨b, hb'⟩ := (hL.sound.bool _ _ hb).mp this
    simp only [ufModel, Problem.ufEnv]
    rw [val_trueClass hA, val_falseClass hA, hb']
    cases b <;> simp
  select x c args ss i s b hx hc hs hb := by
    obtain ⟨C, d, T, Ss, ss', hC, he, hl, hm, hlen, hv, hdom⟩ := ctorOf_info hA hL hrng hx
    simp only [Problem.ufEnv] at hc
    rw [hl] at hc; cases hc
    obtain ⟨S, hS, hsym⟩ := sel_get hm hs
    obtain ⟨cs, hd, hct⟩ := ctorEntry_mem he
    simp only [ufModel]
    rw [symOf_val hA hL hrng hsym, hv]
    exact hL.sel _ _ _ _ _ hd hct _ i S _ hdom hS (by rw [List.getElem?_map, hb]; rfl)
  test x c args t hx ht := by
    obtain ⟨C, d, T, Ss, ss, hC, he, _, _, _, hv, hdom⟩ := ctorOf_info hA hL hrng hx
    simp only [Problem.ufEnv] at ht
    obtain ⟨T', C', d', Ss', hT', hC', he'⟩ := ufTester_info hA hL hrng ht
    rw [hC] at hC'; cases hC'
    rw [he] at he'; cases he'
    obtain ⟨cs, hd, hct⟩ := ctorEntry_mem he
    simp only [ufModel, Problem.ufEnv]
    rw [symOf_val hA hL hrng hT', hv, val_trueClass hA]
    exact hL.test _ _ _ _ _ hd hct _ hdom
  testOther x d args t c hx ht hne hsame := by
    obtain ⟨D, e, TD, SD, ss, hD, heD, _, _, _, hv, hdom⟩ := ctorOf_info hA hL hrng hx
    simp only [Problem.ufEnv] at ht
    obtain ⟨T, C, e', Ss, hT, hC, heC⟩ := ufTester_info hA hL hrng ht
    obtain ⟨C', D', e'', cs, T1, Ss1, T2, Ss2, hC', hD', hCD, hd, hc1, hc2, he1, he2⟩ :=
      sameType_info hA hL hrng hsame
    rw [hC] at hC'; cases hC'
    rw [hD] at hD'; cases hD'
    rw [heC] at he1; cases he1
    simp only [ufModel, Problem.ufEnv]
    rw [symOf_val hA hL hrng hT, hv, val_trueClass hA]
    rw [heD] at he2; cases he2
    exact hL.testOther _ _ _ _ _ _ _ _ hd hc1 hc2 hCD _ hdom
  inj x y c xs ys hx hy hxy := by
    obtain ⟨C, d, T, Ss, ss, hC, he, _, _, _, hv, hdom⟩ := ctorOf_info hA hL hrng hx
    obtain ⟨C', d', T', Ss', ss', hC', he', _, _, _, hv', hdom'⟩ := ctorOf_info hA hL hrng hy
    rw [hC] at hC'; cases hC'
    obtain ⟨cs, hd, hct⟩ := ctorEntry_mem he
    simp only [ufModel] at hxy ⊢
    rw [hv, hv'] at hxy
    exact hL.inj _ _ _ _ _ hd hct _ _ hdom hdom' hxy
  distinct x y c d xs ys hx hy hne hsame := by
    obtain ⟨C, e, T, Ss, ss, hC, he, _, _, _, hv, hdom⟩ := ctorOf_info hA hL hrng hx
    obtain ⟨D, e', T', Ss', ss', hD, he', _, _, _, hv', hdom'⟩ := ctorOf_info hA hL hrng hy
    obtain ⟨C1, D1, e1, cs, T1, Ss1, T2, Ss2, hC1, hD1, hCD, hd, hc1, hc2, he1, he2⟩ :=
      sameType_info hA hL hrng hsame
    rw [hC] at hC1; cases hC1
    rw [hD] at hD1; cases hD1
    simp only [ufModel]
    rw [hv, hv']
    exact hL.distinct _ _ _ _ _ _ _ _ hd hc1 hc2 hCD _ _ hdom hdom'
  expandConst p t c a hp ht hc happ := by
    simp only [Problem.ufEnv] at ht hc
    obtain ⟨T, C, d, Ss, hT, hC, he⟩ := ufTester_info hA hL hrng ht
    obtain ⟨C', d', T', Ss', hC', he', hm⟩ := ufCtor_info hA hL hrng hc
    rw [hC] at hC'; cases hC'
    rw [he] at he'; cases he'
    have hSs : Ss = [] := by cases Ss with
      | nil => rfl
      | cons _ _ => simp at hm
    subst hSs
    obtain ⟨cs, hd, hct⟩ := ctorEntry_mem he
    have hp' := ufEnv_node hA hL hrng hp
    have hdom := tester_arg hA hL hrng hp' hT he
    simp only [ufModel, Problem.ufEnv] at happ ⊢
    rw [symOf_val hA hL hrng hT, val_trueClass hA] at happ
    rw [hL.expand _ _ _ _ _ hd hct _ hdom happ, symOf_val hA hL hrng hC]
    simp [ctorVal]
  expand p t c ss a b fields hp ht hc happ hb hf := by
    simp only [Problem.ufEnv] at ht hc
    obtain ⟨T, C, d, Ss, hT, hC, he⟩ := ufTester_info hA hL hrng ht
    obtain ⟨C', d', T', Ss', ss', hC', he', hl, hm, _, hv, _⟩ := ctorOf_info hA hL hrng hb
    rw [hC] at hC'; cases hC'
    rw [he] at he'; cases he'
    rw [hc] at hl; cases hl
    obtain ⟨cs, hd, hct⟩ := ctorEntry_mem he
    have hp' := ufEnv_node hA hL hrng hp
    have hdom := tester_arg hA hL hrng hp' hT he
    simp only [ufModel, Problem.ufEnv] at happ hf ⊢
    rw [symOf_val hA hL hrng hT, val_trueClass hA] at happ
    rw [hL.expand _ _ _ _ _ hd hct _ hdom happ, hv, hf, sel_map hA hL hrng hm]
  smaller x c args a hx ha := by
    obtain ⟨C, d, T, Ss, ss, hC, he, _, _, _, hv, hdom⟩ := ctorOf_info hA hL hrng hx
    obtain ⟨cs, hd, hct⟩ := ctorEntry_mem he
    simp only [ufModel]
    rw [hv]
    exact hL.smaller _ _ _ _ _ hd hct _ _ hdom (List.mem_map_of_mem ha)

/-- A lemma with a cutting-planes certificate holds: otherwise the negations of
    its literals are bounds the certificate refutes. -/
theorem lia_sound {c : Clause} {nodes : List Lia.Node} (h : Lia.accepts (P.liaEnv A c) nodes = true) :
    c.holds (assign P A M.toInterp) := by
  apply Classical.byContradiction
  intro hn
  apply Lia.accepts_sound h (nums M.toInterp P.nodes)
  refine ⟨?_, ?_, ?_⟩
  · intro hy _ hok
    simp only [Problem.liaEnv, hypOk, Bool.and_eq_true, List.contains_iff_mem] at hok
    obtain ⟨hm, hok⟩ := hok
    generalize litOf hy.reason = L at hm hok
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hm
    have hlit : l.neg.holds (assign P A M.toInterp) :=
      (Lit.holds_neg _ _).mpr fun hh => hn ⟨l, hl, hh⟩
    generalize l.neg = L at hlit hok
    unfold Lit.holds at hlit
    obtain ⟨v, pos⟩ := L
    simp only at hlit hok
    split at hok
    · rename_i x k strict heq
      simp only [Bool.and_eq_true, beq_iff_eq] at hok
      obtain ⟨⟨⟨hx, hk⟩, hs⟩, hu⟩ := hok
      have e := assign_lia hA hL.sound hrng heq
      rw [hlit] at e
      simp only [Lia.side, Lia.Ineq.holds, Problem.liaEnv, hx, hk, hs, hu, liaHolds, liaVal] at e ⊢
      cases pos <;> cases strict <;>
        simp only [Bool.false_eq_true, ↓reduceIte, false_iff, true_iff, Bool.not_false, Bool.not_true,
          Lia.eval_neg, rat_neg, Lia.rat_intCast] at e ⊢ <;> grind
    · rename_i x k heq
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hok
      obtain ⟨⟨⟨hp, hx⟩, hk⟩, hs⟩ := hok
      have e := assign_lia hA hL.sound hrng heq
      rw [hlit, hp] at e
      simp only [Lia.side, Lia.Ineq.holds, Problem.liaEnv, hx, hk, hs, liaHolds, liaVal, true_iff] at e ⊢
      cases hy.upper <;>
        simp only [Bool.false_eq_true, ↓reduceIte, Lia.eval_neg, rat_neg, Lia.rat_intCast,
          ] at e ⊢ <;> grind
    · cases hok
  · intro _ _ _ _ h; simp [Problem.liaEnv] at h
  · intro u hu; exact nums_int hA hL.sound hrng hu

include hin hext hwr in
/-- Every premise of an accepted proof holds. -/
theorem premises_hold :
    ∀ s ∈ A.steps, s.premise = true → s.clause.holds (assign P A M.toInterp) := by
  intro s hs hp
  obtain ⟨j, hj⟩ := mem_zip_of_mem hA.length hs
  have hok := hA.justs s j hj
  cases s <;> cases j <;> simp only [Problem.justOk, Step.premise, Bool.false_eq_true] at hok hp
  · exact inputOk_sound hA.wf (enc_sound hA hL hin hrng hext hwr) hok
  · exact Uf.accepts_sound (uf_sound hA hL hrng) hok
  · exact lia_sound hA hL hrng hok

end

/-- Soundness for a model whose witnesses take the right values: the
    extensionality instances and the ranges of the witnesses hold. Any model
    extends to such a model (`Problem.accepts_sound`, in `Extend.lean`). -/
theorem accepts_sound_of_witnesses {P : Problem} {A : Answer} (hA : Accepted P A) (M : Model R U)
    (size : Val R U → Nat) (hL : P.Laws M size)
    (hin : ∀ f ∈ P.inputs, holds M.toInterp P.nodes f)
    (hlev : ∀ s ∈ A.assumed, ∀ fs, A.levels.lookup s = some fs → ∀ f ∈ fs, holds M.toInterp P.nodes f)
    (hrng : ∀ i < P.nodes.length, inRange P.bvIndex (P.sort i) (val M.toInterp P.nodes i))
    (hext : ∀ (k eq eqw : Nat) (ws : List Nat), A.exts[k]? = some (eq, eqw, ws) →
      holds M.toInterp P.nodes eq ∨ ¬holds M.toInterp P.nodes eqw)
    (hwr : ∀ n w, (P.enc A).width n = some w → ∃ k : Int, M.const n = .num (k : R) ∧ 0 ≤ k ∧ k < 2 ^ w) :
    False := by
  obtain ⟨db, goal, hc, hg, hlits⟩ := hA.conclusion
  obtain ⟨l, hl, hh⟩ := Clausal.check_sound A.steps [] db (by simp)
    (premises_hold hA hL hin hrng hext hwr) hc goal
    (List.mem_of_getElem? hg)
  obtain ⟨hpos, has, hlv⟩ := hlits l hl
  obtain ⟨fs, hfs⟩ := Option.isSome_iff_exists.mp hlv
  unfold Lit.holds assign at hh
  rw [hpos, hfs] at hh
  simp only [decide_eq_false_iff_not] at hh
  exact hh ⟨has, hlev _ has fs hfs⟩

end Vik.Low
