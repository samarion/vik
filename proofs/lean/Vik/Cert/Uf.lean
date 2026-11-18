import Vik.Cert.Clausal

/-!
# Equality proofs

A checker for the lemmas of Vik's theory of uninterpreted functions and
datatypes (`UfLemmas` in `vik/ProofCheck.scala`), and its soundness: a lemma it
accepts holds under every assignment that agrees with a model of the terms.

Terms are numbered classes; a class may be an application `f(x₁, …, xₙ)` of
other classes, `f` a class too. A proof of `a = b` is built from the equalities
of the hypotheses, reflexivity, symmetry, transitivity, congruence, and the
rules of the datatypes. Proofs are lists of steps, each referring to earlier
ones by their index.
-/

namespace Vik.Uf

open Vik.Clausal

/-- What the checker is given. `atom v` is the equality `a = b` that variable
    `v` stands for; `node x` the application class `x` is, if any;
    `ctors c` the selectors of the constructor `c`; `tester t` the constructor
    `t` tests. `trueLit` is the literal of `true`. -/
structure Env where
  atom : Nat → Option (Nat × Nat)
  node : Nat → Option (Nat × List Nat)
  trueClass : Nat
  falseClass : Nat
  trueLit : Lit
  ctors : Nat → Option (List Nat)
  tester : Nat → Option Nat
  /-- Whether two constructors are of the same datatype. -/
  sameType : Nat → Nat → Bool

inductive Step where
  | refl (a : Nat)
  | given (a b : Nat) (reason : Lit)
  | symm (i : Nat)
  | trans (i j : Nat)
  | cong (a b : Nat) (f : Nat) (args : List Nat)
  | rule (a b : Nat) (premises : List Nat)
  deriving Repr

inductive Cert where
  | disequal (p : Nat) (reason : Lit)
  | contradiction (ps : List Nat)
  | equal (p : Nat)
  | apart (left right : Nat) (reason : Lit)
  deriving Repr

def same (p q : Nat × Nat) : Bool := p == q || p == (q.2, q.1)

/-- Whether the hypothesis `reason` asserts `a = b`. -/
def asserted (env : Env) (hyps : List Lit) (a b : Nat) (reason : Lit) : Bool :=
  hyps.contains reason &&
    match env.atom reason.var with
    | some (x, y) =>
      if reason.pos then same (a, b) (x, y)
      else y == env.trueClass && same (a, b) (x, env.falseClass)
    | none => false

/-- The head of class `x` when it is a constructor applied to as many
    arguments as it has selectors, or a constant constructor. -/
def ctorOf (env : Env) (x : Nat) : Option (Nat × List Nat) :=
  match env.ctors x with
  | some [] => some (x, [])
  | _ =>
    match env.node x with
    | some (f, args) =>
      match env.ctors f with
      | some ss => if args.length == ss.length && !ss.isEmpty then some (f, args) else none
      | none => none
    | none => none

def indexOf (s : Nat) : List Nat → Option Nat
  | [] => none
  | t :: ts => if t == s then some 0 else (indexOf s ts).map (· + 1)

def selectorRule (env : Env) (a b p q : Nat) : Bool :=
  match env.node a, ctorOf env q with
  | some (s, [x]), some (c, args) =>
    x == p &&
      match env.ctors c with
      | some ss => match indexOf s ss with
        | some i => args[i]? == some b
        | none => false
      | none => false
  | _, _ => false

def testerRule (env : Env) (a b p q : Nat) : Bool :=
  match env.node a, ctorOf env q with
  | some (t, [x]), some (c, _) => x == p && b == env.trueClass && env.tester t == some c
  | _, _ => false

def injRule (env : Env) (a b p q : Nat) : Bool :=
  match ctorOf env p, ctorOf env q with
  | some (c, xs), some (d, ys) => c == d && (xs.zip ys).contains (a, b)
  | _, _ => false

def fieldsOk (env : Env) (a : Nat) : List Nat → List Nat → Bool
  | [], [] => true
  | f :: fs, s :: ss => env.node f == some (s, [a]) && fieldsOk env a fs ss
  | _, _ => false

def expansionRule (env : Env) (a b p q : Nat) : Bool :=
  q == env.trueClass &&
    match env.node p with
    | some (t, [x]) =>
      x == a &&
        match env.tester t with
        | some c =>
          match env.ctors c with
          | some [] => b == c
          | some ss =>
            match ctorOf env b with
            | some (d, fields) => d == c && fieldsOk env a fields ss
            | none => false
          | none => false
        | none => false
    | _ => false

def oriented (env : Env) (a b p q : Nat) : Bool :=
  selectorRule env a b p q || testerRule env a b p q || injRule env a b p q
    || expansionRule env a b p q

def rule (env : Env) (a b : Nat) : List (Nat × Nat) → Bool
  | [(p, q)] => oriented env a b p q || oriented env b a p q
  | _ => false

/-- Whether the classes `ps` are, pairwise, the classes of `qs`, by the
    proofs `is`. -/
def argsOk (done : List (Nat × Nat)) : List Nat → List Nat → List Nat → Bool
  | [], [], [] => true
  | i :: is, x :: xs, y :: ys => done[i]? == some (x, y) && argsOk done is xs ys
  | _, _, _ => false

def premises (done : List (Nat × Nat)) : List Nat → Option (List (Nat × Nat))
  | [] => some []
  | i :: is =>
    match done[i]?, premises done is with
    | some p, some ps => some (p :: ps)
    | _, _ => none

def step (env : Env) (hyps : List Lit) (done : List (Nat × Nat)) : Step → Option (Nat × Nat)
  | .refl a => some (a, a)
  | .given a b reason => if asserted env hyps a b reason then some (a, b) else none
  | .symm i => (done[i]?).map (fun p => (p.2, p.1))
  | .trans i j =>
    match done[i]?, done[j]? with
    | some (a, b), some (c, d) => if b == c then some (a, d) else none
    | _, _ => none
  | .cong a b f args =>
    match env.node a, env.node b with
    | some (fa, xs), some (fb, ys) =>
      if done[f]? == some (fa, fb) && argsOk done args xs ys then some (a, b) else none
    | _, _ => none
  | .rule a b ps =>
    match premises done ps with
    | some holding => if rule env a b holding then some (a, b) else none
    | none => none

def steps (env : Env) (hyps : List Lit) (done : List (Nat × Nat)) : List Step → Option (List (Nat × Nat))
  | [] => some done
  | s :: rest =>
    match step env hyps done s with
    | some p => steps env hyps (done ++ [p]) rest
    | none => none

/-- Whether the hypothesis `reason` makes `a` and `b` distinct. -/
def apartOk (env : Env) (hyps : List Lit) (a b : Nat) (reason : Lit) : Bool :=
  hyps.contains reason &&
    if reason == env.trueLit then same (a, b) (env.trueClass, env.falseClass)
    else !reason.pos &&
      match env.atom reason.var with
      | some atom => same (a, b) atom
      | none => false

def isArg (env : Env) (a prev : Nat) : Bool :=
  match ctorOf env prev with
  | some (_, args) => args.contains a
  | none => false

/-- Each argument of a constructor node is the next node, the last one's the
    first: `links prev rest a₀`. -/
def links (env : Env) : Nat → List (Nat × Nat) → Nat → Bool
  | prev, [], a0 => isArg env a0 prev
  | prev, (a, n) :: rest, a0 => isArg env a prev && links env n rest a0

def clash (env : Env) : List (Nat × Nat) → Bool
  | [(p, q)] =>
    match ctorOf env p, ctorOf env q with
    | some (c, _), some (d, _) => c != d && env.sameType c d
    | _, _ => false
  | [(test, t), (x, n)] =>
    t == env.trueClass &&
      match env.node test, ctorOf env n with
      | some (f, [y]), some (d, _) =>
        y == x && (match env.tester f with | some c => c != d && env.sameType c d | none => false)
      | _, _ => false
  | _ => false

def cycle (env : Env) : List (Nat × Nat) → Bool
  | [] => false
  | (a0, n0) :: rest => links env n0 rest a0

/-- Whether the certificate shows that `clause` holds. -/
def accepts (env : Env) (clause : Clause) (proof : List Step) (cert : Cert) : Bool :=
  let hyps := clause.map Lit.neg
  match steps env hyps [] proof with
  | none => false
  | some done =>
    match cert with
    | .disequal p reason =>
      match done[p]? with
      | some (a, b) => apartOk env hyps a b reason
      | none => false
    | .contradiction ps =>
      match premises done ps with
      | some holding => clash env holding || cycle env holding
      | none => false
    | .equal p =>
      match clause, done[p]? with
      | l :: _, some q =>
        l.pos && match env.atom l.var with
          | some atom => same q atom
          | none => false
      | _, _ => false
    | .apart left right reason =>
      match clause, done[left]?, done[right]? with
      | l :: _, some (t, s), some (u, s2) =>
        !l.pos && apartOk env hyps s s2 reason &&
          match env.atom l.var with
          | some atom => (t, u) == atom
          | none => false
      | _, _, _ => false

/-! ## Soundness -/

/-- A model of the classes: their values, application, and a size that grows
    from the arguments of a constructor to the constructor term. -/
structure Model (V : Type) where
  val : Nat → V
  app : V → List V → V
  size : V → Nat

/-- What a model of the classes and an assignment agreeing with it satisfy:
    applications, atoms, Booleans and the laws of the datatypes. -/
structure Env.Sound {V : Type} (env : Env) (M : Model V) (ρ : Assignment) : Prop where
  node : ∀ x f args, env.node x = some (f, args) → M.val x = M.app (M.val f) (args.map M.val)
  atom : ∀ v a b, env.atom v = some (a, b) → (ρ v = true ↔ M.val a = M.val b)
  trueLit : env.trueLit.holds ρ
  trueFalse : M.val env.trueClass ≠ M.val env.falseClass
  bool : ∀ v x, env.atom v = some (x, env.trueClass) →
    M.val x = M.val env.trueClass ∨ M.val x = M.val env.falseClass
  select : ∀ x c args ss (i : Nat) s b, ctorOf env x = some (c, args) → env.ctors c = some ss →
    ss[i]? = some s → args[i]? = some b → M.app (M.val s) [M.val x] = M.val b
  test : ∀ x c args t, ctorOf env x = some (c, args) → env.tester t = some c →
    M.app (M.val t) [M.val x] = M.val env.trueClass
  testOther : ∀ x d args t c, ctorOf env x = some (d, args) → env.tester t = some c → c ≠ d →
    env.sameType c d = true → M.app (M.val t) [M.val x] ≠ M.val env.trueClass
  inj : ∀ x y c xs ys, ctorOf env x = some (c, xs) → ctorOf env y = some (c, ys) →
    M.val x = M.val y → xs.map M.val = ys.map M.val
  distinct : ∀ x y c d xs ys, ctorOf env x = some (c, xs) → ctorOf env y = some (d, ys) → c ≠ d →
    env.sameType c d = true → M.val x ≠ M.val y
  expandConst : ∀ p t c a, env.node p = some (t, [a]) → env.tester t = some c → env.ctors c = some [] →
    M.app (M.val t) [M.val a] = M.val env.trueClass → M.val a = M.val c
  expand : ∀ p t c ss a b fields, env.node p = some (t, [a]) → env.tester t = some c →
    env.ctors c = some ss →
    M.app (M.val t) [M.val a] = M.val env.trueClass → ctorOf env b = some (c, fields) →
    fields.map M.val = ss.map (fun s => M.app (M.val s) [M.val a]) → M.val a = M.val b
  smaller : ∀ x c args a, ctorOf env x = some (c, args) → a ∈ args →
    M.size (M.val a) < M.size (M.val x)

section
variable {V : Type} {env : Env} {M : Model V} {ρ : Assignment}

theorem same_val {p q : Nat × Nat} (h : same p q = true) (hq : M.val q.1 = M.val q.2) :
    M.val p.1 = M.val p.2 := by
  unfold same at h
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | rfl
  · exact hq
  · exact hq.symm

theorem same_comm {p q : Nat × Nat} : same p q = same q p := by
  obtain ⟨a, b⟩ := p; obtain ⟨c, d⟩ := q
  rw [Bool.eq_iff_iff]
  simp only [same, Bool.or_eq_true, beq_iff_eq, Prod.mk.injEq]
  omega

theorem indexOf_get {s : Nat} : ∀ {ss : List Nat} {i : Nat}, indexOf s ss = some i → ss[i]? = some s
  | [], _, h => by simp [indexOf] at h
  | t :: ts, i, h => by
    unfold indexOf at h
    split at h
    · rename_i e; cases h; simpa using e
    · cases h' : indexOf s ts with
      | none => rw [h'] at h; cases h
      | some j => rw [h'] at h; cases h; simpa using indexOf_get h'

theorem map_eq_zip {f : Nat → V} : ∀ {xs ys : List Nat} {a b : Nat},
    xs.map f = ys.map f → (a, b) ∈ xs.zip ys → f a = f b
  | [], _, _, _, _, h => by simp at h
  | _ :: _, [], _, _, _, h => by simp at h
  | x :: xs, y :: ys, a, b, e, h => by
    simp only [List.map_cons, List.cons.injEq] at e
    simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · exact e.1
    · exact map_eq_zip e.2 h

variable (hS : env.Sound M ρ)
include hS

theorem asserted_sound {hyps : List Lit} (hh : ∀ l ∈ hyps, l.holds ρ) {a b : Nat} {r : Lit}
    (h : asserted env hyps a b r = true) : M.val a = M.val b := by
  unfold asserted at h
  simp only [Bool.and_eq_true, List.contains_iff_mem] at h
  obtain ⟨hm, h⟩ := h
  have hr := hh r hm
  split at h
  · rename_i x y hat
    have ha := hS.atom _ _ _ hat
    unfold Lit.holds at hr
    split at h
    · rename_i hp
      exact same_val (q := (x, y)) h (ha.mp (by rw [hr, hp]))
    · rename_i hp
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, h⟩ := h
      have hne : M.val x ≠ M.val env.trueClass := by
        intro e; have := ha.mpr e; rw [hr] at this; simp_all
      have := hS.bool _ _ hat
      exact same_val (q := (x, env.falseClass)) h (by simpa [hne] using this)
  · cases h

theorem fieldsOk_map {a : Nat} : ∀ {fields ss : List Nat}, fieldsOk env a fields ss = true →
    fields.map M.val = ss.map (fun s => M.app (M.val s) [M.val a])
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [fieldsOk] at h
  | _ :: _, [], h => by simp [fieldsOk] at h
  | f :: fs, s :: ss, h => by
    simp only [fieldsOk, Bool.and_eq_true, beq_iff_eq] at h
    simp only [List.map_cons, hS.node _ _ _ h.1, List.map_nil, fieldsOk_map h.2]

theorem oriented_sound {a b p q : Nat} (h : oriented env a b p q = true) (hpq : M.val p = M.val q) :
    M.val a = M.val b := by
  unfold oriented at h
  simp only [Bool.or_eq_true] at h
  rcases h with ((h | h) | h) | h
  · -- a selector of a constructor node
    unfold selectorRule at h
    split at h
    · rename_i s x c args hn hc
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, h⟩ := h
      split at h
      · rename_i ss hss
        split at h
        · rename_i i hi
          simp only [beq_iff_eq] at h
          rw [hS.node _ _ _ hn, List.map_cons, List.map_nil, hpq]
          exact hS.select _ _ _ _ _ _ _ hc hss (indexOf_get hi) h
        · cases h
      · cases h
    · cases h
  · -- a tester of a constructor node
    unfold testerRule at h
    split at h
    · rename_i t x c args hn hc
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨rfl, rfl⟩, ht⟩ := h
      rw [hS.node _ _ _ hn, List.map_cons, List.map_nil, hpq]
      exact hS.test _ _ _ _ hc ht
    · cases h
  · -- injectivity
    unfold injRule at h
    split at h
    · rename_i c xs d ys hp hq
      simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at h
      obtain ⟨rfl, hm⟩ := h
      exact map_eq_zip (hS.inj _ _ _ _ _ hp hq hpq) hm
    · cases h
  · -- expansion of a tester
    unfold expansionRule at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h⟩ := h
    split at h
    · rename_i t x hn
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, h⟩ := h
      split at h
      · rename_i c ht
        have hp : M.app (M.val t) [M.val x] = M.val env.trueClass := by
          rw [← hpq, hS.node _ _ _ hn]; rfl
        split at h
        · rename_i hc
          simp only [beq_iff_eq] at h
          subst h
          exact hS.expandConst _ _ _ _ hn ht hc hp
        · rename_i ss _ hc
          split at h
          · rename_i d fields hb
            simp only [Bool.and_eq_true, beq_iff_eq] at h
            obtain ⟨rfl, hf⟩ := h
            exact hS.expand _ _ _ _ _ _ _ hn ht hc hp hb (fieldsOk_map hS hf)
          · cases h
        · cases h
      · cases h
    · cases h

theorem rule_sound {a b : Nat} {holding : List (Nat × Nat)} (h : rule env a b holding = true)
    (hh : ∀ pq ∈ holding, M.val pq.1 = M.val pq.2) : M.val a = M.val b := by
  match holding, h with
  | [(p, q)], h =>
    have hpq := hh (p, q) (by simp)
    unfold rule at h
    simp only [Bool.or_eq_true] at h
    rcases h with h | h
    · exact oriented_sound hS h hpq
    · exact (oriented_sound hS h hpq).symm

omit hS in
theorem premises_sound {done : List (Nat × Nat)} (hd : ∀ pq ∈ done, M.val pq.1 = M.val pq.2) :
    ∀ {is : List Nat} {holding : List (Nat × Nat)}, premises done is = some holding →
      ∀ pq ∈ holding, M.val pq.1 = M.val pq.2
  | [], holding, h => by simp [premises] at h; subst h; simp
  | i :: is, holding, h => by
    unfold premises at h
    split at h
    · rename_i p ps hp hps
      cases h
      intro pq m
      rcases List.mem_cons.mp m with rfl | m
      · exact hd _ (List.mem_of_getElem? hp)
      · exact premises_sound hd hps _ m
    · cases h

omit hS in
theorem argsOk_sound {done : List (Nat × Nat)} (hd : ∀ pq ∈ done, M.val pq.1 = M.val pq.2) :
    ∀ {is xs ys : List Nat}, argsOk done is xs ys = true → xs.map M.val = ys.map M.val
  | [], [], [], _ => rfl
  | i :: is, x :: xs, y :: ys, h => by
    simp only [argsOk, Bool.and_eq_true, beq_iff_eq] at h
    simp only [List.map_cons, hd _ (List.mem_of_getElem? h.1), argsOk_sound hd h.2]
  | [], [], _ :: _, h | [], _ :: _, _, h | _ :: _, [], _, h | _ :: _, _ :: _, [], h => by
    simp [argsOk] at h

theorem step_sound {hyps : List Lit} (hh : ∀ l ∈ hyps, l.holds ρ) {done : List (Nat × Nat)}
    (hd : ∀ pq ∈ done, M.val pq.1 = M.val pq.2) {s : Step} {p : Nat × Nat}
    (h : step env hyps done s = some p) : M.val p.1 = M.val p.2 := by
  cases s with
  | refl a => simp only [step] at h; cases h; rfl
  | given a b r =>
    simp only [step] at h
    split at h
    · rename_i ha; cases h; exact asserted_sound hS hh ha
    · cases h
  | symm i =>
    simp only [step] at h
    cases hi : done[i]? with
    | none => rw [hi] at h; cases h
    | some q => rw [hi] at h; cases h; exact (hd _ (List.mem_of_getElem? hi)).symm
  | trans i j =>
    simp only [step] at h
    split at h
    · rename_i a b c d hi hj
      split at h
      · rename_i e
        cases h
        simp only [beq_iff_eq] at e; subst e
        exact (hd _ (List.mem_of_getElem? hi)).trans (hd _ (List.mem_of_getElem? hj))
      · cases h
    · cases h
  | cong a b f args =>
    simp only [step] at h
    split at h
    · rename_i fa xs fb ys ha hb
      split at h
      · rename_i e
        cases h
        simp only [Bool.and_eq_true, beq_iff_eq] at e
        have hf := hd _ (List.mem_of_getElem? e.1)
        simp only [hS.node _ _ _ ha, hS.node _ _ _ hb, argsOk_sound hd e.2]
        rw [hf]
      · cases h
    · cases h
  | rule a b ps =>
    simp only [step] at h
    split at h
    · rename_i holding hp
      split at h
      · rename_i hr; cases h; exact rule_sound hS hr (premises_sound hd hp)
      · cases h
    · cases h

theorem steps_sound {hyps : List Lit} (hh : ∀ l ∈ hyps, l.holds ρ) :
    ∀ {ss : List Step} {done out : List (Nat × Nat)}, (∀ pq ∈ done, M.val pq.1 = M.val pq.2) →
      steps env hyps done ss = some out → ∀ pq ∈ out, M.val pq.1 = M.val pq.2
  | [], done, out, hd, h => by simp [steps] at h; subst h; exact hd
  | s :: rest, done, out, hd, h => by
    unfold steps at h
    split at h
    · rename_i p hp
      apply steps_sound hh _ h
      intro q m
      rcases List.mem_append.mp m with m | m
      · exact hd q m
      · rw [List.mem_singleton.mp m]; exact step_sound hS hh hd hp
    · cases h

theorem apartOk_sound {hyps : List Lit} (hh : ∀ l ∈ hyps, l.holds ρ) {a b : Nat} {r : Lit}
    (h : apartOk env hyps a b r = true) : M.val a ≠ M.val b := by
  unfold apartOk at h
  simp only [Bool.and_eq_true, List.contains_iff_mem] at h
  obtain ⟨hm, h⟩ := h
  split at h
  · intro e
    have := same_val (M := M) (p := (env.trueClass, env.falseClass)) (q := (a, b))
      (by unfold same at h ⊢; simp only [Bool.or_eq_true, beq_iff_eq, Prod.mk.injEq] at h ⊢; grind) e
    exact hS.trueFalse this
  · simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨hpos, h⟩ := h
    split at h
    · rename_i atom hat
      intro e
      have hr := hh r hm
      unfold Lit.holds at hr
      rw [hpos] at hr
      have := (hS.atom _ _ _ hat).mpr
        (same_val (M := M) (p := atom) (q := (a, b))
          (by unfold same at h ⊢; simp only [Bool.or_eq_true, beq_iff_eq] at h ⊢; grind) e)
      rw [hr] at this; cases this
    · cases h

theorem isArg_size {a prev : Nat} (h : isArg env a prev = true) :
    M.size (M.val a) < M.size (M.val prev) := by
  unfold isArg at h
  split at h
  · rename_i c args hc
    exact hS.smaller _ _ _ _ hc (List.contains_iff_mem.mp h)
  · cases h

theorem links_size {a0 : Nat} : ∀ {prev : Nat} {rest : List (Nat × Nat)},
    links env prev rest a0 = true → (∀ pq ∈ rest, M.val pq.1 = M.val pq.2) →
      M.size (M.val a0) < M.size (M.val prev)
  | prev, [], h, _ => isArg_size hS (by simpa [links] using h)
  | prev, (a, n) :: rest, h, hh => by
    simp only [links, Bool.and_eq_true] at h
    have h1 := isArg_size hS h.1
    have h2 := links_size h.2 (fun pq m => hh pq (List.mem_cons_of_mem _ m))
    have e := hh (a, n) (by simp)
    simp only at e
    rw [← e] at h2
    omega

theorem clash_sound {holding : List (Nat × Nat)} (h : clash env holding = true)
    (hh : ∀ pq ∈ holding, M.val pq.1 = M.val pq.2) : False := by
  match holding, h with
  | [(p, q)], h =>
    have e := hh (p, q) (by simp)
    simp only [clash] at h
    split at h
    · rename_i c xs d ys hp hq
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      exact hS.distinct _ _ _ _ _ _ hp hq h.1 h.2 e
    · cases h
  | [(test, t), (x, n)], h =>
    have e1 := hh (test, t) (by simp)
    have e2 := hh (x, n) (by simp)
    simp only at e1 e2
    simp only [clash, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h⟩ := h
    split at h
    · rename_i f y d ys hn hd
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, h⟩ := h
      split at h
      · rename_i c hc
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
        apply hS.testOther _ _ _ _ _ hd hc h.1 h.2
        rw [← e2, ← e1, hS.node _ _ _ hn]; rfl
      · cases h
    · cases h

theorem cycle_sound {holding : List (Nat × Nat)} (h : cycle env holding = true)
    (hh : ∀ pq ∈ holding, M.val pq.1 = M.val pq.2) : False := by
  match holding, h with
  | (a0, n0) :: rest, h =>
    simp only [cycle] at h
    have := links_size hS h (fun pq m => hh pq (List.mem_cons_of_mem _ m))
    have e := hh (a0, n0) (by simp)
    simp only at e
    rw [e] at this
    omega

/-- A lemma the checker accepts holds under every assignment that agrees with
    a model of the classes. -/
theorem accepts_sound {clause : Clause} {proof : List Step} {cert : Cert}
    (h : accepts env clause proof cert = true) : clause.holds ρ := by
  apply Classical.byContradiction
  intro hn
  have hh : ∀ l ∈ clause.map Lit.neg, l.holds ρ := by
    intro l m
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp m
    exact (Lit.holds_neg ρ k).mpr (fun hk' => hn ⟨k, hk, hk'⟩)
  unfold accepts at h
  simp only at h
  split at h
  · cases h
  · rename_i done hdone
    have hd := steps_sound hS hh (by simp) hdone
    split at h
    · split at h
      · rename_i a b hp
        exact apartOk_sound hS hh h (hd _ (List.mem_of_getElem? hp))
      · cases h
    · split at h
      · rename_i holding hp
        have := premises_sound hd hp
        simp only [Bool.or_eq_true] at h
        rcases h with h | h
        · exact clash_sound hS h this
        · exact cycle_sound hS h this
      · cases h
    · split at h
      · rename_i l _ q hq
        simp only [Bool.and_eq_true] at h
        obtain ⟨hpos, h⟩ := h
        split at h
        · rename_i atom hat
          apply hn
          refine ⟨l, by simp, ?_⟩
          unfold Lit.holds
          rw [hpos]
          exact (hS.atom _ _ _ hat).mpr
            (same_val (M := M) (p := atom) (q := q) (same_comm.trans h) (hd _ (List.mem_of_getElem? hq)))
        · cases h
      · cases h
    · split at h
      · rename_i l _ t s u s2 hl hr
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
        obtain ⟨⟨hpos, hap⟩, h⟩ := h
        split at h
        · rename_i atom hat
          simp only [beq_iff_eq] at h
          subst h
          apply hn
          refine ⟨l, by simp, ?_⟩
          unfold Lit.holds
          rw [hpos]
          cases hv : ρ l.var
          · rfl
          · have e := (hS.atom _ _ _ hat).mp hv
            have e1 := hd _ (List.mem_of_getElem? hl)
            have e2 := hd _ (List.mem_of_getElem? hr)
            simp only at e e1 e2
            exact absurd (e1.symm.trans (e.trans e2)) (apartOk_sound hS hh hap)
        · cases h
      · cases h

end

end Vik.Uf
