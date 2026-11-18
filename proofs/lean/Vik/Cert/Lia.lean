import Vik.Cert.RatCast

/-!
# Cutting-planes certificates

A checker for the certificates of Vik's linear arithmetic (`lia.Certificate`),
and its soundness: a certificate it accepts refutes the bounds it rests on,
over any ordered field of characteristic zero, with the integer unknowns at
integer values.

An inequality `Σ a·u ≤ r + d·δ` holds when `Σ a·u < r`, or `Σ a·u = r` and
`d ≥ 0`: it holds for every small enough positive `δ`. A certificate is a list
of nodes, each referring to earlier ones by their index, so that shared
derivations are checked once.
-/

set_option linter.unusedSectionVars false

namespace Vik.Lia

open Lean.Grind Vik.Real

/-! ## Linear forms -/

/-- `Σ a·u` over the pairs `(u, a)`. -/
abbrev Form := List (Nat × Rat)

/-- The sum of two forms, merging the pairs of a same unknown when both lists
    are sorted. `rec` is the sum with the rest of the first form. -/
def addCons (u : Nat) (a : Rat) (f : Form) (rec : Form → Form) : Form → Form
  | [] => (u, a) :: f
  | (v, b) :: g =>
    if u < v then (u, a) :: rec ((v, b) :: g)
    else if v < u then (v, b) :: addCons u a f rec g
    else if a + b = 0 then rec g else (u, a + b) :: rec g

def add : Form → Form → Form
  | [], g => g
  | (u, a) :: f, g => addCons u a f (add f) g

def scale (k : Rat) (f : Form) : Form :=
  if k = 0 then [] else f.map (fun p => (p.1, k * p.2))

def neg (f : Form) : Form := f.map (fun p => (p.1, -p.2))

/-- The pairs of `f`, their coefficients divided by `k`. -/
def divide (k : Rat) (f : Form) : Form := f.map (fun p => (p.1, p.2 / k))

/-- Whether `f` has integer coefficients over integer unknowns. -/
def integral (isInt : Nat → Bool) (f : Form) : Bool := f.all (fun p => isInt p.1 && p.2.den == 1)

/-- An inequality `form ≤ r + d·δ`. -/
structure Ineq where
  form : Form
  r : Rat
  d : Rat
  deriving DecidableEq, Repr

/-- `0 ≤ r + d·δ` with `r + d·δ < 0`. -/
def Ineq.contradiction (i : Ineq) : Bool := i.form.isEmpty && (i.r < 0 || (i.r == 0 && i.d < 0))

/-- A bound: `x ≤ c` (`upper`) or `x ≥ c`, strict or not, asserted for
    `reason`, or a hypothesis of a split if `reason` is negative. -/
structure Hyp where
  reason : Int
  x : Nat
  c : Int
  strict : Bool
  upper : Bool
  deriving DecidableEq, Repr

/-- What the checker is given: the expression `form x` each `x` stands for, the
    integer unknowns, the bounds the certificate may assume, and the
    disequalities `x ≠ c` asserted for a reason. -/
structure Env where
  form : Nat → Form
  isInt : Nat → Bool
  hypOk : Hyp → Bool
  distinct : Int → Nat → Int → Bool

/-- The inequality of a bound. -/
def side (env : Env) (h : Hyp) : Ineq :=
  let d : Rat := if h.strict then (if h.upper then -1 else 1) else 0
  if h.upper then ⟨env.form h.x, h.c, d⟩ else ⟨neg (env.form h.x), -(h.c : Rat), -d⟩

/-! ## Certificates -/

inductive Node where
  | hyp (h : Hyp)
  | comb (parts : List (Rat × Nat))
  | round (of : Nat)
  | split (reason : Int) (x : Nat) (floor ceil : Int) (low high : Nat) (except : Int) (at_ : Int)
      (strict : Bool)
  deriving Repr

/-- What a node proves, and the hypotheses of the enclosing splits it rests on. -/
abbrev Proved := Ineq × List Hyp

def union (a b : List Hyp) : List Hyp := a ++ b.filter (fun h => !a.contains h)

def combine (done : List Proved) : List (Rat × Nat) → Option Proved
  | [] => some (⟨[], 0, 0⟩, [])
  | (k, i) :: rest =>
    match done[i]?, combine done rest with
    | some (p, o), some (q, o') =>
      if 0 ≤ k then some (⟨add (scale k p.form) q.form, k * p.r + q.r, k * p.d + q.d⟩, union o o')
      else none
    | _, _ => none

/-- The least common multiple of the denominators, over the gcd of the
    numerators brought to it: `Σ a·u` takes multiples of it only. -/
def step (f : Form) : Rat :=
  let l := f.foldl (fun l p => Nat.lcm l p.2.den) 1
  let g := f.foldl (fun g p => Nat.gcd g (p.2.num * ((l / p.2.den : Nat) : Int)).natAbs) 0
  mkRat g l

/-- The greatest integer `k` with `k < q`, or `k ≤ q` if `d ≥ 0`. -/
def floorD (q d : Rat) : Int := if d < 0 && q.den == 1 then q.floor - 1 else q.floor

def gcdInts (f : Form) : Nat := f.foldl (fun g p => Nat.gcd g p.2.num.natAbs) 0

def roundIneq (env : Env) (p : Ineq) : Option Ineq :=
  if p.form.isEmpty then some p
  else
    let r := step p.form
    if 0 < r && integral env.isInt (divide r p.form) then
      some ⟨p.form, r * floorD (p.r / r) p.d, 0⟩
    else none

/-- Whether the values of `f`, multiples of `g`, leave none strictly between
    `floor` and `ceil`, but `at_` if `except` excludes it. -/
def gap (env : Env) (f : Form) (floor ceil : Int) (except at_ : Int) : Bool :=
  let g := gcdInts f
  let next := floor - floor % (g : Int) + g
  let left := if 0 ≤ except && next == at_ then next + g else next
  0 < g && integral env.isInt (divide ((g : Int) : Rat) f) && ceil ≤ left

def discharge (reason : Int) (h : Hyp) (o : List Hyp) : Option (List Hyp) :=
  if o.all (fun k => k.reason != reason || k == h) then some (o.filter (fun k => k.reason != reason))
  else none

/-- Whether a split may close: both sides contradictions, the disequality it
    uses asserted, and nothing left between its sides. -/
def splitOk (env : Env) (pl ph : Ineq) (x : Nat) (floor ceil except at_ : Int) (strict : Bool) : Bool :=
  pl.contradiction && ph.contradiction
    && (except < 0 || env.distinct except x at_)
    && (if strict then 0 ≤ except && floor == at_ && ceil == at_
        else gap env (env.form x) floor ceil except at_)

def node (env : Env) (done : List Proved) : Node → Option Proved
  | .hyp h =>
    if 0 ≤ h.reason then (if env.hypOk h then some (side env h, []) else none)
    else some (side env h, [h])
  | .comb parts => combine done parts
  | .round i =>
    match done[i]? with
    | some (p, o) => (roundIneq env p).map (fun q => (q, o))
    | none => none
  | .split reason x floor ceil low high except at_ strict =>
    match done[low]?, done[high]? with
    | some (pl, ol), some (ph, oh) =>
      if splitOk env pl ph x floor ceil except at_ strict then
        match discharge reason ⟨reason, x, floor, strict, true⟩ ol,
            discharge reason ⟨reason, x, ceil, strict, false⟩ oh with
        | some ol', some oh' => some (⟨[], -1, 0⟩, union ol' oh')
        | _, _ => none
      else none
    | _, _ => none

def check (env : Env) (done : List Proved) : List Node → Option (List Proved)
  | [] => some done
  | n :: rest =>
    match node env done n with
    | some p => check env (done ++ [p]) rest
    | none => none

/-- Whether the last node of `nodes` proves a contradiction, on no open
    hypothesis. -/
def accepts (env : Env) (nodes : List Node) : Bool :=
  match check env [] nodes with
  | some done =>
    match done.getLast? with
    | some (p, o) => p.contradiction && o.isEmpty
    | none => false
  | none => false

/-! ## Soundness -/

variable {R : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R]
  [OrderedRing R] [IsCharP R 0]

attribute [local instance low] Lean.Grind.Ring.intCast

def eval (ρ : Nat → R) : Form → R
  | [] => 0
  | (u, a) :: f => rat a * ρ u + eval ρ f

def Ineq.holds (ρ : Nat → R) (i : Ineq) : Prop :=
  eval ρ i.form < rat i.r ∨ (eval ρ i.form = rat i.r ∧ 0 ≤ i.d)

/-- What the checker assumes of a valuation `ρ` of the unknowns. -/
structure Env.Sound (env : Env) (ρ : Nat → R) : Prop where
  hyp : ∀ h, 0 ≤ h.reason → env.hypOk h = true → (side env h).holds ρ
  distinct : ∀ e x c, 0 ≤ e → env.distinct e x c = true → eval ρ (env.form x) ≠ (c : R)
  int : ∀ u, env.isInt u = true → ∃ n : Int, ρ u = n

def Valid (env : Env) (ρ : Nat → R) (p : Proved) : Prop :=
  (∀ h ∈ p.2, (side env h).holds ρ) → p.1.holds ρ

theorem eval_addCons (ρ : Nat → R) (u : Nat) (a : Rat) (f : Form) (rec : Form → Form)
    (hrec : ∀ g, eval ρ (rec g) = eval ρ f + eval ρ g) (g : Form) :
    eval ρ (addCons u a f rec g) = rat a * ρ u + eval ρ f + eval ρ g := by
  induction g with
  | nil => simp [addCons, eval] <;> grind
  | cons p g ih =>
    obtain ⟨v, b⟩ := p
    simp only [addCons]
    split
    · simp only [eval, hrec]; grind
    · split
      · simp only [eval, ih]; grind
      · have : u = v := by omega
        subst this
        have hab := rat_add (R := R) a b
        split
        · rename_i h0
          rw [h0, rat_zero] at hab
          simp only [eval, hrec]; grind
        · simp only [eval, hrec, hab]; grind

theorem eval_add (ρ : Nat → R) (f g : Form) : eval ρ (add f g) = eval ρ f + eval ρ g := by
  induction f generalizing g with
  | nil => simp [add, eval] <;> grind
  | cons p f ih =>
    obtain ⟨u, a⟩ := p
    simp only [add]
    rw [eval_addCons ρ u a f (add f) ih g]
    simp only [eval] <;> grind

theorem eval_scale (ρ : Nat → R) (k : Rat) (f : Form) : eval ρ (scale k f) = rat k * eval ρ f := by
  unfold scale
  split
  · rename_i h; subst h; simp [eval, rat_zero]; grind
  · induction f with
    | nil => simp [eval]; grind
    | cons p f ih => obtain ⟨u, a⟩ := p; simp only [List.map, eval, ih, rat_mul]; grind

theorem eval_neg (ρ : Nat → R) (f : Form) : eval ρ (neg f) = -eval ρ f := by
  unfold neg
  induction f with
  | nil => simp [eval]; grind
  | cons p f ih => obtain ⟨u, a⟩ := p; simp only [List.map, eval, ih, rat_neg]; grind

theorem eval_divide (ρ : Nat → R) {k : Rat} (hk : k ≠ 0) (f : Form) :
    eval ρ f = rat k * eval ρ (divide k f) := by
  unfold divide
  induction f with
  | nil => simp [eval]; grind
  | cons p f ih =>
    obtain ⟨u, a⟩ := p
    have : a = k * (a / k) := by grind
    have e := congrArg (rat (R := R)) this
    rw [rat_mul] at e
    simp only [List.map, eval]; rw [ih]; grind

theorem rat_den_one {a : Rat} (h : a.den = 1) : rat a = ((a.num : Int) : R) := by
  have e : a * ((1 : Int) : Rat) = ((a.num : Int) : Rat) := by
    have := mul_den a; rw [h] at this; simpa using this
  rw [rat_eq (d := 1) (by decide) e]; grind

theorem eval_integral (env : Env) (ρ : Nat → R) (hρ : env.Sound ρ) (f : Form)
    (h : integral env.isInt f = true) : ∃ n : Int, eval ρ f = (n : R) := by
  induction f with
  | nil => exact ⟨0, by simp [eval]; grind⟩
  | cons p f ih =>
    obtain ⟨u, a⟩ := p
    simp only [integral, List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hu, ha⟩, hf⟩ := h
    obtain ⟨n, hn⟩ := ih hf
    obtain ⟨m, hm⟩ := hρ.int u hu
    refine ⟨a.num * m + n, ?_⟩
    simp only [eval, hn, hm, rat_den_one ha, Ring.intCast_add, Ring.intCast_mul]

theorem rat_lt_iff {a b : Rat} : (rat a : R) < rat b ↔ a < b := by
  constructor
  · intro h; apply Classical.byContradiction; intro h'
    have := rat_le (R := R) (show b ≤ a by grind); grind
  · exact rat_lt

theorem rat_le_iff {a b : Rat} : (rat a : R) ≤ rat b ↔ a ≤ b := by
  constructor
  · intro h; apply Classical.byContradiction; intro h'
    have := rat_lt (R := R) (show b < a by grind); grind
  · exact rat_le

theorem holds_add {ρ : Nat → R} {f g : Form} {r d r' d' : Rat}
    (h1 : Ineq.holds ρ ⟨f, r, d⟩) (h2 : Ineq.holds ρ ⟨g, r', d'⟩) :
    Ineq.holds ρ ⟨add f g, r + r', d + d'⟩ := by
  simp only [Ineq.holds, eval_add, rat_add] at *
  rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
  all_goals first | (left; grind) | (right; constructor <;> grind)

theorem holds_scale {ρ : Nat → R} {f : Form} {r d k : Rat} (hk : 0 ≤ k)
    (h : Ineq.holds ρ ⟨f, r, d⟩) : Ineq.holds ρ ⟨scale k f, k * r, k * d⟩ := by
  simp only [Ineq.holds, eval_scale, rat_mul] at *
  by_cases k0 : k = 0
  · subst k0; right; simp [rat_zero]; grind
  · have kp : (0 : R) < rat k := by
      have := rat_lt (R := R) (show 0 < k by grind); rwa [rat_zero] at this
    rcases h with h | ⟨h, h'⟩
    · left; exact OrderedRing.mul_lt_mul_of_pos_left h kp
    · right; constructor
      · rw [h]
      · exact Rat.mul_nonneg hk h'

theorem contradiction_false {ρ : Nat → R} {i : Ineq} (h : i.contradiction = true)
    (hi : i.holds ρ) : False := by
  obtain ⟨form, r, d⟩ := i
  simp only [Ineq.contradiction, Bool.and_eq_true, List.isEmpty_iff, Bool.or_eq_true,
    decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨rfl, h⟩ := h
  simp only [Ineq.holds, eval] at hi
  rw [← rat_zero (R := R)] at hi
  rcases h with h | ⟨rfl, h⟩
  · have := rat_lt (R := R) h
    rcases hi with hi | ⟨hi, _⟩ <;> grind
  · rcases hi with hi | ⟨_, hi⟩ <;> grind

theorem le_floorD {M : Int} {q d : Rat} (h : (M : Rat) < q ∨ ((M : Rat) = q ∧ 0 ≤ d)) :
    M ≤ floorD q d := by
  unfold floorD
  rcases h with h | ⟨h, hd⟩
  · have h1 : M ≤ q.floor := Rat.le_floor_iff.mpr (Rat.le_of_lt h)
    split
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
      have hq : q = ((q.num : Int) : Rat) := by
        have := mul_den q; rw [hc.2] at this; simpa using this
      rw [hq, Rat.floor_intCast]
      rw [hq] at h
      have := Rat.intCast_lt_intCast.mp h
      omega
    · exact h1
  · have : ¬(d < 0) := by grind
    simp only [this, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    exact Rat.le_floor_iff.mpr (by rw [h]; exact Rat.le_refl)

theorem rat_intCast (n : Int) : rat (n : Rat) = (n : R) := rat_ofInt n

theorem holds_of_le {ρ : Nat → R} {f : Form} {r d : Rat} (hd : 0 ≤ d)
    (h : eval ρ f ≤ rat r) : Ineq.holds ρ ⟨f, r, d⟩ := by
  simp only [Ineq.holds]
  by_cases e : eval ρ f = rat r
  · exact Or.inr ⟨e, hd⟩
  · exact Or.inl (by grind)

theorem roundIneq_sound {env : Env} {ρ : Nat → R} (hρ : env.Sound ρ) {p q : Ineq}
    (h : roundIneq env p = some q) (hp : p.holds ρ) : q.holds ρ := by
  unfold roundIneq at h
  split at h
  · cases h; exact hp
  · dsimp only at h
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨hr, hi⟩ := hc
      generalize step p.form = r at *
      have hr0 : r ≠ 0 := by grind
      obtain ⟨M, hM⟩ := eval_integral env ρ hρ _ hi
      have hev : eval ρ p.form = rat (r * (M : Rat)) := by
        rw [eval_divide ρ hr0, hM, rat_mul, rat_intCast]
      have hq : p.r = r * (p.r / r) := by grind
      have key : (M : Rat) < p.r / r ∨ ((M : Rat) = p.r / r ∧ 0 ≤ p.d) := by
        unfold Ineq.holds at hp
        rw [hev, hq] at hp
        rcases hp with hp | ⟨hp, hd⟩
        · left
          have := rat_lt_iff.mp hp
          apply Classical.byContradiction; intro hn
          have := Rat.mul_le_mul_of_nonneg_left (show p.r / r ≤ (M : Rat) by grind) (Rat.le_of_lt hr)
          grind
        · right
          have := rat_inj hp
          refine ⟨?_, hd⟩
          apply Classical.byContradiction; intro hn
          by_cases h' : (M : Rat) < p.r / r
          · have := Rat.mul_lt_mul_of_pos_left h' hr; grind
          · have := Rat.mul_lt_mul_of_pos_left (show p.r / r < (M : Rat) by grind) hr; grind
      have hk := le_floorD key
      apply holds_of_le (Rat.le_refl)
      rw [hev, rat_le_iff]
      exact Rat.mul_le_mul_of_nonneg_left (Rat.intCast_le_intCast.mpr hk) (Rat.le_of_lt hr)
    · cases h

/-- The values `g·M` leave nothing strictly between `floor` and the next multiple
    of `g` above it, and that one too if it is excluded. -/
theorem gap_int {g M floor ceil except at_ : Int} (hg : 0 < g)
    (hl : ceil ≤ (if 0 ≤ except ∧ floor - floor % g + g = at_ then floor - floor % g + g + g
      else floor - floor % g + g))
    (hne : 0 ≤ except → g * M ≠ at_) : g * M ≤ floor ∨ ceil ≤ g * M := by
  have hd := Int.mul_ediv_add_emod floor g
  have h0 := Int.emod_nonneg floor (show g ≠ 0 by omega)
  have h1 := Int.emod_lt_of_pos floor hg
  generalize floor / g = t at *
  generalize floor % g = s at *
  subst hd
  by_cases hc : g * M ≤ g * t + s
  · exact Or.inl hc
  · right
    have ht : t < M := by
      apply Classical.byContradiction; intro hn
      have := Int.mul_le_mul_of_nonneg_left (show M ≤ t by omega) (Int.le_of_lt hg)
      omega
    have h2 := Int.mul_le_mul_of_nonneg_left (show t + 1 ≤ M by omega) (Int.le_of_lt hg)
    rw [Int.mul_add, Int.mul_one] at h2
    split at hl
    · rename_i hc'
      have h3 : M ≠ t + 1 := by
        intro e; apply hne hc'.1; rw [e, Int.mul_add, Int.mul_one]; omega
      have h4 := Int.mul_le_mul_of_nonneg_left (show t + 2 ≤ M by omega) (Int.le_of_lt hg)
      rw [Int.mul_add] at h4
      omega
    · omega

theorem gap_sound {env : Env} {ρ : Nat → R} (hρ : env.Sound ρ) {f : Form} {floor ceil except at_ : Int}
    (h : gap env f floor ceil except at_ = true)
    (hne : 0 ≤ except → eval ρ f ≠ (at_ : R)) :
    eval ρ f ≤ (floor : R) ∨ (ceil : R) ≤ eval ρ f := by
  unfold gap at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨hg, hi⟩, hl⟩ := h
  generalize gcdInts f = g at *
  have hg0 : ((g : Int) : Rat) ≠ 0 := by
    rw [Ne, ← Rat.intCast_zero, Rat.intCast_inj]; omega
  obtain ⟨M, hM⟩ := eval_integral env ρ hρ _ hi
  have hev : eval ρ f = (((g : Int) * M : Int) : R) := by
    rw [eval_divide ρ (k := ((g : Int) : Rat)) hg0, hM, rat_intCast, Ring.intCast_mul]
  have := gap_int (g := g) (M := M) (floor := floor) (ceil := ceil) (except := except) (at_ := at_)
    (by omega) (by simpa [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] using hl)
    (fun he e => hne he (by rw [hev, e]))
  rw [hev]
  rcases this with h | h
  · exact Or.inl (cast_le h)
  · exact Or.inr (cast_le h)

theorem mem_union_left {a b : List Hyp} {h : Hyp} (m : h ∈ a) : h ∈ union a b :=
  List.mem_append_left _ m

theorem mem_union_right {a b : List Hyp} {h : Hyp} (m : h ∈ b) : h ∈ union a b := by
  unfold union
  by_cases ha : h ∈ a
  · exact List.mem_append_left _ ha
  · exact List.mem_append_right _ (List.mem_filter.mpr ⟨m, by simpa using ha⟩)

theorem discharge_mem {reason : Int} {h : Hyp} {o o' : List Hyp} (hd : discharge reason h o = some o')
    {k : Hyp} (m : k ∈ o) : k = h ∨ k ∈ o' := by
  unfold discharge at hd
  split at hd
  · rename_i hall
    cases hd
    have := List.all_eq_true.mp hall k m
    by_cases hr : k.reason = reason
    · left; simpa [hr] using this
    · right; exact List.mem_filter.mpr ⟨m, by simpa using hr⟩
  · cases hd

theorem combine_sound {env : Env} {ρ : Nat → R} {done : List Proved}
    (hdone : ∀ p ∈ done, Valid env ρ p) :
    ∀ {parts : List (Rat × Nat)} {p : Proved}, combine done parts = some p → Valid env ρ p
  | [], p, h => by
    cases h; intro _; right; exact ⟨by simp [eval, rat_zero], Rat.le_refl⟩
  | (k, i) :: rest, p, h => by
    unfold combine at h
    split at h
    · rename_i p0 o q o' hp hq
      split at h
      · rename_i hk
        cases h
        have vp := hdone _ (List.mem_of_getElem? hp)
        have vq := combine_sound hdone hq
        intro hyps
        have h1 := holds_scale hk (vp (fun h m => hyps h (mem_union_left m)))
        have h2 := vq (fun h m => hyps h (mem_union_right m))
        exact holds_add h1 h2
      · cases h
    · cases h

theorem side_upper {env : Env} {ρ : Nat → R} {r : Int} {x : Nat} {c : Int} {s : Bool}
    (h : eval ρ (env.form x) < (c : R) ∨ (s = false ∧ eval ρ (env.form x) = (c : R))) :
    (side env ⟨r, x, c, s, true⟩).holds ρ := by
  show Ineq.holds ρ ⟨env.form x, (c : Rat), if s then -1 else 0⟩
  unfold Ineq.holds
  rw [rat_intCast]
  rcases h with h | ⟨rfl, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨h, Rat.le_refl⟩

theorem side_lower {env : Env} {ρ : Nat → R} {r : Int} {x : Nat} {c : Int} {s : Bool}
    (h : (c : R) < eval ρ (env.form x) ∨ (s = false ∧ eval ρ (env.form x) = (c : R))) :
    (side env ⟨r, x, c, s, false⟩).holds ρ := by
  show Ineq.holds ρ ⟨neg (env.form x), -(c : Rat), -(if s then 1 else 0)⟩
  unfold Ineq.holds
  rw [eval_neg, rat_neg, rat_intCast]
  rcases h with h | ⟨rfl, h⟩
  · exact Or.inl (by grind)
  · exact Or.inr ⟨by rw [h], show (0 : Rat) ≤ -(if false = true then 1 else 0) by decide⟩

theorem split_sides {env : Env} {ρ : Nat → R} (hρ : env.Sound ρ) {reason : Int} {x : Nat}
    {floor ceil except at_ : Int} {strict : Bool}
    (hex : (except < 0 || env.distinct except x at_) = true)
    (hs : (if strict then 0 ≤ except && floor == at_ && ceil == at_
      else gap env (env.form x) floor ceil except at_) = true) :
    (side env ⟨reason, x, floor, strict, true⟩).holds ρ
      ∨ (side env ⟨reason, x, ceil, strict, false⟩).holds ρ := by
  have hne : 0 ≤ except → eval ρ (env.form x) ≠ (at_ : R) := by
    intro he
    have : env.distinct except x at_ = true := by
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hex
      rcases hex with h | h
      · omega
      · exact h
    exact hρ.distinct _ _ _ he this
  cases strict
  · simp only [Bool.false_eq_true, ↓reduceIte] at hs
    rcases gap_sound hρ hs hne with h | h
    · left; apply side_upper
      by_cases e : eval ρ (env.form x) = (floor : R)
      · exact Or.inr ⟨rfl, e⟩
      · exact Or.inl (by grind)
    · right; apply side_lower
      by_cases e : eval ρ (env.form x) = (ceil : R)
      · exact Or.inr ⟨rfl, e⟩
      · exact Or.inl (by grind)
  · simp only [↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hs
    obtain ⟨⟨he, h1⟩, h2⟩ := hs
    have hn := hne he
    rw [← h1] at hn
    have h3 : ceil = floor := by omega
    rw [h3]
    by_cases hl : eval ρ (env.form x) < (floor : R)
    · exact Or.inl (side_upper (Or.inl hl))
    · exact Or.inr (side_lower (Or.inl (by grind)))

theorem node_sound {env : Env} {ρ : Nat → R} (hρ : env.Sound ρ) {done : List Proved}
    (hdone : ∀ p ∈ done, Valid env ρ p) {n : Node} {p : Proved} (h : node env done n = some p) :
    Valid env ρ p := by
  cases n with
  | hyp hy =>
    simp only [node] at h
    split at h
    · rename_i hr
      split at h
      · rename_i hok; cases h; intro _; exact hρ.hyp hy hr hok
      · cases h
    · cases h; intro hyps; exact hyps hy (List.mem_singleton_self _)
  | comb parts => simp only [node] at h; exact combine_sound hdone h
  | round i =>
    simp only [node] at h
    split at h
    · rename_i p0 o hp
      cases hq : roundIneq env p0 with
      | none => rw [hq] at h; cases h
      | some q =>
        rw [hq] at h; cases h
        intro hyps
        exact roundIneq_sound hρ hq (hdone _ (List.mem_of_getElem? hp) hyps)
    · cases h
  | split reason x floor ceil low high except at_ strict =>
    simp only [node] at h
    split at h
    · rename_i pl ol ph oh hl hh
      split at h
      · rename_i hc
        simp only [splitOk, Bool.and_eq_true] at hc
        obtain ⟨⟨⟨cl, ch⟩, hex⟩, hs⟩ := hc
        split at h
        · rename_i ol' oh' dl dh
          cases h
          intro hyps
          exfalso
          rcases split_sides (reason := reason) hρ hex hs with hside | hside
          · apply contradiction_false (ρ := ρ) cl
            apply hdone _ (List.mem_of_getElem? hl)
            intro k m
            rcases discharge_mem dl m with e | m'
            · rw [e]; exact hside
            · exact hyps k (mem_union_left m')
          · apply contradiction_false (ρ := ρ) ch
            apply hdone _ (List.mem_of_getElem? hh)
            intro k m
            rcases discharge_mem dh m with e | m'
            · rw [e]; exact hside
            · exact hyps k (mem_union_right m')
        · cases h
      · cases h
    · cases h

theorem check_sound {env : Env} {ρ : Nat → R} (hρ : env.Sound ρ) :
    ∀ {nodes : List Node} {done out : List Proved}, (∀ p ∈ done, Valid env ρ p) →
      check env done nodes = some out → ∀ p ∈ out, Valid env ρ p
  | [], done, out, hdone, h => by cases h; exact hdone
  | n :: rest, done, out, hdone, h => by
    unfold check at h
    split at h
    · rename_i p hp
      apply check_sound hρ _ h
      intro q m
      rcases List.mem_append.mp m with m | m
      · exact hdone q m
      · rw [List.mem_singleton.mp m]; exact node_sound hρ hdone hp
    · cases h

/-- A certificate the checker accepts refutes the bounds it may assume: no
    valuation satisfies them, with the integer unknowns at integers and the
    disequalities it may use. -/
theorem accepts_sound {env : Env} {nodes : List Node} (h : accepts env nodes = true)
    (ρ : Nat → R) (hρ : env.Sound ρ) : False := by
  unfold accepts at h
  split at h
  · rename_i out hout
    split at h
    · rename_i p o hl
      simp only [Bool.and_eq_true, List.isEmpty_iff] at h
      obtain ⟨hc, rfl⟩ := h
      have v := check_sound hρ (by simp) hout _ (List.mem_of_getLast? hl)
      exact contradiction_false hc (v (by simp))
    · cases h
  · cases h

end Vik.Lia
