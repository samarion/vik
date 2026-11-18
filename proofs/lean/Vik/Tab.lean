/-!
# Tables with logarithmic lookups

The checkers run in the kernel (`decide +kernel`), which looks up the `i`-th
element of a list in `i` steps, each slow. A `Tab` is a binary tree of the
list's elements, element `0` at the root and the others split by parity, so a
lookup takes about `log₂ i` steps. The kernel shares a tree built once from a
list across lookups, as it caches the values of closed terms.

`Tab.get_of` says a lookup in the tree is one in the list, so a checker can
look up with `Tab.at` and its proof reason about `l[i]?`.
-/

namespace Vik

inductive Tab (α : Type) where
  | leaf
  | node (x : α) (l r : Tab α)

/-- The elements at even positions. -/
def evens {α : Type} : List α → List α
  | [] => []
  | [x] => [x]
  | x :: _ :: xs => x :: evens xs

/-- The elements at odd positions. -/
def odds {α : Type} : List α → List α
  | [] => []
  | _ :: xs => evens xs

/-- The tree of a list of at most `f` elements. -/
def Tab.ofF {α : Type} : Nat → List α → Tab α
  | 0, _ => .leaf
  | _, [] => .leaf
  | f + 1, x :: xs => .node x (Tab.ofF f (evens xs)) (Tab.ofF f (odds xs))

def Tab.of {α : Type} (l : List α) : Tab α := Tab.ofF l.length l

def Tab.get {α : Type} : Tab α → Nat → Option α
  | .leaf, _ => none
  | .node x l r, n =>
    match n with
    | 0 => some x
    | n + 1 => if n % 2 == 0 then l.get (n / 2) else r.get (n / 2)

/-- `l[i]?`, in about `log₂ i` kernel steps once the tree of `l` is built. -/
def Tab.at {α : Type} (l : List α) (i : Nat) : Option α := (Tab.of l).get i

theorem evens_get {α : Type} : ∀ (l : List α) (k : Nat), (evens l)[k]? = l[2 * k]?
  | [], _ => rfl
  | [x], k => by
    cases k with
    | zero => rfl
    | succ k =>
      simp only [evens, List.getElem?_cons_succ, List.getElem?_nil, show 2 * (k + 1) = 2 * k + 1 + 1 by omega]
  | x :: y :: xs, k => by
    cases k with
    | zero => rfl
    | succ k =>
      simp only [evens, List.getElem?_cons_succ]
      rw [evens_get xs k, show 2 * (k + 1) = 2 * k + 1 + 1 by omega]
      simp

theorem odds_get {α : Type} (l : List α) (k : Nat) : (odds l)[k]? = l[2 * k + 1]? := by
  cases l with
  | nil => rfl
  | cons x xs => simp [odds, evens_get]

theorem evens_length {α : Type} : ∀ (l : List α), (evens l).length ≤ l.length
  | [] => Nat.le_refl _
  | [_] => Nat.le_refl _
  | _ :: _ :: xs => by simp only [evens, List.length_cons]; have := evens_length xs; omega

theorem odds_length {α : Type} (l : List α) : (odds l).length + 1 ≤ l.length + 1 := by
  cases l with
  | nil => simp [odds]
  | cons x xs => simp only [odds, List.length_cons]; have := evens_length xs; omega

theorem Tab.get_ofF {α : Type} : ∀ (f : Nat) (l : List α), l.length ≤ f → ∀ i, (Tab.ofF f l).get i = l[i]?
  | 0, l, h, i => by
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; cases i <;> rfl
  | f + 1, [], _, i => by cases i <;> rfl
  | f + 1, x :: xs, h, i => by
    simp only [List.length_cons] at h
    cases i with
    | zero => rfl
    | succ n =>
      simp only [Tab.ofF, Tab.get, List.getElem?_cons_succ]
      split
      · rename_i hn
        rw [Tab.get_ofF f (evens xs) (Nat.le_trans (evens_length xs) (by omega)), evens_get]
        congr 1
        have := Nat.mod_two_eq_zero_or_one n
        simp only [beq_iff_eq] at hn
        omega
      · rename_i hn
        rw [Tab.get_ofF f (odds xs) (by have := odds_length xs; omega), odds_get]
        congr 1
        simp only [beq_iff_eq] at hn
        omega

@[simp] theorem Tab.at_eq {α : Type} (l : List α) (i : Nat) : Tab.at l i = l[i]? :=
  Tab.get_ofF _ l (Nat.le_refl _) i

/-- Compiled code, which does not share the tree across lookups as the kernel
    does, looks up in the list. -/
def Tab.atList {α : Type} (l : List α) (i : Nat) : Option α := l[i]?

@[csimp] theorem Tab.at_eq_atList : @Tab.at = @Tab.atList := by
  funext α l i; exact Tab.at_eq l i

/-- The tree with element `i` set to `x`, for `i` at most the number of
    elements: a table grows by setting its next element. -/
def Tab.set {α : Type} : Tab α → Nat → α → Tab α
  | .leaf, _, x => .node x .leaf .leaf
  | .node _ l r, 0, x => .node x l r
  | .node y l r, n + 1, x => if n % 2 == 0 then .node y (l.set (n / 2) x) r else .node y l (r.set (n / 2) x)

/-- `t` holds `f 0`, …, `f (n - 1)`. -/
def Tab.Holds {α : Type} (t : Tab α) (f : Nat → α) (n : Nat) : Prop :=
  ∀ j, t.get j = if j < n then some (f j) else none

theorem Tab.holds_leaf {α : Type} (f : Nat → α) : Tab.leaf.Holds f 0 := fun _ => rfl

theorem Tab.holds_set {α : Type} : ∀ (t : Tab α) (f : Nat → α) (n : Nat) (x : α), t.Holds f n →
    (t.set n x).Holds (fun j => if j = n then x else f j) (n + 1)
  | .leaf, f, n, x, h => by
    have h0 := h 0
    simp only [Tab.get] at h0
    have hn : n = 0 := by
      cases n with
      | zero => rfl
      | succ n => simp at h0
    subst hn
    intro j
    cases j with
    | zero => rfl
    | succ j => simp [Tab.set, Tab.get]
  | .node y l r, f, n, x, h => by
    have h0 := h 0
    simp only [Tab.get] at h0
    have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with e | e
      · subst e; simp at h0
      · exact e
    have hy : y = f 0 := by simp [hn] at h0; exact h0
    have hl : l.Holds (fun k => f (2 * k + 1)) (n / 2) := by
      intro k
      have := h (2 * k + 1)
      simp only [Tab.get, show (2 * k) % 2 = 0 by omega, show 2 * k / 2 = k by omega, beq_self_eq_true, ↓reduceIte] at this
      rw [this]
      by_cases hk : k < n / 2
      · simp [hk, show 2 * k + 1 < n by omega]
      · simp [hk, show ¬ 2 * k + 1 < n by omega]
    have hr : r.Holds (fun k => f (2 * k + 2)) ((n - 1) / 2) := by
      intro k
      have := h (2 * k + 1 + 1)
      simp only [Tab.get, show (2 * k + 1) % 2 = 1 by omega, show (2 * k + 1) / 2 = k by omega] at this
      simp only [show ((1 : Nat) == 0) = false by rfl, Bool.false_eq_true, ↓reduceIte] at this
      rw [this]
      by_cases hk : k < (n - 1) / 2
      · simp [hk, show 2 * k + 1 + 1 < n by omega]
      · simp [hk, show ¬ 2 * k + 1 + 1 < n by omega]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    intro j
    simp only [Tab.set]
    split
    · rename_i hm
      have hm' : m % 2 = 0 := by simpa using hm
      have ih := Tab.holds_set l _ _ x (show l.Holds (fun k => f (2 * k + 1)) (m / 2) by
        rw [show m / 2 = (m + 1) / 2 by omega]; exact hl)
      cases j with
      | zero => simp [Tab.get, hy]
      | succ j =>
        simp only [Tab.get]
        split
        · rename_i hj
          have hj' : j % 2 = 0 := by simpa using hj
          rw [ih (j / 2)]
          by_cases e : j = m
          · subst e; simp
          · have : j / 2 ≠ m / 2 := by omega
            by_cases hk : j / 2 < m / 2 + 1
            · simp [this, hk, e, show j + 1 < m + 1 + 1 by omega, show 2 * (j / 2) + 1 = j + 1 by omega]
            · simp [this, hk, e, show ¬ j + 1 < m + 1 + 1 by omega]
        · rename_i hj
          have hj' : j % 2 = 1 := by have := Nat.mod_two_eq_zero_or_one j; simp at hj; omega
          rw [hr (j / 2)]
          have e : j ≠ m := by omega
          by_cases hk : j / 2 < (m + 1 - 1) / 2
          · simp [hk, e, show j + 1 < m + 1 + 1 by omega, show 2 * (j / 2) + 2 = j + 1 by omega] <;> omega
          · simp [hk, e, show ¬ j + 1 < m + 1 + 1 by omega] <;> omega
    · rename_i hm
      have hm' : m % 2 = 1 := by have := Nat.mod_two_eq_zero_or_one m; simp at hm; omega
      have ih := Tab.holds_set r _ _ x (show r.Holds (fun k => f (2 * k + 2)) (m / 2) by
        rw [show m / 2 = (m + 1 - 1) / 2 by omega]; exact hr)
      cases j with
      | zero => simp [Tab.get, hy]
      | succ j =>
        simp only [Tab.get]
        split
        · rename_i hj
          have hj' : j % 2 = 0 := by simpa using hj
          rw [hl (j / 2)]
          have e : j ≠ m := by omega
          by_cases hk : j / 2 < (m + 1) / 2
          · simp [hk, e, show j + 1 < m + 1 + 1 by omega, show 2 * (j / 2) + 1 = j + 1 by omega]
          · simp [hk, e, show ¬ j + 1 < m + 1 + 1 by omega]
        · rename_i hj
          have hj' : j % 2 = 1 := by have := Nat.mod_two_eq_zero_or_one j; simp at hj; omega
          rw [ih (j / 2)]
          by_cases e : j = m
          · subst e; simp
          · have : j / 2 ≠ m / 2 := by omega
            by_cases hk : j / 2 < m / 2 + 1
            · simp [this, hk, e, show j + 1 < m + 1 + 1 by omega, show 2 * (j / 2) + 2 = j + 1 by omega]
            · simp [this, hk, e, show ¬ j + 1 < m + 1 + 1 by omega]

theorem Tab.Holds.congr {α : Type} {t : Tab α} {f g : Nat → α} {n : Nat} (h : t.Holds f n)
    (e : ∀ j < n, f j = g j) : t.Holds g n := by
  intro j
  rw [h j]
  split
  · rename_i hj; rw [e j hj]
  · rfl

end Vik
