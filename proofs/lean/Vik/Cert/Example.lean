import Vik.Cert.Extend

/-!
# An example

`x ≤ 0` and `1 ≤ x`, both asserted under the level `s`: the proof derives `¬s`
from the two input clauses and a cutting-planes lemma, and the kernel checks it.
-/

namespace Vik.Low.Example

open Vik.Clausal

/-- Sorts `Bool` and `Int`; one integer constant `x`. -/
def problem : Problem where
  sig := ⟨[.bool, .int], [1]⟩
  nodes := [.tt, .const 0, .num 0, .num 1, .le 1 2, .le 3 1, .bterm 0, .ff, .bterm 7]
  sortOf := [0, 1, 1, 1, 0, 0, 0, 0, 0]
  inputs := []
  datatypes := []
  stores := []
  bvIndex := []

/-- Variables: `0` is `true`, `1` is `x ≤ 0`, `2` is `1 ≤ x`, `3` is the level. -/
def answer : Answer where
  meaning := [some 0, some 4, some 5, none]
  trueLit := ⟨0, true⟩
  levels := [(3, [4, 5])]
  assumed := [3]
  ufAtoms := []
  trueClass := 6
  falseClass := 8
  ufCtors := []
  ufTesters := []
  -- `x ≤ 0` and `-x ≤ -1`
  liaAtoms := [none, some (.bound 0 0 false), some (.bound 1 (-1) false)]
  liaForms := [[(1, 1)], [(1, -1)]]
  steps := [
    .input [⟨3, false⟩, ⟨1, true⟩],
    .input [⟨3, false⟩, ⟨2, true⟩],
    .lemma [⟨1, false⟩, ⟨2, false⟩],
    .derived [⟨3, false⟩] [0, 1, 2]]
  justs := [.input (.assertion 4), .input (.assertion 5),
    .lia [.hyp ⟨2, 0, 0, false, true⟩, .hyp ⟨4, 1, -1, false, true⟩, .comb [(1, 0), (1, 1)]],
    .derived]
  conclusion := 3
  exts := []
  witnesses := []


theorem accepted : problem.accepts answer = true := by decide +kernel

/-- No model satisfies both assertions under the level. -/
theorem no_model {R U : Type} [Lean.Grind.Field R] [LE R] [LT R] [Std.IsLinearOrder R]
    [Std.LawfulOrderLT R] [Lean.Grind.OrderedRing R] [Lean.Grind.IsCharP R 0] (M : Model R U)
    (size : Val R U → Nat) (hL : problem.Laws M size) (h4 : holds M.toInterp problem.nodes 4)
    (h5 : holds M.toInterp problem.nodes 5) : False :=
  Problem.accepts_sound accepted M size hL (by simp [problem]) (by
    intro s hs fs hfs f hf
    simp [answer] at hs; subst hs
    simp [answer] at hfs; subst hfs
    simp at hf; rcases hf with rfl | rfl <;> assumption)
    (by intro i _ w h; simp [problem] at h)

/-! ## With an extensionality instance

The same answer, with two more functions `f` and `g` from a bit-vector index
of width 1 to integers, and the input clauses of their extensionality instance
with witness `w`: `f = g ∨ f(w) ≠ g(w)`, `0 ≤ w` and `w ≤ 1`. The proof does not
need them, but the checker accepts them: the witness is fresh, and its range is
that of the index.
-/

/-- Sorts `Bool`, `Int`, the index (sort 2, of width 1) and `index → Int`;
    constants `x`, `f`, `g` and the witness `w`. -/
def problem2 : Problem where
  sig := ⟨[.bool, .int, .int, .fn [2] 1], [1, 3, 3, 2]⟩
  nodes := [.tt, .const 0, .num 0, .num 1, .le 1 2, .le 3 1, .bterm 0, .ff, .bterm 7,
    .const 1, .const 2, .eq 9 10, .const 3, .app 9 [12], .app 10 [12], .eq 13 14, .le 2 12, .le 12 3]
  sortOf := [0, 1, 1, 1, 0, 0, 0, 0, 0, 3, 3, 0, 2, 1, 1, 0, 0, 0]
  inputs := []
  datatypes := []
  stores := []
  bvIndex := [(2, 1)]

/-- Variables `4` to `7`: `f = g`, `f(w) = g(w)`, `0 ≤ w` and `w ≤ 1`. -/
def answer2 : Answer where
  meaning := [some 0, some 4, some 5, none, some 11, some 15, some 16, some 17]
  trueLit := ⟨0, true⟩
  levels := [(3, [4, 5])]
  assumed := [3]
  ufAtoms := []
  trueClass := 6
  falseClass := 8
  ufCtors := []
  ufTesters := []
  liaAtoms := [none, some (.bound 0 0 false), some (.bound 1 (-1) false)]
  liaForms := [[(1, 1)], [(1, -1)]]
  steps := [
    .input [⟨3, false⟩, ⟨1, true⟩],
    .input [⟨3, false⟩, ⟨2, true⟩],
    .lemma [⟨1, false⟩, ⟨2, false⟩],
    .derived [⟨3, false⟩] [0, 1, 2],
    .input [⟨4, true⟩, ⟨5, false⟩],
    .input [⟨6, true⟩],
    .input [⟨7, true⟩]]
  justs := [.input (.assertion 4), .input (.assertion 5),
    .lia [.hyp ⟨2, 0, 0, false, true⟩, .hyp ⟨4, 1, -1, false, true⟩, .comb [(1, 0), (1, 1)]],
    .derived, .input (.extensionality 0), .input (.witnessRange 16), .input (.witnessRange 17)]
  conclusion := 3
  exts := [(11, 15, [3])]
  witnesses := [3]

theorem accepted2 : problem2.accepts answer2 = true := by decide +kernel

/-- No model satisfies both assertions under the level, with the index in its range. -/
theorem no_model2 {R U : Type} [Lean.Grind.Field R] [LE R] [LT R] [Std.IsLinearOrder R]
    [Std.LawfulOrderLT R] [Lean.Grind.OrderedRing R] [Lean.Grind.IsCharP R 0] (M : Model R U)
    (size : Val R U → Nat) (hL : problem2.Laws M size) (h4 : holds M.toInterp problem2.nodes 4)
    (h5 : holds M.toInterp problem2.nodes 5)
    (hr : ∀ i < problem2.nodes.length, inRange problem2.bvIndex (problem2.sort i) (val M.toInterp problem2.nodes i)) :
    False :=
  Problem.accepts_sound accepted2 M size hL (fun f hf => by cases hf) (by
    intro s hs fs hfs f hf
    cases hs with
    | head =>
      have e : some [4, 5] = some fs := hfs
      cases e
      cases hf with
      | head => exact h4
      | tail _ hf =>
        cases hf with
        | head => exact h5
        | tail _ hf => cases hf
    | tail _ h => cases h) hr

end Vik.Low.Example
