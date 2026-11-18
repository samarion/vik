import Vik.Lower.Unsat

/-!
# An example, from SMT-LIB

```
(declare-const x Int)
(assert (<= x 0))
(assert (< 0 x))
```

lowers to `x ≤ 0` and `1 ≤ x` (the strict bound on integers becomes `0 + 1 ≤ x`,
and the constant folds). The kernel checks the trace and a cutting-planes
proof of the lowered problem, so the script has no model.
-/

namespace Vik.Lower.Example

open Vik.Low Vik.Surf Vik.Clausal

/-- The script: sorts `Bool` and `Int`, the constant `x`, its two assertions. -/
def script : SProblem where
  sig := ⟨[.bool, .int], [1]⟩
  nodes := [.const 0, .num 0, .le [0, 1], .lt [1, 0]]
  sortOf := [1, 1, 0, 0]
  asserts := [2, 3]
  datatypes := []

/-- Its lowering, as Vik solves it. -/
def problem : Problem where
  sig := ⟨[.bool, .int], [1]⟩
  nodes := [.tt, .const 0, .num 0, .num 1, .le 1 2, .le 3 1, .bterm 0, .ff, .bterm 7]
  sortOf := [0, 1, 1, 1, 0, 0, 0, 0, 0]
  inputs := [4, 5]
  datatypes := []
  stores := []
  bvIndex := []

def trace : Trace where
  node := [1, 2, 4, 5]
  mints := []
  inputs := [.assert 2, .assert 3]

/-- Variables: `0` is `true`, `1` is `x ≤ 0`, `2` is `1 ≤ x`. -/
def answer : Answer where
  meaning := [some 0, some 4, some 5]
  trueLit := ⟨0, true⟩
  levels := []
  assumed := []
  ufAtoms := []
  trueClass := 6
  falseClass := 8
  ufCtors := []
  ufTesters := []
  liaAtoms := [none, some (.bound 0 0 false), some (.bound 1 (-1) false)]
  liaForms := [[(1, 1)], [(1, -1)]]
  steps := [
    .input [⟨1, true⟩],
    .input [⟨2, true⟩],
    .lemma [⟨1, false⟩, ⟨2, false⟩],
    .derived [] [0, 1, 2]]
  justs := [.input (.assertion 4), .input (.assertion 5),
    .lia [.hyp ⟨2, 0, 0, false, true⟩, .hyp ⟨4, 1, -1, false, true⟩, .comb [(1, 0), (1, 1)]],
    .derived]
  conclusion := 3
  exts := []
  witnesses := []

theorem checked : trace.check script problem answer = true := by decide +kernel

theorem accepted : problem.accepts answer = true := by decide +kernel

/-- No model of the script satisfies its assertions. -/
theorem no_model {R U : Type} [Lean.Grind.Field R] [LE R] [LT R] [Std.IsLinearOrder R]
    [Std.LawfulOrderLT R] [Lean.Grind.OrderedRing R] [Lean.Grind.IsCharP R 0] (M : Surf.Model R U)
    (size : Val R U → Nat) (hL : script.Laws M size) (hfl : ∀ r : R, ∃ k : Int, Vik.Real.IsFloor r k)
    (h2 : Surf.holds M.toInterp script.nodes 2) (h3 : Surf.holds M.toInterp script.nodes 3) : False :=
  Trace.unsat checked accepted M size hL hfl (by
    intro a ha
    simp only [script, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact h2
    · exact h3)

/-! ## With a level

```
(declare-const x Int)
(assert (<= x 0))
(check-sat-assuming ((< 0 x)))
```

Vik asserts the assumption in a level of its own, under the literal `3`, and
the proof derives `¬3`. The surface script asserts both formulas: those of the
open levels and the assumptions of the check. The trace gives the reason of
each formula of the assumed level.
-/

def problem2 : Problem := { problem with inputs := [4] }

def trace2 : Trace := { trace with inputs := [.assert 2], levels := [[.assert 3]] }

/-- Variables: `0` is `true`, `1` is `x ≤ 0`, `2` is `1 ≤ x`, `3` is the level. -/
def answer2 : Answer :=
  { answer with
    meaning := [some 0, some 4, some 5, none]
    levels := [(3, [5])]
    assumed := [3]
    steps := [
      .input [⟨1, true⟩],
      .input [⟨3, false⟩, ⟨2, true⟩],
      .lemma [⟨1, false⟩, ⟨2, false⟩],
      .derived [⟨3, false⟩] [0, 1, 2]] }

theorem checked2 : trace2.check script problem2 answer2 = true := by decide +kernel

theorem accepted2 : problem2.accepts answer2 = true := by decide +kernel

/-- No model of the script satisfies the assertion and the assumption. -/
theorem no_model2 {R U : Type} [Lean.Grind.Field R] [LE R] [LT R] [Std.IsLinearOrder R]
    [Std.LawfulOrderLT R] [Lean.Grind.OrderedRing R] [Lean.Grind.IsCharP R 0] (M : Surf.Model R U)
    (size : Val R U → Nat) (hL : script.Laws M size) (hfl : ∀ r : R, ∃ k : Int, Vik.Real.IsFloor r k)
    (h2 : Surf.holds M.toInterp script.nodes 2) (h3 : Surf.holds M.toInterp script.nodes 3) : False :=
  Trace.unsat checked2 accepted2 M size hL hfl (by
    intro a ha
    simp only [script, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact h2
    · exact h3)

/-! ## With `let` and `define-fun`

```
(declare-const x Int)
(define-fun pos ((y Int)) Bool (< 0 y))
(assert (let ((z x)) (<= z 0)))
(assert (pos x))
```

The surface nodes keep the `let`, the use of `z`, and the call of `pos`;
node 6 is the instance of the body of `pos` that the lowering inlines, which
the checker matches against the definition. The lowering is that of the first
example.
-/

def script3 : SProblem where
  sig := ⟨[.bool, .int, .fn [1] 0], [1, 2, 1]⟩
  nodes := [.const 0, .num 0, .bound 0, .le [2, 1], .letIn [0] 3, .const 1, .lt [1, 0], .app 5 [0]]
  sortOf := [1, 1, 1, 0, 0, 2, 0, 0]
  asserts := [4, 7]
  datatypes := []
  defs := [⟨1, [2], [.num 0, .const 2, .lt [0, 1]], 2⟩]

def problem3 : Problem :=
  { problem with
    sig := ⟨[.bool, .int, .fn [1] 0], [1, 2, 1]⟩
    nodes := problem.nodes ++ [.const 1, .const 2]
    sortOf := problem.sortOf ++ [2, 1] }

def trace3 : Trace where
  node := [1, 2, 1, 4, 4, 9, 5, 5]
  mints := []
  inputs := [.assert 4, .assert 7]
  insts := [(7, [1, 0, 6])]

theorem checked3 : trace3.check script3 problem3 answer = true := by decide +kernel

theorem accepted3 : problem3.accepts answer = true := by decide +kernel

/-- No model of the script, `pos` defined as its body, satisfies its
    assertions. -/
theorem no_model3 {R U : Type} [Lean.Grind.Field R] [LE R] [LT R] [Std.IsLinearOrder R]
    [Std.LawfulOrderLT R] [Lean.Grind.OrderedRing R] [Lean.Grind.IsCharP R 0] (M : Surf.Model R U)
    (size : Val R U → Nat) (hL : script3.Laws M size) (hfl : ∀ r : R, ∃ k : Int, Vik.Real.IsFloor r k)
    (h4 : Surf.holds M.toInterp script3.nodes 4) (h7 : Surf.holds M.toInterp script3.nodes 7) : False :=
  Trace.unsat checked3 accepted3 M size hL hfl (by
    intro a ha
    simp only [script3, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact h4
    · exact h7)

end Vik.Lower.Example
