import Vik.Lower.BitOps

/-!
# `let` and definitions

The lowering inlines them: a `let` and a use of its variable take the lowered
node of the bound term, and a use of a definition (`define-fun`) that of an
instance of its body, which the trace gives and `SDef.instOk` checks.
`defOk_sound` proves that the lowered node takes the value of the surface one,
in a model where the definitions hold.
-/

set_option linter.unusedSectionVars false

namespace Vik.Lower

open Lean.Grind Vik.Real Vik.Low Vik.Surf

variable {R U : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R]
  [OrderedRing R] [IsCharP R 0]

attribute [local instance low] Lean.Grind.Ring.intCast

/-- The arguments of a use of a definition are in the domains of its
    parameters' sorts. -/
theorem def_args_dom {M : Surf.Model R U} {decls sortOf : List Nat} {f : Nat → Val R U} :
    ∀ (ps args : List Nat), ps.length = args.length →
      (∀ q ∈ ps.zip args, decls.getD q.1 0 = sortOf.getD q.2 0) →
      (∀ a ∈ args, M.dom (sortOf[a]?.getD 0) (f a)) →
      Forall2 M.dom (ps.map fun p => decls.getD p 0) (args.map f)
  | [], [], _, _, _ => trivial
  | p :: ps, a :: args, hl, hs, hd => by
    refine ⟨?_, def_args_dom ps args (by simpa using hl) (fun q m => hs q (by simp [m]))
      (fun b m => hd b (by simp [m]))⟩
    have e := hs (p, a) (by simp)
    simp only at e
    show M.dom (decls.getD p 0) (f a)
    rw [e, List.getD_eq_getElem?_getD]
    exact hd a (by simp)
  | [], _ :: _, hl, _, _ => by simp at hl
  | _ :: _, [], hl, _, _ => by simp at hl

section
variable {SP : SProblem} {P : Problem} {tr : Trace} {Ms : Surf.Model R U}
  (hM : Ms.Sound SP.sig) (hw : Surf.wellFormed SP.nodes = true) (ht : Surf.typed SP.sig SP.nodes SP.sortOf = true)

set_option quotPrecheck false in
local notation "ρ" => Low.val (lowModel SP P tr Ms).toInterp P.nodes
set_option quotPrecheck false in
local notation "vs" => Surf.val Ms.toInterp SP.nodes

include hM hw ht in
/-- A `let`, a use of its variable, or a use of a definition, that
    `Trace.defOk` accepts, takes the value of its lowered node. -/
theorem defOk_sound (hD : ∀ d ∈ SP.defs, d.Holds SP.sig Ms) {i : Nat} {n : SNode}
    (hn : SP.nodes[i]? = some n) (hb : tr.defOk SP i = true) (ih : ∀ c < i, ρ (tr.at c) = enc (vs c)) :
    ρ (tr.at i) = enc (vs i) := by
  have hv := Surf.val_node (I := Ms.toInterp) hw hn
  have hch := children_lt hw hn
  have hil := lt_of_get hn
  -- a use of definition `c` with the arguments `args`
  have key : ∀ (c : Nat) (args : List Nat) (isApp : Bool), (∀ a ∈ args, a < i) →
      vs i = (if isApp then Ms.app (Ms.const c) (args.map vs) else Ms.const c) →
      (match SP.defs.find? (·.sym == c), tr.insts.lookup i with
        | some d, some ms =>
          isApp == !d.params.isEmpty && d.params.length == args.length && Surf.wellFormed d.nodes &&
            d.root < d.nodes.length &&
            (d.params.zip args).all (fun q => SP.sig.decls.getD q.1 0 == SP.sortOf.getD q.2 0) &&
            d.instOk SP.nodes args ms && ms.getD d.root 0 < i && tr.at i == tr.at (ms.getD d.root 0)
        | _, _ => false) = true →
      ρ (tr.at i) = enc (vs i) := by
    intro c args isApp hargs hvi hb
    split at hb
    · rename_i d ms hd hms
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at hb
      obtain ⟨⟨⟨⟨⟨⟨⟨hap, hlen⟩, hwd⟩, hroot⟩, hsorts⟩, hinst⟩, hr⟩, hl⟩ := hb
      have hdm := List.mem_of_find?_eq_some hd
      have hsym : d.sym = c := beq_iff_eq.mp (List.find?_some (p := fun x : SDef => x.sym == c) hd)
      have hfa := def_args_dom (M := Ms) (f := vs) d.params args hlen
        (fun q m => by simpa using hsorts q m) (fun a m => Surf.val_dom hM hw ht a (by have := hargs a m; omega))
      have hlaw := hD d hdm _ hfa
      have hiv := inst_val Ms.toInterp hw hwd hinst d.root hroot
      rw [hl, ih _ hr, hiv, ← hlaw, hsym, hvi]
      cases isApp with
      | false =>
        have : d.params = [] := by
          cases h : d.params with
          | nil => rfl
          | cons _ _ => rw [h] at hap; simp at hap
        simp only [this, if_true]; rfl
      | true =>
        have : d.params ≠ [] := by
          intro h; rw [h] at hap; simp at hap
        simp only [this, if_false]; rfl
    · cases hb
  unfold Trace.defOk at hb
  try simp only [Tab.at_eq] at hb
  rw [hn] at hb
  cases n with
  | letIn bs b =>
    simp only [beq_iff_eq] at hb
    rw [hb, ih b (hch b (by simp [SNode.children])), hv]; rfl
  | bound d =>
    simp only [beq_iff_eq] at hb
    rw [hb, ih d (hch d (by simp [SNode.children])), hv]; rfl
  | const c =>
    simp only [SProblem.callOf] at hb
    exact key c [] false (by simp) (by rw [hv]; rfl) hb
  | app f args =>
    cases hfn : SP.nodes[f]? with
    | none => simp [SProblem.callOf, hfn] at hb
    | some m =>
      cases m with
      | const c =>
        simp only [Tab.at_eq, SProblem.callOf, hfn] at hb
        refine key c args true (fun a m => hch a (by simp [SNode.children, m])) ?_ hb
        rw [hv]
        have hfv := Surf.val_node (I := Ms.toInterp) hw hfn
        simp only [Surf.evalNode] at hfv
        simp only [Surf.evalNode, if_true]
        change Ms.app (vs f) (args.map vs) = _
        rw [hfv]
      | _ => simp [SProblem.callOf, hfn] at hb
  | _ => simp [SProblem.callOf] at hb

end

end Vik.Lower
