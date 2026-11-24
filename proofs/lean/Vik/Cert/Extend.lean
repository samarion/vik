import Vik.Cert.Proof

/-!
# Extending a model with witnesses

`accepts_sound_of_witnesses` (in `Proof.lean`) assumes a model whose
witnesses already take the right values: the extensionality instances and the
ranges of the witnesses hold. This file builds such a model from any model of
the problem, and so proves the soundness of the checker, `Problem.accepts_sound`.

The witnesses take values one instance after the other, in the order of the
answer. First every integer witness takes `0`, which is in the range of any
bit-vector index. Then the witnesses of instance `k` take values where the two
functions of the instance differ, if they differ: extensionality gives such
values, in range for an index of bit-vectors. The functions of instance `k`
depend on no witness of instance `k` or later, so their values are already
final; and the later instances change no witness of instance `k`. The inputs,
the levels and the symbols of datatypes and stores depend on no witness at
all, so the new model still satisfies them.
-/

set_option linter.unusedSectionVars false

namespace Vik.Low

open Lean.Grind Vik.Real Vik.Clausal

variable {R U : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R]
  [OrderedRing R] [IsCharP R 0]

attribute [local instance low] Lean.Grind.Ring.intCast

/-! ## Setting the witnesses -/

/-- The symbols `ws` take the values `xs`; the others keep theirs. -/
def setWits (c : Nat → Val R U) : List Nat → List (Val R U) → Nat → Val R U
  | w :: ws, x :: xs, n => if n = w then x else setWits c ws xs n
  | _, _, n => c n

theorem setWits_not {c : Nat → Val R U} {n : Nat} :
    ∀ {ws : List Nat} {xs : List (Val R U)}, n ∉ ws → setWits c ws xs n = c n
  | [], _, _ => by simp [setWits]
  | _ :: _, [], _ => by simp [setWits]
  | w :: ws, x :: xs, h => by
    have h1 : n ≠ w := fun e => h (List.mem_cons.mpr (Or.inl e))
    have h2 : n ∉ ws := fun m => h (List.mem_cons_of_mem _ m)
    simp only [setWits, if_neg h1]
    exact setWits_not h2

theorem setWits_map {c : Nat → Val R U} :
    ∀ {ws : List Nat} {xs : List (Val R U)}, nodupB ws = true → ws.length = xs.length →
      ws.map (setWits c ws xs) = xs
  | [], [], _, _ => rfl
  | w :: ws, x :: xs, h, hl => by
    simp only [nodupB, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_any_beq, List.any_eq_false,
      beq_iff_eq] at h
    simp only [List.map_cons, List.cons.injEq]
    refine ⟨by simp [setWits], ?_⟩
    rw [List.map_congr_left (g := setWits c ws xs) (fun n m => by
      simp only [setWits]; rw [if_neg (fun e => h.1 n m (e.symm))])]
    exact setWits_map h.2 (by simpa using hl)

theorem setWits_mem {c : Nat → Val R U} {Q : Nat → Val R U → Prop} (d : Nat → Nat) {n : Nat} :
    ∀ {ws : List Nat} {xs : List (Val R U)}, Forall2 Q (ws.map d) xs → n ∈ ws → Q (d n) (setWits c ws xs n)
  | w :: ws, x :: xs, ⟨hq, hf⟩, m => by
    simp only [setWits]
    split
    · rename_i e; subst e; exact hq
    · rename_i e
      exact setWits_mem d hf (by simpa [e] using m)

theorem forall2_length {α β : Type} {r : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, Forall2 r l l' → l.length = l'.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, ⟨_, h⟩ => by simp [forall2_length h]

/-! ## The facts of the checker of witnesses -/

section
variable {P : Problem} {A : Answer} (hA : Accepted P A)
include hA

theorem wits_info :
    (∀ p ∈ P.bvIndex, P.sig.is p.1 .int = true) ∧
    (∀ n ∈ P.stores, A.rank n = 0) ∧ (∀ n ∈ P.dtSyms, A.rank n = 0) ∧
    (∀ f ∈ P.inputs, depthOf (depths A.rank P.nodes) f = 0) ∧
    (∀ l ∈ A.levels, ∀ f ∈ l.2, depthOf (depths A.rank P.nodes) f = 0) ∧
    (∀ i < P.nodes.length, depthOf (depths A.rank P.nodes) i = 0 ∨ (P.bvIndex.lookup (P.sort i)).isNone ∨
      (∃ n, P.nodes[i]? = some (.const n) ∧ n ∈ A.witnesses) ∨ ∃ f args, P.nodes[i]? = some (.app f args)) ∧
    (∀ k eq eqw ws, A.exts[k]? = some (eq, eqw, ws) → nodupB ws = true ∧ (∀ n ∈ ws, A.rank n = k + 2) ∧
      ∃ f g F G, P.nodes[eq]? = some (.eq f g) ∧ P.nodes[eqw]? = some (.eq F G) ∧
        depthOf (depths A.rank P.nodes) f < k + 2 ∧ depthOf (depths A.rank P.nodes) g < k + 2 ∧
        chainRev P.nodes f F ws.reverse = true ∧ chainRev P.nodes g G ws.reverse = true ∧
        chainExact P.sig P.nodes P.sortOf F ws.reverse = true) := by
  have h := hA.wits
  unfold Problem.witnessesOk at h
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, List.mem_range, Tab.at_eq, Problem.node_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  refine ⟨h1, h2, h3, h4, h5, fun i hi => ?_, fun k eq eqw ws hk => ?_⟩
  · have := h6 i hi
    simp only [Bool.or_eq_true, beq_iff_eq] at this
    rcases this with (h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · split at h
      · rename_i n hn
        exact Or.inr (Or.inr (Or.inl ⟨n, hn, List.contains_iff_mem.mp h⟩))
      · rename_i f args hn
        exact Or.inr (Or.inr (Or.inr ⟨f, args, hn⟩))
      · cases h
  · have hkl : k < A.exts.length := by
      rcases Nat.lt_or_ge k A.exts.length with h' | h'
      · exact h'
      · rw [List.getElem?_eq_none h'] at hk; cases hk
    have := h7 k hkl
    rw [hk] at this
    simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at this
    obtain ⟨⟨hnd, hr⟩, h⟩ := this
    refine ⟨hnd, hr, ?_⟩
    split at h
    · rename_i f g F G he hew
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
      exact ⟨f, g, F, G, he, hew, h1, h2, h3, h4, h5⟩
    · cases h

end

theorem rank_zero {A : Answer} {n : Nat} (h : A.rank n = 0) : n ∉ A.witnesses := by
  unfold Answer.rank rankOf at h
  split at h
  · omega
  · split at h
    · omega
    · rename_i hc; simpa using hc

/-! ## The model with witnesses -/

section
variable {P : Problem} {A : Answer} (hA : Accepted P A) {M : Model R U} {size : Val R U → Nat}
  (hL : P.Laws M size)

/-- `M` with the symbols' values `c`. -/
def Model.withConst (M : Model R U) (c : Nat → Val R U) : Model R U :=
  { const := c, app := M.app, dom := M.dom }

/-- The integer witnesses take `0`. -/
def startConst (P : Problem) (A : Answer) (M : Model R U) (n : Nat) : Val R U :=
  if A.witnesses.contains n && P.sig.is (P.sig.declOf n) .int then .num 0 else M.const n

open Classical in
/-- The witnesses of instance `e` take values where its functions differ, if
    they do. -/
noncomputable def stepConst (P : Problem) (M : Model R U) (c : Nat → Val R U) (e : Nat × Nat × List Nat)
    (n : Nat) : Val R U :=
  match P.nodes[e.1]? with
  | some (.eq f g) =>
    if h : ∃ xs, Forall2 (fun a x => M.dom a x ∧ inRange P.bvIndex a x) (e.2.2.map P.sig.declOf) xs ∧
        appAll (M.withConst c).toInterp (val (M.withConst c).toInterp P.nodes f) xs ≠
          appAll (M.withConst c).toInterp (val (M.withConst c).toInterp P.nodes g) xs then
      setWits c e.2.2 (Classical.choose h) n
    else c n
  | _ => c n

/-- The values of the symbols after the first `k` instances. -/
noncomputable def buildConst (P : Problem) (A : Answer) (M : Model R U) : Nat → Nat → Val R U
  | 0 => startConst P A M
  | k + 1 => fun n =>
    match A.exts[k]? with
    | some e => stepConst P M (buildConst P A M k) e n
    | none => buildConst P A M k n

theorem stepConst_not {c : Nat → Val R U} {e : Nat × Nat × List Nat} {n : Nat} (h : n ∉ e.2.2) :
    stepConst P M c e n = c n := by
  unfold stepConst
  split
  · split
    · exact setWits_not h
    · rfl
  · rfl

include hA in
/-- Each instance changes only the symbols of rank above `k + 1`, from the
    `k`-th on. -/
theorem buildConst_agree {k : Nat} : ∀ j, k ≤ j → ∀ n, A.rank n ≤ k + 1 →
    buildConst P A M j n = buildConst P A M k n := by
  intro j hj n hn
  induction j with
  | zero =>
    have : k = 0 := by omega
    subst this; rfl
  | succ j ih =>
    rcases Nat.lt_or_ge j k with hjk | hjk
    · have : k = j + 1 := by omega
      subst this; rfl
    · rw [← ih hjk]
      simp only [buildConst]
      split
      · rename_i e he
        obtain ⟨eq, eqw, ws⟩ := e
        apply stepConst_not
        intro m
        have := (wits_info hA).2.2.2.2.2.2 j eq eqw ws he
        have := this.2.1 n m
        omega
      · rfl

include hA in
theorem buildConst_zero {j n : Nat} (h : A.rank n = 0) : buildConst P A M j n = M.const n := by
  rw [buildConst_agree hA (k := 0) j (Nat.zero_le _) n (by omega)]
  simp only [buildConst, startConst]
  have := rank_zero h
  rw [if_neg (by simp [this])]

include hL in
/-- Every symbol keeps a value of its sort. -/
theorem buildConst_dom : ∀ k n s, P.sig.decls[n]? = some s → M.dom s (buildConst P A M k n) := by
  intro k
  induction k with
  | zero =>
    intro n s hs
    simp only [buildConst, startConst]
    split
    · rename_i hc
      simp only [Bool.and_eq_true, Sig.is, beq_iff_eq, Sig.declOf, hs, Option.getD_some] at hc
      exact (hL.sound.int _ _ hc.2).mpr ⟨0, by rw [Ring.intCast_zero]⟩
    · exact hL.sound.const n s hs
  | succ k ih =>
    intro n s hs
    simp only [buildConst]
    split
    · rename_i e _
      unfold stepConst
      split
      · split
        · rename_i h
          by_cases m : n ∈ e.2.2
          · have := setWits_mem (c := buildConst P A M k) P.sig.declOf (Classical.choose_spec h).1 m
            simp only [Sig.declOf, hs, Option.getD_some] at this
            exact this.1
          · rw [setWits_not m]; exact ih n s hs
        · exact ih n s hs
      · exact ih n s hs
    · exact ih n s hs

include hA in
/-- A witness of a bit-vector index stays in its range. -/
theorem buildConst_range : ∀ k n w, (P.enc A).width n = some w →
    ∃ v : Int, buildConst P A M k n = .num (v : R) ∧ 0 ≤ v ∧ v < 2 ^ w := by
  intro k
  have hbv := (wits_info hA).1
  induction k with
  | zero =>
    intro n w hw
    simp only [Enc.width, Problem.enc] at hw
    split at hw
    · rename_i hn
      split at hw
      · rename_i s hs
        have hint := hbv (s, w) (lookup_mem hw)
        simp only [buildConst, startConst, hn, Sig.declOf, hs, Option.getD_some]
        simp only at hint
        simp only [hint, Bool.and_self, ↓reduceIte]
        exact ⟨0, by rw [Ring.intCast_zero], Int.le_refl 0, Int.pow_pos (by decide)⟩
      · cases hw
    · cases hw
  | succ k ih =>
    intro n w hw
    simp only [buildConst]
    split
    · rename_i e _
      unfold stepConst
      split
      · split
        · rename_i h
          by_cases m : n ∈ e.2.2
          · have := setWits_mem (c := buildConst P A M k) P.sig.declOf (Classical.choose_spec h).1 m
            simp only [Enc.width, Problem.enc] at hw
            split at hw
            · split at hw
              · rename_i s hs
                simp only [Sig.declOf, hs, Option.getD_some] at this
                exact this.2 w hw
              · cases hw
            · cases hw
          · rw [setWits_not m]; exact ih n w hw
        · exact ih n w hw
      · exact ih n w hw
    · exact ih n w hw

include hL in
theorem withConst_sound {c : Nat → Val R U} (hc : ∀ n s, P.sig.decls[n]? = some s → M.dom s (c n)) :
    (M.withConst c).Sound P.sig P.bvIndex where
  bool := hL.sound.bool
  int := hL.sound.int
  real := hL.sound.real
  fn := hL.sound.fn
  const := hc
  bvInt := hL.sound.bvInt

include hL in
/-- Two different functions differ on some arguments, in range for indices of
    bit-vectors, along a chain of sorts. -/
theorem exists_differ : ∀ (as : List Nat) (s t : Nat) (p q : Val R U), SortChain P.sig s as t →
    M.dom s p → M.dom s q → p ≠ q →
    ∃ xs, Forall2 (fun a x => M.dom a x ∧ inRange P.bvIndex a x) as xs ∧
      appAll M.toInterp p xs ≠ appAll M.toInterp q xs
  | [], s, t, p, q, _, _, _, hpq => ⟨[], trivial, hpq⟩
  | a :: as, s, t, p, q, ⟨r, hs, hc⟩, hp, hq, hpq => by
    have : ∃ x, (M.dom a x ∧ inRange P.bvIndex a x) ∧ M.app p [x] ≠ M.app q [x] := by
      apply Classical.byContradiction
      intro hn
      apply hpq
      apply hL.ext s [a] r p q hs hp hq
      intro xs hxs
      match xs, hxs with
      | [x], ⟨hx, _⟩ =>
        apply Classical.byContradiction
        intro hne
        exact hn ⟨x, hx, hne⟩
    obtain ⟨x, hx, hne⟩ := this
    have hp' := (hL.sound.fn s [a] r p [x] hs hp ⟨hx, trivial⟩).1
    have hq' := (hL.sound.fn s [a] r q [x] hs hq ⟨hx, trivial⟩).1
    obtain ⟨xs, hxs, hd⟩ := exists_differ as r t _ _ hc hp' hq' hne
    exact ⟨x :: xs, ⟨hx, hxs⟩, hd⟩

include hA hL in
/-- The nodes of bit-vector sorts stay in range as the witnesses take their
    values: they are of depth `0`, witnesses, or applications of nodes before
    them. -/
theorem rng_build (hrng : ∀ i < P.nodes.length, inRange P.bvIndex (P.sort i) (val M.toInterp P.nodes i))
    (k : Nat) : ∀ i < P.nodes.length,
      inRange P.bvIndex (P.sort i) (val (M.withConst (buildConst P A M k)).toInterp P.nodes i) := by
  obtain ⟨_, _, _, _, _, hbv, _⟩ := wits_info hA
  have hw := hA.wf
  have hsk := withConst_sound hL (buildConst_dom (A := A) hL k)
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
  intro hi
  rcases hbv i hi with h0 | hn | ⟨n, hn, hwit⟩ | ⟨f, args, hn⟩
  · rw [val_agree (rank := A.rank) (I := (M.withConst (buildConst P A M k)).toInterp) (I' := M.toInterp) (D := 0)
      hw rfl (fun n hn => buildConst_zero (M := M) (j := k) hA (by omega)) i (by omega)]
    exact hrng i hi
  · intro w hw'; simp [hw'] at hn
  · intro w hw'
    have tn := typed_node hA.typed hn
    simp only [Tab.at_eq, nodeTyped, beq_iff_eq] at tn
    have hwd : (P.enc A).width n = some w := by
      simp only [Enc.width, Problem.enc, List.contains_iff_mem.mpr hwit, ↓reduceIte, tn]
      exact hw'
    obtain ⟨v, hv, hr⟩ := buildConst_range (M := M) hA k n w hwd
    exact ⟨v, by rw [val_const hw hn]; exact hv, hr⟩
  · exact rng_app hsk hw hA.typed hi hn (fun j hj => ih j hj (by omega))

include hA hL in
/-- The instance `k` holds once its witnesses have taken their values. -/
theorem instance_holds (hrng : ∀ i < P.nodes.length, inRange P.bvIndex (P.sort i) (val M.toInterp P.nodes i))
    {k eq eqw : Nat} {ws : List Nat} (hk : A.exts[k]? = some (eq, eqw, ws)) :
    ∀ (c : Nat → Val R U), (∀ n, A.rank n ≤ k + 2 → c n = buildConst P A M (k + 1) n) →
      holds (M.withConst c).toInterp P.nodes eq ∨ ¬holds (M.withConst c).toInterp P.nodes eqw := by
  intro c hc
  obtain ⟨hnd, hr, f, g, F, G, he, hew, hdf, hdg, hcf, hcg, hxf⟩ := (wits_info hA).2.2.2.2.2.2 k eq eqw ws hk
  have hw := hA.wf
  let Ik := (M.withConst (buildConst P A M k)).toInterp
  let Ic := (M.withConst c).toInterp
  -- the functions keep the values they had before instance `k`
  have agree : ∀ i, depthOf (depths A.rank P.nodes) i ≤ k + 1 → val Ic P.nodes i = val Ik P.nodes i := by
    apply val_agree (I := Ic) (I' := Ik) hw rfl
    intro n hn
    show c n = buildConst P A M k n
    rw [hc n (by omega)]
    exact buildConst_agree hA (k + 1) (by omega) n hn
  rw [holds_eq hw he, holds_eq hw hew, agree f (by omega), agree g (by omega)]
  by_cases hfg : val Ik P.nodes f = val Ik P.nodes g
  · exact Or.inl hfg
  right
  have hF := chain_val (I := Ic) hw ws.reverse F hcf
  have hG := chain_val (I := Ic) hw ws.reverse G hcg
  rw [List.reverse_reverse] at hF hG
  rw [hF, hG, agree f (by omega), agree g (by omega)]
  have wsc : ws.map Ic.const = ws.map (buildConst P A M (k + 1)) :=
    List.map_congr_left (fun n m => hc n (by have := hr n m; omega))
  rw [wsc]
  -- the step of instance `k`
  have hstep : buildConst P A M (k + 1) = stepConst P M (buildConst P A M k) (eq, eqw, ws) := by
    simp only [buildConst, hk]
  have hs := chain_sorts hA.typed ws.reverse F hcf hxf
  rw [List.reverse_reverse] at hs
  have lf := child_lt hw he (j := f) (by simp [Node.children])
  have lg := child_lt hw he (j := g) (by simp [Node.children])
  have hsk := withConst_sound hL (buildConst_dom (A := A) hL k)
  have df := val_dom hsk hw hA.typed (rng_build hA hL hrng k) f (by have := lt_of_node he; omega)
  have dg := val_dom hsk hw hA.typed (rng_build hA hL hrng k) g (by have := lt_of_node he; omega)
  have tg : P.sortOf[g]?.getD 0 = P.sortOf[f]?.getD 0 := by
    have := typed_node hA.typed he
    simp only [Tab.at_eq, nodeTyped, Bool.and_eq_true, beq_iff_eq] at this
    exact this.2.symm
  rw [tg] at dg
  have ex := exists_differ hL _ _ _ _ _ hs df dg hfg
  rw [hstep]
  by_cases hex : ∃ xs, Forall2 (fun a x => M.dom a x ∧ inRange P.bvIndex a x) (ws.map P.sig.declOf) xs ∧
      appAll (M.withConst (buildConst P A M k)).toInterp
          (val (M.withConst (buildConst P A M k)).toInterp P.nodes f) xs ≠
        appAll (M.withConst (buildConst P A M k)).toInterp
          (val (M.withConst (buildConst P A M k)).toInterp P.nodes g) xs
  · have hlen : ws.length = (Classical.choose hex).length := by
      have := forall2_length (Classical.choose_spec hex).1
      simpa using this
    have hmap : ws.map (stepConst P M (buildConst P A M k) (eq, eqw, ws)) = Classical.choose hex := by
      rw [List.map_congr_left (g := setWits (buildConst P A M k) ws (Classical.choose hex))
        (fun n _ => by unfold stepConst; simp only [he]; rw [dif_pos hex])]
      exact setWits_map hnd hlen
    rw [hmap]
    exact (Classical.choose_spec hex).2
  · exact absurd ex hex

end

/-! ## Soundness -/

theorem dtSyms_mem {P : Problem} {d : Nat} {cs : List (Nat × Nat × List Nat)} {C T : Nat} {Ss : List Nat}
    (hd : (d, cs) ∈ P.datatypes) (hc : (C, T, Ss) ∈ cs) :
    C ∈ P.dtSyms ∧ T ∈ P.dtSyms ∧ ∀ S ∈ Ss, S ∈ P.dtSyms := by
  unfold Problem.dtSyms
  refine ⟨?_, ?_, fun S m => ?_⟩
  · exact List.mem_flatMap.mpr ⟨(d, cs), hd, List.mem_flatMap.mpr ⟨(C, T, Ss), hc, by simp⟩⟩
  · exact List.mem_flatMap.mpr ⟨(d, cs), hd, List.mem_flatMap.mpr ⟨(C, T, Ss), hc, by simp⟩⟩
  · exact List.mem_flatMap.mpr ⟨(d, cs), hd, List.mem_flatMap.mpr ⟨(C, T, Ss), hc, by simp [m]⟩⟩

/-- The laws hold of a model that changes no symbol of datatypes or stores. -/
theorem laws_withConst {P : Problem} {M : Model R U} {size : Val R U → Nat} (hL : P.Laws M size)
    {c : Nat → Val R U} (hdom : ∀ n s, P.sig.decls[n]? = some s → M.dom s (c n))
    (hdt : ∀ n ∈ P.dtSyms, c n = M.const n) (hst : ∀ n ∈ P.stores, c n = M.const n) :
    P.Laws (M.withConst c) size := by
  have cv : ∀ d cs C T Ss, (d, cs) ∈ P.datatypes → (C, T, Ss) ∈ cs →
      ∀ xs, ctorVal (M.withConst c) C xs = ctorVal M C xs := by
    intro d cs C T Ss hd hc xs
    unfold ctorVal
    simp only [Model.withConst]
    rw [hdt C (dtSyms_mem hd hc).1]
  constructor
  · exact withConst_sound hL hdom
  · intro d cs C T Ss hd hc xs i S x hxs hS hx
    rw [cv d cs C T Ss hd hc]
    simp only [Model.withConst]
    rw [hdt S ((dtSyms_mem hd hc).2.2 S (List.mem_of_getElem? hS))]
    exact hL.sel d cs C T Ss hd hc xs i S x hxs hS hx
  · intro d cs C T Ss hd hc xs hxs
    rw [cv d cs C T Ss hd hc]
    simp only [Model.withConst]
    rw [hdt T (dtSyms_mem hd hc).2.1]
    exact hL.test d cs C T Ss hd hc xs hxs
  · intro d cs C T Ss C' T' Ss' hd hc hc' hne ys hys
    rw [cv d cs C' T' Ss' hd hc']
    simp only [Model.withConst]
    rw [hdt T (dtSyms_mem hd hc).2.1]
    exact hL.testOther d cs C T Ss C' T' Ss' hd hc hc' hne ys hys
  · intro d cs C T Ss hd hc xs ys hxs hys he
    rw [cv d cs C T Ss hd hc, cv d cs C T Ss hd hc] at he
    exact hL.inj d cs C T Ss hd hc xs ys hxs hys he
  · intro d cs C T Ss C' T' Ss' hd hc hc' hne xs ys hxs hys
    rw [cv d cs C T Ss hd hc, cv d cs C' T' Ss' hd hc']
    exact hL.distinct d cs C T Ss C' T' Ss' hd hc hc' hne xs ys hxs hys
  · intro d cs C T Ss hd hc v hv ht
    rw [cv d cs C T Ss hd hc]
    simp only [Model.withConst] at ht ⊢
    rw [hdt T (dtSyms_mem hd hc).2.1] at ht
    rw [List.map_congr_left (g := fun S => M.app (M.const S) [v])
      (fun S m => by rw [hdt S ((dtSyms_mem hd hc).2.2 S m)])]
    exact hL.expand d cs C T Ss hd hc v hv ht
  · intro d cs C T Ss hd hc xs x hxs hx
    rw [cv d cs C T Ss hd hc]
    exact hL.smaller d cs C T Ss hd hc xs x hxs hx
  · intro d cs hd v hv
    obtain ⟨ct, hct, h⟩ := hL.exhaust d cs hd v hv
    refine ⟨ct, hct, ?_⟩
    simp only [Model.withConst]
    rw [hdt ct.2.1 (dtSyms_mem hd hct).2.1]
    exact h
  · intro n hn s arr idx el hd hs harr a i v j ha hi hv hj ri rj rv
    simp only [Model.withConst]
    rw [hst n hn]
    exact hL.store n hn s arr idx el hd hs harr a i v j ha hi hv hj ri rj rv
  · exact hL.ext

/-- **Soundness.** When the checker accepts an answer, no model of the
    problem's laws satisfies its inputs and the formulas of the levels it
    assumed, with the nodes of bit-vector indices in range. -/
theorem Problem.accepts_sound {P : Problem} {A : Answer} (h : P.accepts A = true) (M : Model R U)
    (size : Val R U → Nat) (hL : P.Laws M size)
    (hin : ∀ f ∈ P.inputs, holds M.toInterp P.nodes f)
    (hlev : ∀ s ∈ A.assumed, ∀ fs, A.levels.lookup s = some fs → ∀ f ∈ fs, holds M.toInterp P.nodes f)
    (hrng : ∀ i < P.nodes.length, inRange P.bvIndex (P.sort i) (val M.toInterp P.nodes i)) :
    False := by
  have hA := accepted h
  obtain ⟨_, hst, hdt, hinp, hlv, hbv, _⟩ := wits_info hA
  let N := A.exts.length
  let c := buildConst P A M N
  let M' := M.withConst c
  have hw := hA.wf
  -- the nodes of depth `0` keep their values
  have same : ∀ i, depthOf (depths A.rank P.nodes) i = 0 → val M'.toInterp P.nodes i = val M.toInterp P.nodes i :=
    fun i hi => val_agree (rank := A.rank) (I := M'.toInterp) (I' := M.toInterp) (D := 0) hw rfl
      (fun n hn => buildConst_zero (M := M) (j := N) hA (by omega)) i (by omega)
  have hL' : P.Laws M' size :=
    laws_withConst hL (buildConst_dom hL N) (fun n m => buildConst_zero hA (hdt n m))
      (fun n m => buildConst_zero hA (hst n m))
  refine accepts_sound_of_witnesses hA M' size hL' ?_ ?_ ?_ ?_ ?_
  · intro f m
    unfold holds; rw [same f (hinp f m)]; exact hin f m
  · intro s hs fs hfs f m
    unfold holds; rw [same f (hlv (s, fs) (lookup_mem hfs) f m)]
    exact hlev s hs fs hfs f m
  · intro i
    induction i using Nat.strongRecOn with
    | ind i ih =>
    intro hi
    rcases hbv i hi with h0 | hn | ⟨n, hn, hwit⟩ | ⟨f, args, hn⟩
    · rw [same i h0]; exact hrng i hi
    · intro w hw'; simp [hw'] at hn
    · intro w hw'
      have tn := typed_node hA.typed hn
      simp only [Tab.at_eq, nodeTyped, beq_iff_eq] at tn
      have hwd : (P.enc A).width n = some w := by
        simp only [Enc.width, Problem.enc, List.contains_iff_mem.mpr hwit, ↓reduceIte, tn]
        exact hw'
      obtain ⟨v, hv, hr⟩ := buildConst_range (M := M) hA N n w hwd
      exact ⟨v, by rw [val_const hw hn]; exact hv, hr⟩
    · exact rng_app hL'.sound hw hA.typed hi hn (fun j hj => ih j hj (by omega))
  · intro k eq eqw ws hk
    have hkN : k < N := by
      rcases Nat.lt_or_ge k A.exts.length with h' | h'
      · exact h'
      · rw [List.getElem?_eq_none h'] at hk; cases hk
    exact instance_holds hA hL hrng hk c (fun n hn => buildConst_agree hA N (by omega) n hn)
  · intro n w hw'
    exact buildConst_range (M := M) hA N n w hw'

end Vik.Low
