import Vik.Lower.Trace
import Vik.Cert.Clausal

/-!
# CPC proofs

A checker for the CPC proofs Vik writes (`Cpc.scala`), over the surface terms
of the script (`Vik/Surface.lean`): the terms of the proof extend the table
of the script's nodes, and each step names the node it concludes, which the
checker checks against its rule. The rules are those of cvc5's `Cpc.eo` that
Vik's proofs use, and those of `proofs/cpc/Vik.eo`: `vik_lower`, `vik_rup`
and `vik_uf`.

The checker does not compute conclusions as Ethos does, it checks a
conclusion given: what it accepts follows from the premises, which is all its
soundness needs (`Vik/Cpc/Sound.lean`).
-/

namespace Vik.Cpc

open Vik.Surf Vik.Low Vik.Clausal

/-- A step of a `vik_uf` lemma: `refl t` equates `t` with itself, `given i`
    is hypothesis `i`, `symm j`, `trans j k` and `cong j ks l r` come from
    earlier steps, the last equating the applications `l` and `r`. -/
inductive UfStep where
  | refl (t : Nat)
  | given (i : Nat)
  | symm (j : Nat)
  | trans (j k : Nat)
  | cong (j : Nat) (ks : List Nat) (l r : Nat)
  deriving Repr

/-- The rules that conclude a tautology, with no premise. -/
inductive Taut where
  | andPos | andNeg | orPos | orNeg
  | equivPos1 | equivPos2 | equivNeg1 | equivNeg2
  | itePos1 | itePos2 | itePos3 | iteNeg1 | iteNeg2 | iteNeg3
  | refl | iteEq | evaluate | doubleNot | implElim | eqRefl
  deriving Repr, DecidableEq

/-- The rule of a step, with what the checker needs beyond its premises and
    conclusion. -/
inductive Rule where
  /-- `assume` of the script's assertion `a`, through equivalence `e`. -/
  | assume (a : Nat) (e : Option Nat)
  /-- `vik_lower`, through equivalence `e`. -/
  | lower (e : Option Nat)
  | rup
  | uf (s : List UfStep)
  | taut (k : Taut)
  /-- `reordering` and `factoring`. -/
  | weaken
  /-- `chain_m_resolution`, with the polarities and the pivots. -/
  | chain (pols : List Bool) (lits : List Nat)
  | andElim | andIntro | symm | trans | cong | eqResolve | trueElim | impliesElim
  deriving Repr

/-- A step: its rule, its premises by index among the facts, its conclusion. -/
structure Step where
  rule : Rule
  prems : List Nat := []
  concl : Nat
  deriving Repr

/-- `step`, `assume-push` of a formula, and `step-pop` of `scope`: the fact of
    index `p` within the scope, and the implication concluded. -/
inductive Cmd where
  | step (s : Step)
  | push (f : Nat)
  | pop (p concl : Nat)
  deriving Repr

/-- Nodes `x` and `y` take the same value: their children pairwise, through
    the equivalences `hs`, one for each pair of children that differ. When `x`
    uses a definition, `ms` is an instance of its body (`SDef.instOk`), whose
    root takes the value of `x` and is paired with `y`. -/
structure Eqv where
  x : Nat
  y : Nat
  hs : List Nat := []
  ms : List Nat := []
  deriving Repr

/-- A proof: its nodes and their sorts after those of the script, the
    equivalences between them, and the commands. -/
structure Proof where
  extra : List SNode
  sorts : List Nat
  eqvs : List Eqv
  tt : Nat
  ff : Nat
  cmds : List Cmd
  deriving Repr

/-- The table of a proof's nodes. -/
structure Ctx where
  sig : SSig
  nodes : List SNode
  sortOf : List Nat

def Ctx.node (c : Ctx) (i : Nat) : Option SNode := Tab.at c.nodes i

def Ctx.isBool (c : Ctx) (i : Nat) : Bool := c.sig.is ((Tab.at c.sortOf i).getD 0) .bool

/-! ## Shapes -/

def eqArgs : SNode → Option (Nat × Nat)
  | .eq [a, b] | .iff [a, b] => some (a, b)
  | _ => none

def Ctx.eqOf (c : Ctx) (i : Nat) : Option (Nat × Nat) := (c.node i).bind eqArgs

def Ctx.notOf (c : Ctx) (i : Nat) : Option Nat :=
  match c.node i with
  | some (.not a) => some a
  | _ => none

def Ctx.isNot (c : Ctx) (i a : Nat) : Bool := c.notOf i == some a

def Ctx.isTt (c : Ctx) (i : Nat) : Bool := c.node i == some .tt
def Ctx.isFf (c : Ctx) (i : Nat) : Bool := c.node i == some .ff

/-- The literals of a clause: an `or`, `false`, or one literal. -/
def Ctx.clause (c : Ctx) (i : Nat) : List Nat :=
  match c.node i with
  | some (.or as) => as
  | some .ff => []
  | _ => [i]

def Ctx.isOr (c : Ctx) (i : Nat) : Bool :=
  match c.node i with
  | some (.or _) => true
  | _ => false

/-- Literal `l` as an atom and the value that makes it true, without its
    double negations. -/
def Ctx.sgn (c : Ctx) : Nat → Nat → Nat × Bool
  | 0, l => (l, true)
  | fuel + 1, l =>
    match c.notOf l with
    | some a =>
      match c.notOf a with
      | some b => c.sgn fuel b
      | none => (a, false)
    | none => (l, true)

def sgnFuel : Nat := 1000

/-- The children of a node of the shapes the rules rewrite by congruence,
    with the node's kind. -/
def kids : SNode → Option (Nat × List Nat)
  | .app f as => some (0, f :: as)
  | .not a => some (1, [a])
  | .and as => some (2, as)
  | .or as => some (3, as)
  | .implies as => some (4, as)
  | .iff as => some (5, as)
  | .eq as => some (6, as)
  | .xor as => some (7, as)
  | .distinct as => some (8, as)
  | .ite a b d => some (9, [a, b, d])
  | _ => none

/-- The pairs of children of two nodes of one kind and arity. -/
def samePairs (n m : SNode) : Option (List (Nat × Nat)) :=
  match kids n, kids m with
  | some (k, as), some (k', bs) => if k == k' && as.length == bs.length then some (as.zip bs) else none
  | _, _ => none

/-! ## Equivalences -/

/-- The pairs of distinct elements, in order. -/
def pairsOf : List Nat → List (Nat × Nat)
  | [] => []
  | a :: rest => rest.map (a, ·) ++ pairsOf rest

/-- `(= a₁ … aₙ)` read as the conjunction of its consecutive pairs. -/
def Ctx.chainPairs (c : Ctx) (eq : Bool) : List Nat → List Nat → Option (List (Nat × Nat))
  | a :: b :: rest, e :: es =>
    match c.node e with
    | some (.eq [p, q]) => if eq then (c.chainPairs eq (b :: rest) es).map ([(a, p), (b, q)] ++ ·) else none
    | some (.iff [p, q]) => if eq then none else (c.chainPairs eq (b :: rest) es).map ([(a, p), (b, q)] ++ ·)
    | _ => none
  | [_], [] => some []
  | _, _ => none

/-- `(=> a₁ … aₙ)` read to the right, as node `y`. -/
def Ctx.implPairs (c : Ctx) : List Nat → Nat → Option (List (Nat × Nat))
  | [a, b], y =>
    match c.node y with
    | some (.implies [p, q]) => some [(a, p), (b, q)]
    | _ => none
  | a :: rest@(_ :: _ :: _), y =>
    match c.node y with
    | some (.implies [p, z]) => (c.implPairs rest z).map ((a, p) :: ·)
    | _ => none
  | _, _ => none

/-- `(xor a₁ … aₙ)` read to the left, reversed, as node `y`. -/
def Ctx.xorPairs (c : Ctx) : List Nat → Nat → Option (List (Nat × Nat))
  | [b, a], y =>
    match c.node y with
    | some (.xor [p, q]) => some [(a, p), (b, q)]
    | _ => none
  | b :: rest@(_ :: _ :: _), y =>
    match c.node y with
    | some (.xor [z, q]) => (c.xorPairs rest z).map ((b, q) :: ·)
    | _ => none
  | _, _ => none

/-- The disequality of node `e`: `(not (= p q))`. -/
def Ctx.diseq (c : Ctx) (e : Nat) : Option (Nat × Nat) := (c.notOf e).bind c.eqOf

/-- `(distinct a₁ … aₙ)` as the conjunction of the disequalities `es` of its pairs. -/
def Ctx.diseqPairs (c : Ctx) : List (Nat × Nat) → List Nat → Option (List (Nat × Nat))
  | (a, b) :: ps, e :: es =>
    match c.diseq e with
    | some (p, q) => (c.diseqPairs ps es).map ((a, p) :: (b, q) :: ·)
    | none => none
  | [], [] => some []
  | _, _ => none

/-- The pairs of children through which node `x` takes the value of node `y`:
    a `let` and its body, a variable and its term, the empty conjunction and
    disjunction, chains of `=`, `=>` and `xor` as CPC reads them, `xor` and
    `distinct` as `vik_lower` rewrites them, and nodes of one shape. -/
def Ctx.eqvPairs (c : Ctx) (x y : Nat) : Option (List (Nat × Nat)) :=
  match c.node x, c.node y with
  | some (.letIn _ b), _ => some [(b, y)]
  | some (.bound d), _ => some [(d, y)]
  | some (.and []), some .tt => some []
  | some (.or []), some .ff => some []
  | some (.eq as@(_ :: _ :: _ :: _)), some (.and es) => c.chainPairs true as es
  | some (.iff as@(_ :: _ :: _ :: _)), some (.and es) => c.chainPairs false as es
  | some (.implies as@(_ :: _ :: _ :: _)), _ => c.implPairs as y
  | some (.xor as@(_ :: _ :: _ :: _)), _ => c.xorPairs as.reverse y
  | some (.xor [a, b]), some (.not e) =>
    match c.node e with
    | some (.iff [p, q]) => some [(a, p), (b, q)]
    | _ => none
  | some (.distinct as), some (.and es) =>
    if (pairsOf as).length == es.length then c.diseqPairs (pairsOf as) es else none
  | some n, some m => samePairs n m
  | _, _ => none

/-- Node `x` as the use of a symbol `k`, a constant or an application, with
    its arguments. -/
def Ctx.defUse (c : Ctx) (x : Nat) : Option (Nat × List Nat × Bool) :=
  match c.node x with
  | some (.const k) => some (k, [], false)
  | some (.app f as) =>
    match c.node f with
    | some (.const k) => some (k, as, true)
    | _ => none
  | _ => none

/-- A use `x` of a definition (`define-fun`) and an instance `ms` of the
    definition's body on the use's arguments: the instance's root paired with
    `y`. -/
def Ctx.defPairs (c : Ctx) (defs : List SDef) (x y : Nat) (ms : List Nat) : Option (List (Nat × Nat)) :=
  match c.defUse x with
  | some (k, as, isApp) =>
    match defs.find? (·.sym == k) with
    | some d =>
      if isApp == !d.params.isEmpty && d.params.length == as.length && wellFormed d.nodes &&
          d.root < d.nodes.length &&
          (d.params.zip as).all (fun q => c.sig.decls.getD q.1 0 == c.sortOf.getD q.2 0) &&
          d.instOk c.nodes as ms then
        some [(ms.getD d.root 0, y)]
      else none
    | none => none
  | none => none

/-- Each pair equal, or equated by an earlier equivalence among `hs`, in turn. -/
def pairsOk (eqvs : List Eqv) (k : Nat) : List (Nat × Nat) → List Nat → Bool
  | [], _ => true
  | (p, q) :: ps, hs =>
    if p == q then pairsOk eqvs k ps hs
    else
      match hs with
      | h :: hs' =>
        h < k && (match Tab.at eqvs h with
          | some e => e.x == p && e.y == q
          | none => false) && pairsOk eqvs k ps hs'
      | [] => false

def Ctx.eqvOk (c : Ctx) (defs : List SDef) (eqvs : List Eqv) (k : Nat) : Bool :=
  match Tab.at eqvs k with
  | some e =>
    match if e.ms.isEmpty then c.eqvPairs e.x e.y else c.defPairs defs e.x e.y e.ms with
    | some ps => pairsOk eqvs k ps e.hs
    | none => false
  | none => false

def Ctx.eqvsOk (c : Ctx) (defs : List SDef) (eqvs : List Eqv) : Bool :=
  (List.range eqvs.length).all fun k => c.eqvOk defs eqvs k

/-- `x` takes the value of `y`: they are equal, or equivalence `e` equates them. -/
def viaEqv (eqvs : List Eqv) (x y : Nat) : Option Nat → Bool
  | none => x == y
  | some e =>
    match Tab.at eqvs e with
    | some q => q.x == x && q.y == y
    | none => false

/-! ## Reverse unit propagation (`vik_rup`) -/

/-- The value of literal `l` in `t`, if it has one. -/
def Ctx.litVal (c : Ctx) (t : TT) (l : Nat) : Option Bool :=
  let (a, p) := c.sgn sgnFuel l
  (t.get a).map (· == p)

/-- `t` with literal `l` set to `b`. -/
def Ctx.setLit (c : Ctx) (t : TT) (l : Nat) (b : Bool) : TT :=
  let (a, p) := c.sgn sgnFuel l
  t.set a (p == b)

/-- `none` when a literal of `ls` is true, otherwise those that have no value. -/
def Ctx.openLits (c : Ctx) (t : TT) : List Nat → Option (List Nat)
  | [] => some []
  | l :: ls =>
    match c.litVal t l with
    | some true => none
    | some false => c.openLits t ls
    | none => (c.openLits t ls).map (l :: ·)

/-- Unit propagation over the clauses `cs`, in turn, to a conflict. -/
def Ctx.propagate (c : Ctx) : TT → List Nat → Bool
  | _, [] => false
  | t, x :: xs =>
    if c.litVal t x == some false then true
    else
      let t := if c.isOr x then c.setLit t x true else t
      match c.openLits t (c.clause x) with
      | none => c.propagate t xs
      | some [] => true
      | some [u] => c.propagate (c.setLit t u true) xs
      | some _ => c.propagate t xs

/-- Two literals of `ls` are each other's negation. -/
def Ctx.taut (c : Ctx) (ls : List Nat) : Bool :=
  let ss := ls.map (c.sgn sgnFuel)
  ss.any fun (a, p) => ss.contains (a, !p)

/-- `d` follows from the premises `cs` by unit propagation. -/
def Ctx.rup (c : Ctx) (cs : List Nat) (d : Nat) : Bool :=
  let ls := if c.isOr d then d :: c.clause d else c.clause d
  c.taut ls || c.propagate (ls.foldl (fun t l => c.setLit t l false) .leaf) cs

/-! ## Equality lemmas (`vik_uf`) -/

/-- The hypotheses of clause `d`: each literal false, as an atom and its value. -/
def Ctx.hyps (c : Ctx) (d : Nat) : List (Nat × Bool) :=
  (c.clause d).map fun l => let (a, p) := c.sgn sgnFuel l; (a, !p)

/-- The equality of a hypothesis. -/
def Ctx.given (c : Ctx) (tt ff : Nat) (h : Nat × Bool) : Option (Nat × Nat) :=
  if h.2 then
    match c.eqOf h.1 with
    | some e => some e
    | none => some (h.1, tt)
  else if c.isBool h.1 then some (h.1, ff) else none

/-- The equalities of the steps, in order. -/
def Ctx.ufSteps (c : Ctx) (tt ff : Nat) (H : List (Nat × Bool)) :
    List (Nat × Nat) → List UfStep → Option (List (Nat × Nat))
  | done, [] => some done
  | done, s :: ss =>
    let r : Option (Nat × Nat) := match s with
      | .refl t => some (t, t)
      | .given i => H[i]?.bind (c.given tt ff)
      | .symm j => done[j]?.map fun (a, b) => (b, a)
      | .trans j k =>
        match done[j]?, done[k]? with
        | some (a, b), some (b', d) => if b == b' then some (a, d) else none
        | _, _ => none
      | .cong j ks l r =>
        match done[j]?, c.node l, c.node r with
        | some (f, g), some (.app f' as), some (.app g' bs) =>
          if f == f' && g == g' && as.length == ks.length && bs.length == ks.length &&
              (ks.zip (as.zip bs)).all fun (k, p) => done[k]? == some p then some (l, r)
          else none
        | _, _, _ => none
    match r with
    | some e => c.ufSteps tt ff H (done ++ [e]) ss
    | none => none

/-- The last equality contradicts the hypotheses. -/
def Ctx.clash (c : Ctx) (H : List (Nat × Bool)) (a b : Nat) : Bool :=
  (c.isTt a && c.isFf b) || (c.isFf a && c.isTt b) ||
  (c.isTt b && H.contains (a, false)) || (c.isTt a && H.contains (b, false)) ||
  (c.isFf b && H.contains (c.sgn sgnFuel a)) || (c.isFf a && H.contains (c.sgn sgnFuel b)) ||
  H.any fun (e, v) => !v && (c.eqOf e == some (a, b) || c.eqOf e == some (b, a))

/-- Clause `d` holds by the equalities of `ss`. -/
def Ctx.uf (c : Ctx) (tt ff d : Nat) (ss : List UfStep) : Bool :=
  let H := c.hyps d
  match c.ufSteps tt ff H [] ss with
  | some done =>
    match done.getLast? with
    | some (a, b) => c.clash H a b
    | none => false
  | none => false

/-! ## Resolution -/

/-- Literal `l` is the pivot `L`, or its negation when `pol` is false. -/
def Ctx.isPos (c : Ctx) (pol : Bool) (L l : Nat) : Bool := if pol then l == L else c.isNot l L

/-- Literal `l` is the negation of `L`, or `L` when `pol` is false. -/
def Ctx.isNeg (c : Ctx) (pol : Bool) (L l : Nat) : Bool := if pol then c.isNot l L else l == L

/-- The literals of premise `x` once the negative pivot is resolved away. -/
def Ctx.rest (c : Ctx) (pol : Bool) (L x : Nat) : List Nat :=
  if c.isNeg pol L x then [] else (c.clause x).filter fun l => !c.isNeg pol L l

/-- The resolvent of clause `cur` with the premises, in turn. -/
def Ctx.resolve (c : Ctx) : List Nat → List Nat → List Bool → List Nat → Option (List Nat)
  | cur, [], [], [] => some cur
  | cur, x :: xs, pol :: pols, L :: Ls =>
    c.resolve (cur.filter (fun l => !c.isPos pol L l) ++ c.rest pol L x) xs pols Ls
  | _, _, _, _ => none

/-- Each literal of `ls` implies formula `d`. -/
def Ctx.implies (c : Ctx) (ls : List Nat) (d : Nat) : Bool :=
  ls.all fun l => l == d || (c.clause d).contains l

def Ctx.chain (c : Ctx) (ps : List Nat) (pols : List Bool) (Ls : List Nat) (d : Nat) : Bool :=
  match ps, pols, Ls with
  | x :: xs, pol :: _, L :: _ =>
    let cur := if c.isPos pol L x then [x] else c.clause x
    match c.resolve cur xs pols Ls with
    | some r => c.implies r d
    | none => false
  | _, _, _ => false

/-! ## Tautologies -/

def Ctx.args (c : Ctx) (i : Nat) : Option (List Nat) := (c.node i).map SNode.children

/-- A closed formula of `true`, `false`, `not`, `and` and `or`, and its value. -/
def Ctx.evalB (c : Ctx) : Nat → Nat → Option Bool
  | 0, _ => none
  | fuel + 1, i =>
    match c.node i with
    | some .tt => some true
    | some .ff => some false
    | some (.not a) => (c.evalB fuel a).map (!·)
    | _ => none

/-- `(or (not f) …)`, the `not` and the rest of the clause. -/
def Ctx.orNot (c : Ctx) (d : Nat) : Option (Nat × List Nat) :=
  match c.node d with
  | some (.or (n :: ls)) => (c.notOf n).map (·, ls)
  | _ => none

def Ctx.tautOk (c : Ctx) (k : Taut) (d : Nat) : Bool :=
  match k with
  | .andPos =>
    match c.orNot d with
    | some (f, [x]) => match c.node f with | some (.and as) => as.contains x | _ => false
    | _ => false
  | .andNeg =>
    match c.node d with
    | some (.or (f :: ns)) =>
      match c.node f with
      | some (.and as) => as.length == ns.length && (as.zip ns).all fun (a, n) => c.isNot n a
      | _ => false
    | _ => false
  | .orPos =>
    match c.orNot d with
    | some (f, ls) => c.node f == some (.or ls)
    | _ => false
  | .orNeg =>
    match c.node d with
    | some (.or [f, n]) =>
      match c.node f, c.notOf n with
      | some (.or as), some x => as.contains x
      | _, _ => false
    | _ => false
  | .equivPos1 | .equivPos2 =>
    match c.orNot d with
    | some (e, [l1, l2]) =>
      match c.node e with
      | some (.iff [a, b]) => if k == .equivPos1 then c.isNot l1 a && l2 == b else l1 == a && c.isNot l2 b
      | _ => false
    | _ => false
  | .equivNeg1 | .equivNeg2 =>
    match c.node d with
    | some (.or [e, l1, l2]) =>
      match c.node e with
      | some (.iff [a, b]) => if k == .equivNeg1 then l1 == a && l2 == b else c.isNot l1 a && c.isNot l2 b
      | _ => false
    | _ => false
  | .itePos1 | .itePos2 | .itePos3 =>
    match c.orNot d with
    | some (e, [l1, l2]) =>
      match c.node e with
      | some (.ite x a b) =>
        if k == .itePos1 then c.isNot l1 x && l2 == a
        else if k == .itePos2 then l1 == x && l2 == b
        else l1 == a && l2 == b
      | _ => false
    | _ => false
  | .iteNeg1 | .iteNeg2 | .iteNeg3 =>
    match c.node d with
    | some (.or [e, l1, l2]) =>
      match c.node e with
      | some (.ite x a b) =>
        if k == .iteNeg1 then c.isNot l1 x && c.isNot l2 a
        else if k == .iteNeg2 then l1 == x && c.isNot l2 b
        else c.isNot l1 a && c.isNot l2 b
      | _ => false
    | _ => false
  | .refl =>
    match c.eqOf d with
    | some (a, b) => a == b
    | none => false
  | .iteEq =>
    match c.node d with
    | some (.ite x e1 e2) =>
      match c.eqOf e1, c.eqOf e2 with
      | some (k1, a), some (k2, b) => k1 == k2 && c.node k1 == some (.ite x a b)
      | _, _ => false
    | _ => false
  | .evaluate =>
    match c.node d with
    | some (.iff [t, v]) =>
      match c.evalB 64 t with
      | some true => c.isTt v
      | some false => c.isFf v
      | none => false
    | _ => false
  | .doubleNot =>
    match c.node d with
    | some (.iff [x, y]) => (c.notOf x).bind c.notOf == some y
    | _ => false
  | .implElim =>
    match c.node d with
    | some (.iff [x, y]) =>
      match c.node x, c.node y with
      | some (.implies [a, b]), some (.or [n, b']) => c.isNot n a && b == b'
      | _, _ => false
    | _ => false
  | .eqRefl =>
    match c.node d with
    | some (.iff [e, t]) =>
      c.isTt t && match c.eqOf e with
        | some (a, b) => a == b
        | none => false
    | _ => false

/-! ## Steps -/

/-- Congruence: `d` equates `t` with a node of its shape whose children differ
    by the premises, in order. -/
def Ctx.congOk (c : Ctx) (ps : List Nat) (d : Nat) : Bool :=
  match c.eqOf d with
  | some (t, u) =>
    match c.node t, c.node u with
    | some n, some m =>
      match samePairs n m with
      | some pairs =>
        -- An application keeps its function: the premises are for the arguments.
        let pairs := match n with
          | .app _ _ => pairs.tail
          | _ => pairs
        (match n, m with
          | .app f _, .app g _ => f == g
          | _, _ => true) &&
        pairs.length == ps.length && (pairs.zip ps).all fun ((a, b), p) => c.eqOf p == some (a, b)
      | none => false
    | _, _ => false
  | none => false

/-- The chain `s = … = a = …` of the premises, from `a`, to `d`, which equates
    `s` with the last term. -/
def Ctx.transOk (c : Ctx) (s : Nat) : Nat → List Nat → Nat → Bool
  | a, [], d => match c.eqOf d with
    | some (x, y) => x == s && y == a
    | none => false
  | a, p :: ps, d => match c.eqOf p with
    | some (x, y) => x == a && c.transOk s y ps d
    | none => false

def Ctx.stepOk (c : Ctx) (asserts : List Nat) (P : Proof) (s : Step) (ps : List Nat) : Bool :=
  let d := s.concl
  match s.rule, ps with
  | .assume a e, [] => asserts.contains a && viaEqv P.eqvs a d e
  | .lower e, [f] => viaEqv P.eqvs f d e
  | .rup, ps => c.rup ps d
  | .uf ss, [] => c.uf P.tt P.ff d ss
  | .taut k, [] => c.tautOk k d
  | .weaken, [x] => x == d || c.implies (c.clause x) d
  | .chain pols Ls, ps => c.chain ps pols Ls d
  | .andElim, [x] =>
    match c.node x with
    | some (.and as) => as.contains d
    | _ => false
  | .andIntro, ps => c.node d == some (.and ps) || ps == [d]
  | .symm, [x] =>
    match c.node x, c.node d with
    | some (.eq [a, b]), some (.eq [b', a']) => a == a' && b == b'
    | some (.iff [a, b]), some (.iff [b', a']) => a == a' && b == b'
    | some (.not e), some (.not e') =>
      match c.node e, c.node e' with
      | some (.eq [a, b]), some (.eq [b', a']) => a == a' && b == b'
      | some (.iff [a, b]), some (.iff [b', a']) => a == a' && b == b'
      | _, _ => false
    | _, _ => false
  | .trans, p :: ps => match c.eqOf p with
    | some (a, _) => c.transOk a a (p :: ps) d
    | none => false
  | .cong, ps => c.congOk ps d
  | .eqResolve, [x, e] => c.node e == some (.iff [x, d])
  | .trueElim, [e] =>
    match c.node e with
    | some (.iff [x, t]) => x == d && c.isTt t
    | _ => false
  | .impliesElim, [x] =>
    match c.node x, c.node d with
    | some (.implies [a, b]), some (.or [n, b']) => c.isNot n a && b == b'
    | _, _ => false
  | _, _ => false

/-! ## Proofs -/

/-- A table from numbers, as a binary trie. -/
inductive Trie where
  | leaf
  | node (v : Option Nat) (l r : Trie)

def Trie.get : Trie → Nat → Option Nat
  | .leaf, _ => none
  | .node v l r, n =>
    match n with
    | 0 => v
    | n + 1 => if n % 2 == 0 then l.get (n / 2) else r.get (n / 2)

def Trie.single : Nat → Nat → Nat → Trie
  | 0, _, _ => .leaf
  | _ + 1, 0, b => .node (some b) .leaf .leaf
  | f + 1, n + 1, b =>
    if n % 2 == 0 then .node none (Trie.single f (n / 2) b) .leaf else .node none .leaf (Trie.single f (n / 2) b)

def Trie.set : Trie → Nat → Nat → Trie
  | .leaf, n, b => Trie.single (n + 1) n b
  | .node _ l r, 0, b => .node (some b) l r
  | .node v l r, n + 1, b => if n % 2 == 0 then .node v (l.set (n / 2) b) r else .node v l (r.set (n / 2) b)

def optAll : List (Option Nat) → Option (List Nat)
  | [] => some []
  | x :: xs => x.bind fun a => (optAll xs).map (a :: ·)

/-- The state of a proof: its facts by index, their number, and the
    assumptions of the open scopes, each with the number of facts before it. -/
structure State where
  facts : Trie
  n : Nat
  stack : List (Nat × Nat)

def State.prem (st : State) (i : Nat) : Option Nat := if i < st.n then st.facts.get i else none

def State.add (st : State) (d : Nat) : State := { st with facts := st.facts.set st.n d, n := st.n + 1 }

def Ctx.cmd (c : Ctx) (asserts : List Nat) (P : Proof) (st : State) : Cmd → Option State
  | .step s =>
    match optAll (s.prems.map st.prem) with
    | some ps => if c.stepOk asserts P s ps then some (st.add s.concl) else none
    | none => none
  | .push f => if c.isBool f then some { st.add f with stack := (f, st.n) :: st.stack } else none
  | .pop p d =>
    match st.stack, st.prem p with
    | (f, m) :: rest, some g =>
      if c.node d == some (.implies [f, g]) then
        some { facts := st.facts.set m d, n := m + 1, stack := rest }
      else none
    | _, _ => none

def Ctx.run (c : Ctx) (asserts : List Nat) (P : Proof) : State → List Cmd → Option State
  | st, [] => some st
  | st, x :: xs =>
    match c.cmd asserts P st x with
    | some st' => c.run asserts P st' xs
    | none => none

/-- The table of the script's nodes and the proof's. -/
def Proof.ctx (SP : Vik.Lower.SProblem) (P : Proof) : Ctx :=
  ⟨SP.sig, SP.nodes ++ P.extra, SP.sortOf ++ P.sorts⟩

/-- The checker: the table of nodes is well formed and well sorted, the
    equivalences hold, and the proof derives `false` with no scope open. -/
def Proof.check (SP : Vik.Lower.SProblem) (P : Proof) : Bool :=
  let c := P.ctx SP
  SP.sortOf.length == SP.nodes.length &&
  wellFormed c.nodes && typed c.sig c.nodes c.sortOf &&
  c.isTt P.tt && c.isFf P.ff && c.eqvsOk SP.defs P.eqvs &&
  match c.run SP.asserts P ⟨.leaf, 0, []⟩ P.cmds with
  | some st => st.stack.isEmpty && 0 < st.n && (st.facts.get (st.n - 1)).any c.isFf
  | none => false

end Vik.Cpc
