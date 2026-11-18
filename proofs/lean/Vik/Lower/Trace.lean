import Vik.Surface
import Vik.Lower.Shape
import Vik.Cert.Extend
import Vik.Rules
import Vik.Values

/-!
# Lowering traces

A surface script, the lowered problem Vik solves, and a trace between them:
the lowered node of each surface node, and the symbols the lowering mints
after those of the script, each with its reason (the value of an `ite`, the
store of an array sort). `Trace.check` checks the trace node by node, against
the shape the lowering gives each operation (`expect`).

This covers the operations that lower to themselves: Booleans, linear integer
and real arithmetic, uninterpreted functions, datatypes, arrays, and `ite` on
terms; and the operations on bit-vectors that lower to linear terms and
comparisons of their values.
-/

set_option linter.unusedSectionVars false

namespace Vik.Lower

open Lean.Grind Vik.Real Vik.Low Vik.Surf

/-- The lowered sort of a surface sort: a bit-vector is its integer, an array
    the function from its indices. -/
def lowerSort : SSort → SortDef
  | .bool => .bool
  | .int => .int
  | .real => .real
  | .user => .user
  | .bv _ => .int
  | .fn as r => .fn as r
  | .array i e => .fn [i] e

/-- A surface script at one `check-sat`: its sorts and symbols, its nodes with
    their sorts, the assertions, and its datatypes (for each sort, the
    constructors with their testers and selectors).

    The assertions are those the check sees: the assertions of the open
    levels (named or not) and the assumptions of a `check-sat-assuming`. The
    nodes are the script's terms as written, `let` and the uses of
    definitions included; the nodes of the instances of definitions that the
    lowering inlines come before their uses. -/
structure SProblem where
  sig : SSig
  nodes : List SNode
  sortOf : List Nat
  asserts : List Nat
  datatypes : List (Nat × List (Nat × Nat × List Nat))
  /-- The definitions (`define-fun`), each asserted as SMT-LIB says. -/
  defs : List SDef := []

/-- A rule of the lowering that mints integer symbols (the rules of
    `LoweringCheck.check`), over lowered nodes. -/
inductive Rule where
  /-- `modulo(v, w, lo, hi)`: `v mod 2^w`, and `v div 2^w` unless `hi - lo < 4`. -/
  | modulo (v w : Nat) (lo hi : Int)
  /-- `cases(c, thn, els, lo, hi)`: `thn` if the formula `c` holds, `els` otherwise. -/
  | cases (c thn els : Nat) (lo hi : Int)
  /-- `divide(v, d, qmax)`: `v div d` and `v mod d`. -/
  | divide (v : Nat) (d qmax : Int)
  /-- `sdivide(t, w, d, floor)`: the quotient and remainder of the signed
      value of `t` by `d`, floored or truncated. -/
  | sdivide (t w : Nat) (d : Int) (floor : Bool)
  /-- `int2bv(t, w)`: `t mod 2^w` and `t div 2^w`. -/
  | int2bv (t w : Nat)
  /-- `smodz(a, c, w)`: whether `bvsmod` by the constant `c` corrects the
      remainder. -/
  | smodz (a : Nat) (c : Int) (w : Nat)
  /-- `bits(t, w)`: bit `j` of `t`, for each `j < w`. -/
  | bits (t w : Nat)
  /-- `udiv(a, b, w)`: the quotient and remainder of `a` by the unknown `b`,
      all ones and `a` when `b` is zero. -/
  | udiv (a b w : Nat)
  deriving DecidableEq, Repr

/-- The lowered nodes a rule applies to. -/
def Rule.args : Rule → List Nat
  | .modulo v _ _ _ | .divide v _ _ | .sdivide v _ _ _ | .int2bv v _ | .smodz v _ _ | .bits v _ => [v]
  | .cases c t e _ _ => [c, t, e]
  | .udiv a b _ => [a, b]

/-- The number of symbols of a rule. -/
def Rule.nsyms : Rule → Nat
  | .modulo _ _ lo hi => if hi - lo < 4 then 1 else 2
  | .cases .. | .smodz .. => 1
  | .bits _ w => w
  | _ => 2

/-- The signed value of `t`, of width `w`. -/
def signedI (w : Nat) (t : Int) : Int := if 2 ^ (w - 1) ≤ t then t - 2 ^ w else t

/-- The signed divisor of `bvsmod` by the constant `c`. -/
def smodT (c : Int) (w : Nat) : Int := if 2 ^ w / 2 ≤ c then c - 2 ^ w else c

/-- `smodz`: `1` when the signs of `a` and of the divisor differ and the
    truncated remainder is not zero. -/
def smodzVal (a c : Int) (w : Nat) : Int :=
  let t := smodT c w
  let neg := decide (2 ^ (w - 1) ≤ a)
  let differ := if 0 < t then neg else !neg
  if differ && (signedI w a).tmod t.natAbs != 0 then 1 else 0

/-- The value of symbol `j` of a rule, the integers of its arguments `ι` and
    the truths of its conditions `τ`. -/
def Rule.ival (ι : Nat → Int) (τ : Nat → Bool) : Rule → Nat → Int
  | .modulo v w _ _, 0 => ι v % 2 ^ w
  | .modulo v w _ _, _ => ι v / 2 ^ w
  | .cases c t e _ _, _ => if τ c then ι t else ι e
  | .divide v d _, 0 => ι v / d
  | .divide v d _, _ => ι v % d
  | .sdivide t w d fl, 0 => if fl then signedI w (ι t) / d else (signedI w (ι t)).tdiv d
  | .sdivide t w d fl, _ => if fl then signedI w (ι t) % d else (signedI w (ι t)).tmod d
  | .int2bv t w, 0 => ι t % 2 ^ w
  | .int2bv t w, _ => ι t / 2 ^ w
  | .smodz a c w, _ => smodzVal (ι a) c w
  | .bits t _, j => bit (ι t) j
  | .udiv a b w, 0 => (if ι b = 0 then 2 ^ w - 1 else ι a / ι b) % 2 ^ w
  | .udiv a b w, _ => (if ι b = 0 then ι a else ι a % ι b) % 2 ^ w

/-- Whether symbol `j` of a rule is a bit-vector of width `w` whatever its
    arguments: a remainder modulo `2^w`, a bit, or the correction of `smodz`. -/
def Rule.bvOut : Rule → Nat → Nat → Bool
  | .modulo _ w' _ _, 0, w | .int2bv _ w', 0, w | .udiv _ _ w', _, w => w' == w
  | .bits _ _, _, w | .smodz .., _, w => 0 < w
  | _, _, _ => false

/-- A real-valued symbol the lowering mints. -/
inductive RRule where
  /-- `rat(p, q)`: the rational `p / q`. -/
  | rat (p : Int) (q : Nat)
  /-- `ratmul(p, q, t)`: `p / q · t`. -/
  | ratmul (p : Int) (q t : Nat)
  /-- `floor(t)`: the floor of `t`, an integer. -/
  | floor (t : Nat)
  deriving DecidableEq, Repr

/-- The lowered nodes a real rule applies to. -/
def RRule.args : RRule → List Nat
  | .rat .. => []
  | .ratmul _ _ t | .floor t => [t]

/-- Whether the symbol of a real rule is an integer. -/
def RRule.isInt : RRule → Bool
  | .floor _ => true
  | _ => false

/-- Why the lowering mints a symbol. -/
inductive Mint where
  /-- The value of the `ite` at surface node `i`. -/
  | ite (i : Nat)
  /-- The store of the arrays of surface sort `s`. -/
  | store (s : Nat)
  /-- Symbol `j` of a rule. -/
  | rule (r : Rule) (j : Nat)
  /-- The symbol of a real rule. -/
  | real (r : RRule)
  /-- A symbol no reason defines, of the surface sort `s`, a Boolean or a
      number: a witness of the answer (an index where two arrays differ), or a
      symbol an earlier check minted. Any value of its sort. -/
  | witness (s : Nat)
  /-- A symbol no reason defines, valued as surface node `i`: a witness of
      the answer of a sort without numbers, such as an uninterpreted one. -/
  | pick (i : Nat)
  deriving DecidableEq, Repr

/-- Why a lowered input holds. -/
inductive InputWhy where
  /-- It is the lowering of the surface assertion at node `a`. -/
  | assert (a : Nat)
  /-- `c → k = t` for the `ite` symbol `k`. -/
  | iteThen (k : Nat)
  /-- `¬c → k = e` for the `ite` symbol `k`. -/
  | iteElse (k : Nat)
  /-- `0 ≤ t ≤ 2^w - 1` for the lowered node `t` of the surface node `i`, a
      bit-vector of width `w`. -/
  | range (i : Nat)
  /-- Fact `f` of rule `r`, `aux` the node of the signed value of `sdivide`,
      or of the remainder for `smodz`. -/
  | rule (r : Rule) (f aux : Nat)
  /-- Fact `f` of the real rule `r`. -/
  | real (r : RRule) (f : Nat)
  deriving DecidableEq, Repr

structure Trace where
  /-- The lowered node of each surface node. -/
  node : List Nat
  /-- The symbols after those of the script, in order. -/
  mints : List Mint
  /-- Why each lowered input holds, in order. -/
  inputs : List InputWhy
  /-- Why each formula of each assumed level holds: one list per level of
      `Answer.assumed`, in order, for the formulas `Answer.levels` gives it. -/
  levels : List (List InputWhy) := []
  /-- For each use of a definition, by its node: the nodes of the instance of
      the definition's body that the lowering inlined, one per body node. -/
  insts : List (Nat × List Nat) := []

/-! ## The expected shapes -/

/-- Consecutive pairs. -/
def consec {α : Type} : List α → List (α × α)
  | a :: b :: rest => (a, b) :: consec (b :: rest)
  | _ => []

/-- All pairs, in order. -/
def allPairs {α : Type} : List α → List (α × α)
  | [] => []
  | a :: rest => rest.map (a, ·) ++ allPairs rest

/-- The conjunction of conditions, itself when there is one. -/
def chainS : List Shape → Shape
  | [s] => s
  | ss => .and ss

/-- `(=> a₁ … aₙ)`, to the right. -/
def impliesS : List Shape → Option Shape
  | [] => none
  | [s] => some s
  | s :: rest => (impliesS rest).map (.implies s)

/-- `(xor a₁ … aₙ)`, to the left. -/
def xorS : List Shape → Option Shape
  | [] => none
  | s :: rest => some (rest.foldl (fun acc x => .not (.iff acc x)) s)

/-- The sum of linear combinations. -/
def sumForms : List (Lia.Form × Int) → Lia.Form × Int
  | [] => ([], 0)
  | (f, c) :: ps => (f ++ (sumForms ps).1, c + (sumForms ps).2)

/-- The product of two linear combinations, one of them a constant. -/
def mul2 (p q : Lia.Form × Int) : Option (Lia.Form × Int) :=
  if p.1.isEmpty then some (Lia.scale (p.2 : Rat) q.1, p.2 * q.2)
  else if q.1.isEmpty then some (Lia.scale (q.2 : Rat) p.1, p.2 * q.2)
  else none

def mulForms : List (Lia.Form × Int) → Option (Lia.Form × Int)
  | [] => some ([], 1)
  | p :: ps => (mulForms ps).bind (mul2 p)

section
variable (SP : SProblem) (P : Problem) (tr : Trace)

/-- The lowered node of surface node `i`. -/
def Trace.at (i : Nat) : Nat := (Tab.at tr.node i).getD 0

theorem Trace.at_eq (i : Nat) : tr.at i = tr.node[i]?.getD 0 := by simp [Trace.at]

def SProblem.sort (i : Nat) : Nat := SP.sortOf[i]?.getD 0

theorem SProblem.sort_eq (i : Nat) : SP.sort i = SP.sortOf[i]?.getD 0 := rfl

def SProblem.isBool (i : Nat) : Bool := SP.sig.is (SP.sort i) .bool
def SProblem.isInt (i : Nat) : Bool := SP.sig.is (SP.sort i) .int
def SProblem.isNum (i : Nat) : Bool := SP.sig.numeric (SP.sort i)

/-- The width of surface sort `s`, if it is a sort of bit-vectors. -/
def SProblem.sortWidth (s : Nat) : Option Nat :=
  match SP.sig.sorts[s]? with
  | some (SSort.bv w) => some w
  | _ => none

/-- The width of surface node `i`, if it is a bit-vector. -/
def SProblem.width (i : Nat) : Option Nat := SP.sortWidth (SP.sort i)

def SProblem.isBv (i : Nat) : Bool := (SP.width i).isSome

/-- Whether surface node `i` lowers to an integer: an integer or a bit-vector. -/
def SProblem.isIntLike (i : Nat) : Bool := SP.isInt i || SP.isBv i

/-- Whether surface node `i` lowers to a number. -/
def SProblem.isArith (i : Nat) : Bool := SP.isNum i || SP.isBv i

/-- The sorts of bit-vectors, with their widths. -/
def SProblem.bvIndex : List (Nat × Nat) :=
  (List.range SP.sig.sorts.length).filterMap fun s => (SP.sortWidth s).map (s, ·)

/-- Surface node `a` as a lowered term. -/
def leaf (a : Nat) : Shape := if SP.isBool a then .bool (tr.at a) else .same (tr.at a)

/-- Surface node `a`, a formula. -/
def form (a : Nat) : Shape := .bool (tr.at a)

/-- Surface node `a` as a linear combination. -/
def linOf (a : Nat) : Lia.Form × Int := lin P.nodes (tr.at a)

/-- `a < b` on integers: `a + 1 ≤ b`. -/
def ltInt (a b : Nat) : Shape := .le (.num (linOf P tr a).1 ((linOf P tr a).2 + 1)) (.same (tr.at b))

/-- The equality of two lowered terms of surface sort `s`. -/
def eqS (num : Bool) (a b : Shape) : Shape := if num then .and [.le a b, .le b a] else .eq a b

def Trace.nsd : Nat := SP.sig.decls.length

/-- `negative(t, w)`: the sign of the lowered node `t`, `2^(w-1) ≤ t`. -/
def negS (t w : Nat) : Shape :=
  match Tab.at P.nodes (t) with
  | some (.num v) => if 2 ^ (w - 1) ≤ v then .tt else .ff
  | _ => .le (.num [] (2 ^ (w - 1))) (.same t)

/-! ## The symbols of rules -/

/-- The rank of a symbol: one more than its index among the minted symbols if
    a rule mints it, `0` otherwise. A rule's arguments only depend on the
    symbols of rules minted before it. -/
def Trace.rank (k : Nat) : Nat :=
  if SP.sig.decls.length ≤ k then
    match Tab.at tr.mints (k - SP.sig.decls.length) with
    | some (.rule _ _) | some (.real _) => k - SP.sig.decls.length + 1
    | _ => 0
  else 0

/-- The rule and index of the symbol of lowered node `x`, if a rule mints it. -/
def Trace.symAt (x : Nat) : Option (Rule × Nat) :=
  match Tab.at P.nodes (x) with
  | some (.const k) =>
    if SP.sig.decls.length ≤ k then
      match Tab.at tr.mints (k - SP.sig.decls.length) with
      | some (.rule r j) => some (r, j)
      | _ => none
    else none
  | _ => none

/-- The lowered node of symbol `j` of rule `r`. -/
def Trace.symNode (r : Rule) (j : Nat) : Option Nat :=
  let m := tr.mints.idxOf (.rule r j)
  if m < tr.mints.length then
    let x := P.nodes.idxOf (.const (SP.sig.decls.length + m))
    if x < P.nodes.length then some x else none
  else none

/-- The real rule of the symbol of lowered node `x`, if one mints it. -/
def Trace.realAt (x : Nat) : Option RRule :=
  match Tab.at P.nodes (x) with
  | some (.const k) =>
    if SP.sig.decls.length ≤ k then
      match Tab.at tr.mints (k - SP.sig.decls.length) with
      | some (.real r) => some r
      | _ => none
    else none
  | _ => none

/-- The lowered node of the symbol of the real rule `r`. -/
def Trace.realNode (r : RRule) : Option Nat :=
  let m := tr.mints.idxOf (.real r)
  if m < tr.mints.length then
    let x := P.nodes.idxOf (.const (SP.sig.decls.length + m))
    if x < P.nodes.length then some x else none
  else none

/-! ## Intervals of lowered integers -/

/-- The width of a lowered node of a bit-vector: of its sort, or of a
    surface node it lowers. -/
def Trace.bvWidth (l : Nat) : Option Nat :=
  match SP.sortWidth ((Tab.at P.sortOf (l)).getD 0) with
  | some w => some w
  | none => (List.range SP.nodes.length).findSome? fun i => if tr.at i == l then SP.width i else none

/-- The interval of a linear combination, from those of its unknowns. -/
def linIv (leaf : Nat → Option (Int × Int)) : Lia.Form → Option (Int × Int)
  | [] => some (0, 0)
  | (u, a) :: f =>
    if a.den = 1 then
      match leaf u, linIv leaf f with
      | some (l, h), some (L, H) => if 0 ≤ a.num then some (a.num * l + L, a.num * h + H) else some (a.num * h + L, a.num * l + H)
      | _, _ => none
    else none

/-- The interval of lowered node `x`, from those of its unknowns. -/
def nodeIv (leaf : Nat → Option (Int × Int)) (x : Nat) : Option (Int × Int) :=
  (linIv leaf (lin P.nodes x).1).map fun p => (p.1 + (lin P.nodes x).2, p.2 + (lin P.nodes x).2)

/-- Whether lowered node `x` is of sort `Int`. -/
def isIntN (x : Nat) : Bool := P.sig.is (P.sortOf[x]?.getD 0) .int

/-- The constraint `g + gc ≥ 0` a comparison of integers `x` gives when it
    holds. -/
def condAtom (x : Nat) : List (Lia.Form × Int) :=
  match Tab.at P.nodes (x) with
  | some (.le a b) =>
    if isIntN P a && isIntN P b then [((lin P.nodes b).1 ++ Lia.neg (lin P.nodes a).1, (lin P.nodes b).2 - (lin P.nodes a).2)]
    else []
  | _ => []

/-- The constraints `g + gc ≥ 0` the formula `c` gives, or its negation: those
    of comparisons of integers. -/
def condCons (c : Nat) (pos : Bool) : List (Lia.Form × Int) :=
  if pos then
    match Tab.at P.nodes (c) with
    | some (.and xs) => xs.flatMap (condAtom P)
    | _ => condAtom P c
  else
    match Tab.at P.nodes (c) with
    | some (.le a b) =>
      if isIntN P a && isIntN P b then [((lin P.nodes a).1 ++ Lia.neg (lin P.nodes b).1, (lin P.nodes a).2 - (lin P.nodes b).2 - 1)]
      else []
    | _ => []

/-- The interval of a linear combination `f` narrowed by constraints: `f` is
    at least `-gc` more than `g`, or at most `gc` less than `-g`. -/
def refine (f : Lia.Form × Int) (cons : List (Lia.Form × Int)) (i : Option (Int × Int)) : Option (Int × Int) :=
  cons.foldl (fun acc gc => acc.map fun p =>
    (if (canon (f.1 ++ Lia.neg gc.1)).isEmpty then max p.1 (f.2 - gc.2) else p.1,
     if (canon (f.1 ++ gc.1)).isEmpty then min p.2 (f.2 + gc.2) else p.2)) i

def ivHull : Option (Int × Int) → Option (Int × Int) → Option (Int × Int)
  | some (a, b), some (c, d) => some (min a c, max b d)
  | _, _ => none

def ivSub (i : Option (Int × Int)) (lo hi : Int) : Bool :=
  match i with
  | some (a, b) => lo ≤ a && b ≤ hi
  | none => false

/-- The interval of branch `t` of `cases` when `c` is `pos`. -/
def branchIv (node : Nat → Option (Int × Int)) (c t : Nat) (pos : Bool) : Option (Int × Int) :=
  refine (lin P.nodes t) (condCons P c pos) (node t)

/-- The interval of symbol `j` of a rule, from those of the nodes. -/
def Rule.iv (node : Nat → Option (Int × Int)) : Rule → Nat → Option (Int × Int)
  | .modulo _ w _ _, 0 => some (0, 2 ^ w - 1)
  | .modulo v w _ _, _ => (node v).map fun p => (p.1 / 2 ^ w, p.2 / 2 ^ w)
  | .cases c t e _ _, _ => ivHull (branchIv P node c t true) (branchIv P node c e false)
  | .divide v d _, 0 => if 0 < d then (node v).map fun p => (p.1 / d, p.2 / d) else none
  | .divide _ d _, _ => if 0 < d then some (0, d - 1) else none
  | .sdivide t w d fl, 0 =>
    if 0 < d && 0 < w && ivSub (node t) 0 (2 ^ w - 1) then
      let half : Int := 2 ^ (w - 1)
      if fl then some ((-half) / d, (half - 1) / d)
      else some (-(half / d), (half - 1) / d)
    else none
  | .sdivide _ _ d fl, _ => if 0 < d then (if fl then some (0, d - 1) else some (-(d - 1), d - 1)) else none
  | .int2bv _ w, 0 => some (0, 2 ^ w - 1)
  | .int2bv _ _, _ => none
  | .smodz .., _ => some (0, 1)
  | .bits .., _ => some (0, 1)
  | .udiv _ _ w, _ => some (0, 2 ^ w - 1)

/-- The interval of a leaf: a number, a symbol of a rule (`sym`), or a
    bit-vector. -/
def Trace.leafIv (sym : Rule → Nat → Option (Int × Int)) (l : Nat) : Option (Int × Int) :=
  match Tab.at P.nodes (l) with
  | some (.num v) => some (v, v)
  | some _ =>
    match tr.symAt SP P l with
    | some (r, j) => sym r j
    | none => (tr.bvWidth SP P l).map fun w => (0, 2 ^ w - 1)
  | none => none

/-- The interval of symbol `j` of a rule from the intervals `node` of its
    arguments alone, whatever the truth of its conditions, if it has one. -/
def Rule.fixedIv (node : Nat → Option (Int × Int)) : Rule → Nat → Option (Int × Int)
  | .modulo _ w _ _, 0 => some (0, 2 ^ w - 1)
  | .cases _ t e _ _, _ => ivHull (node t) (node e)
  | .int2bv _ w, 0 => some (0, 2 ^ w - 1)
  | .smodz .., _ => some (0, 1)
  | .bits .., _ => some (0, 1)
  | .udiv _ _ w, _ => some (0, 2 ^ w - 1)
  | _, _ => none

/-- The order in which the ranges of lowered nodes follow from one another: by
    the depth of the rule symbols they depend on, then by number. -/
def Trace.mu (x : Nat) : Nat := depthOf (depths (tr.rank SP) P.nodes) x * P.nodes.length + x

/-- The interval of a leaf: a number, a rule symbol (`sym`), or a node of a
    bit-vector sort before `B` in the order `mu`. -/
def Trace.fixedLeaf (B : Nat) (sym : Rule → Nat → Option (Int × Int)) (l : Nat) : Option (Int × Int) :=
  match Tab.at P.nodes l with
  | some (.num v) => some (v, v)
  | some _ =>
    match tr.symAt SP P l with
    | some (r, j) => sym r j
    | none =>
      if tr.mu SP P l < B then (SP.sortWidth ((Tab.at P.sortOf l).getD 0)).map fun w => (0, 2 ^ w - 1)
      else none
  | none => none

/-- The intervals of the lowered nodes from those of numbers, rule symbols and
    nodes of bit-vector sorts before `B`, unfolding `n` rules deep: such as
    that of the sum of a bit-vector's bits, or of a sign extension. -/
def Trace.fixedAt (B : Nat) : Nat → Nat → Option (Int × Int)
  | 0 => nodeIv P (tr.fixedLeaf SP P B (Rule.fixedIv fun _ => none))
  | n + 1 => nodeIv P (tr.fixedLeaf SP P B (Rule.fixedIv (Trace.fixedAt B n)))

/-- The intervals of the lowered nodes, unfolding `n` rules deep. -/
def Trace.ivAt : Nat → Nat → Option (Int × Int)
  | 0 => nodeIv P (tr.leafIv SP P fun _ _ => none)
  | n + 1 => nodeIv P (tr.leafIv SP P (Rule.iv P (Trace.ivAt n)))

def Trace.iv (x : Nat) : Option (Int × Int) := tr.ivAt SP P (tr.mints.length + 1) x

/-! ## The facts of rules -/

/-- `lo ≤ k ≤ hi`. -/
def intS (k : Nat) (lo hi : Int) : List Shape := [.le (.num [] lo) (.same k), .le (.same k) (.num [] hi)]

/-- `a = b` on integers. -/
def eqI (a b : Shape) : Shape := .and [.le a b, .le b a]

/-- The facts of rule `r`, its symbols at nodes `ks`, `aux` the node of the
    signed value of `sdivide` or of the remainder of `smodz`. -/
def Rule.facts (ks : List Nat) (aux : Nat) : Rule → List Shape
  | .modulo v w lo hi =>
    let m : Int := 2 ^ w
    let r := ks.getD 0 0
    intS r 0 (m - 1) ++
      if hi - lo < 4 then
        [.or ((List.range (hi - lo + 1).toNat).map fun (i : Nat) => eqI (.same v) (.num [(r, 1)] ((lo + (i : Int)) * m)))]
      else
        let q := ks.getD 1 0
        intS q lo hi ++ [eqI (.same v) (.num [(r, 1), (q, (m : Rat))] 0)]
  | .cases c t e lo hi =>
    let k := ks.getD 0 0
    intS k lo hi ++ [.implies (.bool c) (eqI (.same k) (.same t)), .implies (.not (.bool c)) (eqI (.same k) (.same e))]
  | .divide v d qmax =>
    let q := ks.getD 0 0
    let r := ks.getD 1 0
    intS q 0 qmax ++ intS r 0 (d - 1) ++ [eqI (.same v) (.num [(q, (d : Rat)), (r, 1)] 0)]
  | .sdivide t w d fl =>
    let q := ks.getD 0 0
    let r := ks.getD 1 0
    let half : Int := 2 ^ (w - 1)
    intS q (-(half / d) - 1) ((half - 1) / d) ++ intS r (if fl then 0 else -(d - 1)) (d - 1) ++
      [eqI (.same aux) (.num [(q, (d : Rat)), (r, 1)] 0)] ++
      if fl then []
      else [.implies (negS P t w) (.le (.same r) (.num [] 0)), .implies (.not (negS P t w)) (.le (.num [] 0) (.same r))]
  | .int2bv t w =>
    let k0 := ks.getD 0 0
    let k1 := ks.getD 1 0
    intS k0 0 (2 ^ w - 1) ++ [eqI (.same t) (.num [(k0, 1), (k1, ((2 ^ w : Int) : Rat))] 0)]
  | .smodz a c w =>
    let z := ks.getD 0 0
    let differ := if 0 < smodT c w then negS P a w else .not (negS P a w)
    let rz := eqI (.same aux) (.num [] 0)
    intS z 0 1 ++
      [.implies (.not differ) (eqI (.same z) (.num [] 0)), .implies rz (eqI (.same z) (.num [] 0)),
        .implies (.and [differ, .not rz]) (eqI (.same z) (.num [] 1))]
  | .bits t w =>
    (List.range w).flatMap (fun (j : Nat) => intS (ks.getD j 0) 0 1) ++
      [eqI (.same t) (.num ((List.range w).map fun (j : Nat) => (ks.getD j 0, ((2 ^ j : Int) : Rat))) 0)]
  | .udiv a b w =>
    let q := ks.getD 0 0
    let r := ks.getD 1 0
    let zero := eqI (.same b) (.num [] 0)
    intS q 0 (2 ^ w - 1) ++ intS r 0 (2 ^ w - 1) ++
      [.implies zero (.and [eqI (.same q) (.num [] (2 ^ w - 1)), eqI (.same r) (.same a)]),
        .implies (.not zero)
          (.and [eqI (.same a) (.num ((lin P.nodes aux).1 ++ [(r, 1)]) (lin P.nodes aux).2), .le (.num [(r, 1)] 1) (.same b)])]

/-- Whether node `x` is `signed(t, w)`: the constant, or the `cases` tagged
    `signed`. -/
def Trace.signedOk (t w x : Nat) : Bool :=
  match Tab.at P.nodes (t) with
  | some (.num v) => Tab.at P.nodes (x) == some (.num (signedI w v))
  | _ =>
    match tr.symAt SP P x with
    | some (.cases c thn els lo hi, 0) =>
      lo == -(2 ^ (w - 1)) && hi == 2 ^ (w - 1) - 1 && fits P.sig P.nodes P.sortOf c (negS P t w) &&
        fits P.sig P.nodes P.sortOf thn (.num (lin P.nodes t).1 ((lin P.nodes t).2 - 2 ^ w)) && els == t
    | _ => false

/-- `Σ_{j<k} 2^(j·w) · p`: `p` repeated `k` times. -/
def repeatForm (w : Nat) (p : Lia.Form × Int) : Nat → Lia.Form × Int
  | 0 => ([], 0)
  | k + 1 =>
    let r := repeatForm w p k
    (r.1 ++ Lia.scale ((2 ^ (k * w) : Int) : Rat) p.1, r.2 + 2 ^ (k * w) * p.2)

/-- A signed comparison of the lowered nodes of `l` and `r`, of width `w`,
    from the unsigned one `u`: `(nl ∧ ¬nr) ∨ ((nl ↔ nr) ∧ u)`. -/
def signedS (w l r : Nat) (u : Shape) : Shape :=
  .or [.and [negS P (tr.at l) w, .not (negS P (tr.at r) w)],
    .and [.iff (negS P (tr.at l) w) (negS P (tr.at r) w), u]]

/-- A comparison of bit-vectors of width `w`. -/
def cmpS (op : BvCmp) (w a b : Nat) : Shape :=
  match op with
  | .ult => ltInt P tr a b
  | .ule => .le (.same (tr.at a)) (.same (tr.at b))
  | .ugt => ltInt P tr b a
  | .uge => .le (.same (tr.at b)) (.same (tr.at a))
  | .slt => signedS P tr w a b (ltInt P tr a b)
  | .sle => signedS P tr w a b (.le (.same (tr.at a)) (.same (tr.at b)))
  | .sgt => signedS P tr w b a (ltInt P tr b a)
  | .sge => signedS P tr w b a (.le (.same (tr.at b)) (.same (tr.at a)))

/-- Whether the lowered symbol `k` is minted for the `ite` at `i`, or one
    before it with the same lowered children. -/
def Trace.iteOf (k i : Nat) : Bool :=
  k ≥ SP.sig.decls.length &&
    match Tab.at tr.mints (k - SP.sig.decls.length), Tab.at SP.nodes (i) with
    | some (.ite i'), some (.ite c a b) =>
      i' ≤ i &&
        match Tab.at SP.nodes (i') with
        | some (.ite c' a' b') => tr.at c' == tr.at c && tr.at a' == tr.at a && tr.at b' == tr.at b
        | _ => false
    | _, _ => false

/-- Whether the lowered symbol `n` is minted for the store of surface sort `s`. -/
def Trace.storeOf (n s : Nat) : Bool :=
  n ≥ SP.sig.decls.length && Tab.at tr.mints (n - SP.sig.decls.length) == some (.store s)

/-- The shape of the lowering of surface node `i`. -/
def expect (i : Nat) : Option Shape :=
  let T := tr.at
  let L := leaf SP tr
  let F := form tr
  match Tab.at SP.nodes (i) with
  | none => none
  | some n =>
  match n with
  | .const k => if k < SP.sig.decls.length then some (.const k) else none
  | .app f args => some (.app (.same (T f)) (args.map L))
  | .num v => some (.num [] v)
  | .tt => some .tt
  | .ff => some .ff
  | .not a => some (.not (F a))
  | .and as => some (.and (as.map F))
  | .or as => some (.or (as.map F))
  | .implies as => impliesS (as.map F)
  | .xor as => xorS (as.map F)
  | .iff as => some (chainS ((consec as).map fun p => .iff (F p.1) (F p.2)))
  | .eq as =>
    match as with
    | [] => none
    | a :: _ =>
      if SP.isBool a then none
      else some (chainS ((consec as).map fun p => eqS (SP.isArith a) (.same (T p.1)) (.same (T p.2))))
  | .distinct as =>
    match as with
    | [] => none
    | a :: _ =>
      if SP.isBool a then none
      else if SP.isIntLike a then
        some (.and ((allPairs as).map fun p => .or [ltInt P tr p.1 p.2, ltInt P tr p.2 p.1]))
      else if SP.isNum a then
        some (.and ((allPairs as).map fun p => .or [.lt (.same (T p.1)) (.same (T p.2)), .lt (.same (T p.2)) (.same (T p.1))]))
      else some (.and ((allPairs as).map fun p => .not (.eq (.same (T p.1)) (.same (T p.2)))))
  | .le as => some (chainS ((consec as).map fun p => .le (.same (T p.1)) (.same (T p.2))))
  | .ge as => some (chainS ((consec as).map fun p => .le (.same (T p.2)) (.same (T p.1))))
  | .lt as =>
    if as.all SP.isInt then some (chainS ((consec as).map fun p => ltInt P tr p.1 p.2))
    else some (chainS ((consec as).map fun p => .lt (.same (T p.1)) (.same (T p.2))))
  | .gt as =>
    if as.all SP.isInt then some (chainS ((consec as).map fun p => ltInt P tr p.2 p.1))
    else some (chainS ((consec as).map fun p => .lt (.same (T p.2)) (.same (T p.1))))
  | .ite c a b =>
    if SP.isBool i then some (.ite (F c) (F a) (F b))
    else
      match Tab.at P.nodes (T i) with
      | some (.const k) => if tr.iteOf SP k i then some (.const k) else none
      | _ => none
  | .add as => some (.num (sumForms (as.map (linOf P tr))).1 (sumForms (as.map (linOf P tr))).2)
  | .sub as =>
    match as with
    | [] => some (.num [] 0)
    | a :: rest =>
      let r := sumForms (rest.map (linOf P tr))
      some (.num ((linOf P tr a).1 ++ Lia.neg r.1) ((linOf P tr a).2 - r.2))
  | .neg a => some (.num (Lia.neg (linOf P tr a).1) (-(linOf P tr a).2))
  | .mul as => (mulForms (as.map (linOf P tr))).map fun p => .num p.1 p.2
  | .select a x => some (.app (.same (T a)) [L x])
  | .store a x v =>
    match Tab.at P.nodes (T i) with
    | some (.app g _) =>
      match Tab.at P.nodes (g) with
      | some (.const n) => if tr.storeOf SP n (SP.sort a) then some (.app (.const n) [L a, L x, L v]) else none
      | _ => none
    | _ => none
  | .bvlit w v => if v < 2 ^ w then some (.num [] v) else none
  | .bvun op w a =>
    match op with
    | .not => some (.num (Lia.neg (linOf P tr a).1) (2 ^ w - 1 - (linOf P tr a).2))
    | .zeroExtend _ => some (.same (T a))
    | .repeat k => some (.num (repeatForm w (linOf P tr a) k).1 (repeatForm w (linOf P tr a) k).2)
    | .rotateLeft k | .rotateRight k => if k % w = 0 then some (.same (T a)) else none
    | .extract i j => if j = 0 && i + 1 = w then some (.same (T a)) else none
    | .signExtend k => if k = 0 then some (.same (T a)) else none
    | .neg => none
  | .concat _ wb a b =>
    some (.num (Lia.scale ((2 ^ wb : Int) : Rat) (linOf P tr a).1 ++ (linOf P tr b).1)
      (2 ^ wb * (linOf P tr a).2 + (linOf P tr b).2))
  | .bv2int false _ a => some (.same (T a))
  | .bv2int true _ _ => none
  | .bvcmp op w a b => if w = 0 then none else some (cmpS P tr op w a b)
  | .bvbin _ _ _ _ => none
  | .int2bv _ _ => none
  | .rat .. | .div _ | .toReal _ | .toInt _ | .isInt _ | .letIn .. | .bound _ => none

/-! ## Operations through rules -/

/-- The constant a linear combination stands for, if it has no unknowns. -/
def constOf (f : Lia.Form × Int) : Option Int := if (canon f.1).isEmpty then some f.2 else none

/-- A unary operation on a constant bit-vector. -/
def bvunConst (op : BvUn) (w : Nat) (a : Int) : Int := Vik.val (op.apply (BitVec.ofInt w a))

/-- A binary operation on constant bit-vectors. -/
def bvbinConst (op : BvBin) (w : Nat) (a b : Int) : Int :=
  Vik.val (op.apply (BitVec.ofInt w a) (BitVec.ofInt w b))

/-- Whether node `l` is `v mod 2^w`, `f` the linear combination of `v`: the
    constant, or the remainder of a `modulo` of a node of shape `f`. -/
def Trace.modOk (l : Nat) (f : Lia.Form × Int) (w : Nat) : Bool :=
  match constOf f with
  | some c => Tab.at P.nodes (l) == some (.num (c % 2 ^ w))
  | none =>
    match tr.symAt SP P l with
    | some (.modulo v w' _ _, 0) => w' == w && fits P.sig P.nodes P.sortOf v (.num f.1 f.2)
    | _ => false

/-- Whether node `l` is the quotient (`j = 0`) or the remainder (`j = 1`) of
    `v` by `d`, `f` the linear combination of `v`. -/
def Trace.divOk (l : Nat) (f : Lia.Form × Int) (d : Int) (j : Nat) : Bool :=
  match constOf f with
  | some c => Tab.at P.nodes (l) == some (.num (if j = 0 then c / d else c % d))
  | none =>
    match tr.symAt SP P l with
    | some (.divide v d' _, j') => d' == d && j' == j && fits P.sig P.nodes P.sortOf v (.num f.1 f.2)
    | _ => false

/-- Whether node `l` is the symbol of a `cases` on the formula `c`, between
    the linear combinations `thn` and `els`. -/
def Trace.casesOk (l : Nat) (c : Shape) (thn els : Lia.Form × Int) : Bool :=
  match tr.symAt SP P l with
  | some (.cases c' t e _ _, 0) =>
    fits P.sig P.nodes P.sortOf c' c && fits P.sig P.nodes P.sortOf t (.num thn.1 thn.2) &&
      fits P.sig P.nodes P.sortOf e (.num els.1 els.2)
  | _ => false

/-- A symbol as a linear combination. -/
def symForm (x : Option Nat) (a : Rat) : Lia.Form := match x with
  | some x => [(x, a)]
  | none => []

/-- `bvsdiv`, `bvsrem` and `bvsmod` of the lowered node `t` by the constant
    `c`, at node `l`. -/
def Trace.sdivOk (op : BvBin) (w l t : Nat) (c : Int) : Bool :=
  let T := smodT c w
  if T = 0 then
    match op with
    | .sdiv => tr.casesOk SP P l (negS P t w) ([], 1) ([], 2 ^ w - 1)
    | _ => l == t
  else
    let r := Rule.sdivide t w T.natAbs false
    match tr.symNode SP P r 0, tr.symNode SP P r 1 with
    | some q, some rm =>
      match op with
      | .sdiv => tr.modOk SP P l ([(q, if 0 < T then 1 else -1)], 0) w
      | .srem => tr.modOk SP P l ([(rm, 1)], 0) w
      | _ =>
        match tr.symNode SP P (.smodz t c w) 0 with
        | some z => tr.modOk SP P l ([(rm, 1), (z, (T : Rat))], 0) w
        | none => false
    | _, _ => false

/-- `bvashr` of the lowered node `t` by the constant `c`, at node `l`. -/
def Trace.ashrOk (w l t : Nat) (c : Int) : Bool :=
  match tr.symAt SP P l with
  | some (.modulo v w' _ _, 0) =>
    w' == w &&
      if w ≤ c then tr.casesOk SP P v (negS P t w) ([], -1) ([], 0)
      else tr.symAt SP P v == some (.sdivide t w (2 ^ c.toNat) true, 0)
  | _ => false

/-- The quotient of `extract`, `t` divided by `2^j`, at node `x`. -/
def Trace.extractQ (t : Nat) (f : Lia.Form × Int) (j x : Nat) : Bool :=
  if j = 0 then x == t else tr.divOk SP P x f (2 ^ j) 0

/-- A rotation of the lowered node `t` to the left by `0 < s < w`, at node
    `l`: `2^s·r + q` for `t = 2^(w-s)·q + r`. -/
def Trace.rotOk (l t w s : Nat) : Bool :=
  0 < s && s < w &&
    let r := Rule.divide t (2 ^ (w - s)) (2 ^ s - 1)
    match tr.symNode SP P r 0, tr.symNode SP P r 1 with
    | some q, some rm => fits P.sig P.nodes P.sortOf l (.num [(rm, ((2 ^ s : Int) : Rat)), (q, ((1 : Int) : Rat))] 0)
    | _, _ => false

/-! ## Bits -/

/-- A bit as the lowering builds one: a literal, a symbol `k` in `{0, 1}` (a
    bit of `bits`, or a `cases` between `1` and `0`), or the negation of a bit. -/
inductive BitRef where
  | lit (b : Bool)
  | sym (k : Nat)
  | neg (r : BitRef)
  deriving DecidableEq, Repr

/-- `bitConstant`: a bit as a linear combination, `0` or `1`. -/
def BitRef.form : BitRef → Lia.Form × Int
  | .lit b => ([], if b then 1 else 0)
  | .sym k => ([(k, 1)], 0)
  | .neg r => (Lia.neg r.form.1, 1 - r.form.2)

/-- The complement of a bit. -/
def BitRef.flip : BitRef → BitRef
  | .lit b => .lit !b
  | .neg r => r
  | r => .neg r

/-- `fromBits`: `Σ_{i<n} 2^i · bit i`. -/
def bitsForm (d : Nat → BitRef) : Nat → Lia.Form × Int
  | 0 => ([], 0)
  | n + 1 =>
    let g := bitsForm d n
    let f := (d n).form
    (g.1 ++ Lia.scale ((2 ^ n : Int) : Rat) f.1, g.2 + 2 ^ n * f.2)

/-- Bit `i` of a list of bits. -/
def bitAt (rs : List BitRef) (i : Nat) : BitRef := rs.getD i (.lit false)

/-- The bits of a sum `Σ 2^i · bit i`, read off its terms: `2^i · k` is the
    symbol `k`, `-2^i · k` its negation, and what is left of the constant
    gives the literal bits. `Trace.sumOk` checks the reading. -/
def decodeBits (f : Lia.Form × Int) (w : Nat) : List BitRef :=
  let g := canon f.1
  let base (i : Nat) : Option BitRef :=
    match g.find? (fun p => p.2 == ((2 ^ i : Int) : Rat) || p.2 == -((2 ^ i : Int) : Rat)) with
    | some (k, a) => some (if 0 < a then .sym k else .neg (.sym k))
    | none => none
  let negW : Int := (List.range w).foldl (fun s i => match base i with
    | some (.neg _) => s + 2 ^ i
    | _ => s) 0
  (List.range w).map fun i => (base i).getD (.lit (bit (f.2 - negW) i == 1))

/-- The two gates of a bitwise operation, folded on literals and equal bits. -/
inductive Gate where
  | ref (r : BitRef)
  | and (r s : BitRef)
  | or (r s : BitRef)
  | xor (r s : BitRef)

/-- `gate`: bit `i` of a bitwise operation of bits `x` and `y`. -/
def gateOf (op : BvBin) (x y : BitRef) : Gate :=
  match op with
  | .and =>
    if x = .lit true then .ref y else if y = .lit true then .ref x
    else if x = .lit false ∨ y = .lit false then .ref (.lit false)
    else if x = y then .ref x else .and x y
  | .or =>
    if x = .lit true ∨ y = .lit true then .ref (.lit true)
    else if x = .lit false then .ref y else if y = .lit false then .ref x
    else if x = y then .ref x else .or x y
  | _ =>
    if x = .lit true then .ref (.neg y) else if y = .lit true then .ref (.neg x)
    else if x = .lit false then .ref y else if y = .lit false then .ref x
    else if x = y then .ref (.lit false) else .xor x y

/-- The operation of the bits of a bitwise operation, and whether its result
    is complemented. -/
def bitwiseOf : BvBin → Option (BvBin × Bool)
  | .and => some (.and, false)
  | .or => some (.or, false)
  | .xor => some (.xor, false)
  | .nand => some (.and, true)
  | .nor => some (.or, true)
  | .xnor => some (.xor, true)
  | _ => none


/-- Whether `k` is the symbol of a `cases` between `1` and `0`, on a formula
    `c` for which `p c` holds. -/
def Trace.casesBit (k : Nat) (p : Nat → Bool) : Bool :=
  match tr.symAt SP P k with
  | some (.cases c t e _ _, 0) => fits P.sig P.nodes P.sortOf t (.num [] 1) && fits P.sig P.nodes P.sortOf e (.num [] 0) && p c
  | _ => false

/-- Whether node `k` is in `{0, 1}`: a bit of `bits`, or a `cases` between `1`
    and `0`. -/
def Trace.bitSym (k : Nat) : Bool :=
  match tr.symAt SP P k with
  | some (.bits _ _, _) => true
  | _ => tr.casesBit SP P k fun _ => true

def Trace.refOk : BitRef → Bool
  | .lit _ => true
  | .sym k => tr.bitSym SP P k
  | .neg r => Trace.refOk r

/-- Whether lowered node `t` is the sum of bits `rs`. -/
def Trace.sumOk (t : Nat) (rs : List BitRef) : Bool :=
  rs.all (tr.refOk SP P) &&
    fits P.sig P.nodes P.sortOf t (.num (bitsForm (bitAt rs) rs.length).1 (bitsForm (bitAt rs) rs.length).2)

/-- The bits of `bits(u, w)`, if the trace mints them. -/
def Trace.decomp (u w : Nat) : Option (List BitRef) :=
  ((List.range w).mapM fun j => tr.symNode SP P (.bits u w) j).map (·.map .sym)

/-- `knownBits`: the bits of the lowered node `t` of width `w`: a constant's,
    a sum of bits, the decomposition of `t`, or the complement of a
    decomposition. -/
def Trace.tbits (t w : Nat) : Option (List BitRef) :=
  let f := lin P.nodes t
  match constOf f with
  | some v => some ((List.range w).map fun i => .lit (bit v i == 1))
  | none =>
    let d := decodeBits f w
    if tr.sumOk SP P t d then some d
    else
      match tr.decomp SP P t w with
      | some rs => some rs
      | none =>
        match canon f.1 with
        | [(u, a)] =>
          if a == -1 && f.2 == 2 ^ w - 1 && isIntN P u then (tr.decomp SP P u w).map (·.map .neg) else none
        | _ => none

/-- Whether formula node `x` has the truth of bit `r`. -/
def Trace.refFits (x : Nat) : BitRef → Bool
  | .lit b => Tab.at P.nodes (x) == some (if b then .tt else .ff)
  | .sym k => fits P.sig P.nodes P.sortOf x (.le (.num [] 1) (.same k)) || tr.casesBit SP P k (· == x)
  | .neg r =>
    match Tab.at P.nodes (x) with
    | some (.not y) => Trace.refFits y r
    | _ => false

/-- Whether bit `d` has the truth of bit `r`: the same bit, a `cases` on a
    formula of `r`, or negations of such bits. -/
def Trace.refMatch : BitRef → BitRef → Bool
  | d, r =>
    d == r ||
      match d, r with
      | .sym k, r => tr.casesBit SP P k fun c => tr.refFits SP P c r
      | .neg d', .neg r' => Trace.refMatch d' r'
      | _, _ => false

/-- Formula nodes `p` and `q` have the truths of `r` and `s`, in either order. -/
def Trace.pairFits (p q : Nat) (r s : BitRef) : Bool :=
  (tr.refFits SP P p r && tr.refFits SP P q s) || (tr.refFits SP P p s && tr.refFits SP P q r)

/-- Whether bit `d` is the gate of `op` on bits `x` and `y`. -/
def Trace.gateOk (op : BvBin) (x y d : BitRef) : Bool :=
  match gateOf op x y with
  | .ref r => tr.refMatch SP P d r
  | .and r s =>
    match d with
    | .sym k => tr.casesBit SP P k fun c =>
      match Tab.at P.nodes (c) with
      | some (.and [p, q]) => tr.pairFits SP P p q r s
      | _ => false
    | _ => false
  | .or r s =>
    match d with
    | .sym k => tr.casesBit SP P k fun c =>
      match Tab.at P.nodes (c) with
      | some (.or [p, q]) => tr.pairFits SP P p q r s
      | _ => false
    | _ => false
  | .xor r s =>
    match d with
    | .sym k => tr.casesBit SP P k fun c =>
      match Tab.at P.nodes (c) with
      | some (.not z) =>
        match Tab.at P.nodes (z) with
        | some (.iff p q) => tr.pairFits SP P p q r s
        | _ => false
      | _ => false
    | _ => false

/-- `masked`: the bitwise operation `op` of the lowered node `t` (of linear
    combination `f`) with a mask of a run of low or high ones. -/
def Trace.maskForm (op : BvBin) (t : Nat) (f : Lia.Form × Int) (mask : Int) (w : Nat) :
    Option (Lia.Form × Int) :=
  match (List.range (w + 1)).find? (fun k => mask == 2 ^ k - 1 || mask == 2 ^ w - 2 ^ k) with
  | none => none
  | some k =>
    let low : Option (Lia.Form × Int) :=
      if k = w then some f
      else if k = 0 then some ([], 0)
      else (tr.symNode SP P (.divide t (2 ^ k) (2 ^ w / 2 ^ k - 1)) 1).map fun r => ([(r, 1)], 0)
    low.map fun lo =>
      let high : Lia.Form × Int := (f.1 ++ Lia.neg lo.1, f.2 - lo.2)
      let km : (Lia.Form × Int) × (Lia.Form × Int) := if mask == 2 ^ k - 1 then (high, lo) else (lo, high)
      match op with
      | .and => km.2
      | .or => (km.1.1, km.1.2 + mask)
      | _ => (km.1.1 ++ Lia.neg km.2.1, km.1.2 + mask - km.2.2)

/-- `masked` on whichever of `ta` and `tb` is a constant. -/
def Trace.maskedOf (op : BvBin) (w ta tb : Nat) : Option (Lia.Form × Int) :=
  match constOf (lin P.nodes tb) with
  | some c => tr.maskForm SP P op ta (lin P.nodes ta) c w
  | none =>
    match constOf (lin P.nodes ta) with
    | some c => tr.maskForm SP P op tb (lin P.nodes tb) c w
    | none => none

/-- A bitwise operation `op` of the lowered nodes `ta` and `tb`, at node `l`:
    through a mask, or bit by bit. -/
def Trace.bitwiseOk (op : BvBin) (w l ta tb : Nat) : Bool :=
  match bitwiseOf op with
  | none => false
  | some (op', neg) =>
    let viaMask :=
      match tr.maskedOf SP P op' w ta tb with
      | some E =>
        fits P.sig P.nodes P.sortOf l (if neg then .num (Lia.neg E.1) (2 ^ w - 1 - E.2) else .num E.1 E.2)
      | none => false
    viaMask ||
      match tr.tbits SP P ta w, tr.tbits SP P tb w with
      | some A, some B =>
        let D := decodeBits (lin P.nodes l) w
        A.length == w && B.length == w && tr.sumOk SP P l D &&
          (List.range w).all fun i =>
            tr.gateOk SP P op' (bitAt A i) (bitAt B i) (if neg then (bitAt D i).flip else bitAt D i)
      | _, _ => false



/-- `same`: formula node `x` is `f ↔ g` for the bits `r` and `s`, folded on
    literals and equal bits. -/
def Trace.sameOk (x : Nat) (r s : BitRef) : Bool :=
  if r = .lit true then tr.refFits SP P x s
  else if s = .lit true then tr.refFits SP P x r
  else if r = .lit false then tr.refFits SP P x (.neg s)
  else if s = .lit false then tr.refFits SP P x (.neg r)
  else if r = s then Tab.at P.nodes (x) == some .tt
  else
    match Tab.at P.nodes (x) with
    | some (.iff p q) => tr.refFits SP P p r && tr.refFits SP P q s
    | _ => false

/-- `equal` bit by bit: formula node `x` is the conjunction of `same` on the
    bits of the lowered nodes `ta` and `tb`, of width `w`. -/
def Trace.bitEqOk (x ta tb w : Nat) : Bool :=
  match tr.tbits SP P ta w, tr.tbits SP P tb w, Tab.at P.nodes (x) with
  | some A, some B, some (.and xs) =>
    A.length == w && B.length == w && xs.length == w &&
      (List.range w).all fun i => tr.sameOk SP P (xs.getD i 0) (bitAt A i) (bitAt B i)
  | _, _, _ => false

/-- `equal` of the surface bit-vectors `a` and `b` of width `w`, at formula
    node `x`: two bounds, or bit by bit. -/
def Trace.pairEqOk (w x a b : Nat) : Bool :=
  fits P.sig P.nodes P.sortOf x (eqS true (.same (tr.at a)) (.same (tr.at b))) ||
    tr.bitEqOk SP P x (tr.at a) (tr.at b) w

/-- One condition of `chainOk`: `equal`, or its negation. -/
def Trace.pairCondOk (w : Nat) (neg : Bool) (x : Nat) (p : Nat × Nat) : Bool :=
  if neg then
    match Tab.at P.nodes (x) with
    | some (.not z) => tr.pairEqOk SP P w z p.1 p.2
    | _ => false
  else tr.pairEqOk SP P w x p.1 p.2

/-- `chain` of `equal` (or of its negation) on the pairs `ps`, at node `x`. -/
def Trace.chainOk (w x : Nat) (ps : List (Nat × Nat)) (neg : Bool) : Bool :=
  match ps with
  | [p] => tr.pairCondOk SP P w neg x p
  | _ =>
    match Tab.at P.nodes (x) with
    | some (.and xs) =>
      xs.length == ps.length && (List.range ps.length).all fun j => tr.pairCondOk SP P w neg (xs.getD j 0) (ps.getD j (0, 0))
    | _ => false

/-- The node of the first symbol `0` of a rule satisfying `pred`. -/
def Trace.findSym (pred : Rule → Bool) : Option Nat :=
  match tr.mints.findIdx? (fun m => match m with
    | .rule r 0 => pred r
    | _ => false) with
  | some m =>
    let x := P.nodes.idxOf (.const (SP.sig.decls.length + m))
    if x < P.nodes.length then some x else none
  | none => none

/-- A partial product: `2^i · kept` when bit `r` is set, `0` otherwise (the
    `cases` tagged `part`). -/
def Trace.partialOf (kept : Nat) (r : BitRef) (i : Nat) : Option (Lia.Form × Int) :=
  let k := lin P.nodes kept
  let sh : Lia.Form × Int := (Lia.scale ((2 ^ i : Int) : Rat) k.1, 2 ^ i * k.2)
  match r with
  | .lit true => some sh
  | .lit false => some ([], 0)
  | _ =>
    (tr.findSym SP P fun rl => match rl with
      | .cases c t e _ _ =>
        tr.refFits SP P c r && fits P.sig P.nodes P.sortOf t (.num sh.1 sh.2) &&
          fits P.sig P.nodes P.sortOf e (.num [] 0)
      | _ => false).map fun x => ([(x, 1)], 0)

/-- The sum of the partial products of `kept` by the bits `B`, below `n`. -/
def Trace.partialForms (kept : Nat) (B : List BitRef) : Nat → Option (Lia.Form × Int)
  | 0 => some ([], 0)
  | n + 1 =>
    (Trace.partialForms kept B n).bind fun g =>
      (tr.partialOf SP P kept (bitAt B n) n).map fun f => (g.1 ++ f.1, g.2 + f.2)

/-- Whether node `v` is the exact product of `kept` by `blasted`, of width
    `w`: the sum of the partial products of `kept` by the bits of `blasted`. -/
def Trace.exactOk (v kept blasted w : Nat) : Bool :=
  match tr.tbits SP P blasted w with
  | some B =>
    B.length == w &&
      match tr.partialForms SP P kept B w with
      | some F => fits P.sig P.nodes P.sortOf v (.num F.1 F.2)
      | none => false
  | none => false

/-- `bvmul` of two unknowns at node `l`: the remainder of a `modulo` of the sum
    of the partial products of one operand by the bits of the other. -/
def Trace.productOk (w l ta tb : Nat) : Bool :=
  match tr.symAt SP P l with
  | some (.modulo v w' _ _, 0) => w' == w && (tr.exactOk SP P v ta tb w || tr.exactOk SP P v tb ta w)
  | _ => false

/-- Whether the arguments of a rule are within the bounds under which its
    facts hold. -/
def Trace.ruleOk (r : Rule) (aux : Nat) : Bool :=
  match r with
  | .modulo v w lo hi => isIntN P v && ivSub (tr.iv SP P v) (lo * 2 ^ w) ((hi + 1) * 2 ^ w - 1)
  | .cases c t e lo hi =>
    isIntN P t && isIntN P e && P.sig.is ((Tab.at P.sortOf (c)).getD 0) .bool &&
      ivSub (branchIv P (tr.iv SP P) c t true) lo hi && ivSub (branchIv P (tr.iv SP P) c e false) lo hi
  | .divide v d qmax => isIntN P v && 0 < d && ivSub (tr.iv SP P v) 0 (qmax * d + d - 1)
  | .sdivide t w d _ => isIntN P t && 0 < d && 0 < w && ivSub (tr.iv SP P t) 0 (2 ^ w - 1) && tr.signedOk SP P t w aux
  | .int2bv t _ => isIntN P t
  | .smodz a c w =>
    isIntN P a && 0 < w && smodT c w != 0 &&
      tr.symAt SP P aux == some (.sdivide a w (smodT c w).natAbs false, 1)
  | .bits t w => isIntN P t && ivSub (tr.iv SP P t) 0 (2 ^ w - 1)
  | .udiv a b w =>
    isIntN P a && isIntN P b && ivSub (tr.iv SP P a) 0 (2 ^ w - 1) && ivSub (tr.iv SP P b) 0 (2 ^ w - 1) &&
      aux < P.nodes.length &&
      match tr.symNode SP P (.udiv a b w) 0 with
      | some q => tr.exactOk SP P aux b q w
      | none => false

/-- The facts of the rule `r`, if its symbols have nodes. -/
def Trace.ruleFacts (r : Rule) (aux : Nat) : Option (List Shape) :=
  ((List.range r.nsyms).mapM fun j => tr.symNode SP P r j).map fun ks => r.facts P ks aux


/-- The number of stages of a barrel shifter of width `w`: the least `n` with
    `w ≤ 2^n`. -/
def stagesOf (w : Nat) : Nat := ((List.range (w + 1)).find? fun j => decide (w ≤ 2 ^ j)).getD 0

/-- A stage of a barrel shifter: `t` shifted by `2^j`, as `times`, `divide`, or
    `modulo` of the floor quotient of `sdivide`. -/
def Trace.stepNode (op : BvBin) (w t j : Nat) : Option Nat :=
  let d : Int := 2 ^ (2 ^ j)
  match op with
  | .shl =>
    match tr.findSym SP P fun r => match r with
      | .modulo v w' lo hi =>
        w' == w && lo == 0 && hi == d - 1 &&
          fits P.sig P.nodes P.sortOf v (.num (Lia.scale (d : Rat) (lin P.nodes t).1) (d * (lin P.nodes t).2))
      | _ => false with
    | some s => some s
    | none =>
      -- a constant shifted in range: the lowering folds it to a number
      match constOf (lin P.nodes t) with
      | some c =>
        let x := P.nodes.idxOf (.num (c * d))
        if 0 ≤ c * d && c * d < 2 ^ w && x < P.nodes.length then some x else none
      | none => none
  | .lshr => tr.symNode SP P (.divide t d (2 ^ w / d - 1)) 0
  | _ => (tr.symNode SP P (.sdivide t w d true) 0).bind fun q => tr.symNode SP P (.modulo q w (-1) 0) 0

/-- The first `j` stages of a barrel shifter of `ta` by the bits `B`. -/
def Trace.stageNode (op : BvBin) (w ta : Nat) (B : List BitRef) : Nat → Option Nat
  | 0 => some ta
  | j + 1 =>
    (Trace.stageNode op w ta B j).bind fun t =>
      if bitAt B j = .lit false then some t
      else
        (tr.stepNode SP P op w t j).bind fun s =>
          if bitAt B j = .lit true then some s
          else
            tr.findSym SP P fun r => match r with
              | .cases c th el _ _ => tr.refFits SP P c (bitAt B j) && th == s && el == t
              | _ => false

/-- The `far` condition of a shift by `tam` (bits `B`) with `n` stages, at
    formula node `c`: the bits from `n` on, and `w ≤ tam` when `w ≠ 2^n`. -/
def Trace.farOk (w n tam : Nat) (B : List BitRef) (c : Nat) : Bool :=
  let ge : Shape := .le (.num [] w) (.same tam)
  match Tab.at P.nodes (c) with
  | some (.or xs) =>
    (xs.all fun x => (List.range w).any (fun j => n ≤ j && tr.refFits SP P x (bitAt B j)) ||
      fits P.sig P.nodes P.sortOf x ge) &&
    ((List.range w).all fun j => j < n || bitAt B j == .lit false || xs.any fun x => tr.refFits SP P x (bitAt B j)) &&
    (2 ^ n == w || xs.any fun x => fits P.sig P.nodes P.sortOf x ge)
  | _ => false

/-- A shift of `ta` by the unknown `tam`, at node `l`: a barrel shifter over
    the bits of `tam`, and the value past the width when `tam` reaches it. -/
def Trace.shiftOk (op : BvBin) (w l ta tam : Nat) : Bool :=
  let n := stagesOf w
  match tr.tbits SP P tam w with
  | some B =>
    B.length == w && 0 < w &&
      match tr.stageNode SP P op w ta B n, tr.symAt SP P l with
      | some sh, some (.cases c th el _ _, 0) =>
        el == sh && tr.farOk SP P w n tam B c &&
          match op with
          | .ashr => tr.casesOk SP P th (negS P ta w) ([], 2 ^ w - 1) ([], 0)
          | _ => fits P.sig P.nodes P.sortOf th (.num [] 0)
      | _, _ => false
  | none => false

/-- Whether `x` is the magnitude of `t`, of width `w`: the `cases` tagged
    `abs`, `2^w - t` when `t` is negative, `t` otherwise. -/
def Trace.absOk (t w x : Nat) : Bool :=
  match tr.symAt SP P x with
  | some (.cases c th el _ _, 0) =>
    fits P.sig P.nodes P.sortOf c (negS P t w) &&
      fits P.sig P.nodes P.sortOf th (.num (Lia.neg (lin P.nodes t).1) (-(lin P.nodes t).2 + 2 ^ w)) &&
      fits P.sig P.nodes P.sortOf el (.num (lin P.nodes t).1 (lin P.nodes t).2)
  | _ => false

/-- Whether `k` is symbol `j` of the `udiv` of the magnitudes of `ta` and `tb`. -/
def Trace.magDivOk (ta tb w k j : Nat) : Bool :=
  match tr.symAt SP P k with
  | some (.udiv xa xb w', j') => j' == j && w' == w && tr.absOk SP P ta w xa && tr.absOk SP P tb w xb
  | _ => false

/-- The remainder of the magnitudes, `r`, if `rm` is the remainder of the sign
    of `ta`: the `cases` tagged `sremr`, `2^w - r` when `ta` is negative and
    `r ≥ 1`, `r` otherwise. -/
def Trace.sremOf (ta tb w rm : Nat) : Option Nat :=
  match tr.symAt SP P rm with
  | some (.cases c th r _ _, 0) =>
    if tr.magDivOk SP P ta tb w r 1 &&
        fits P.sig P.nodes P.sortOf c (.and [negS P ta w, .le (.num [] 1) (.same r)]) &&
        fits P.sig P.nodes P.sortOf th (.num [(r, -1)] (2 ^ w)) then some r
    else none
  | _ => none

/-- `bvsdiv`, `bvsrem` or `bvsmod` of two unknowns at node `l`: the unsigned
    division of the magnitudes, the signs SMT-LIB asks for, and the answer to a
    zero divisor. -/
def Trace.sdivUnknownOk (op : BvBin) (w l ta tb : Nat) : Bool :=
  let fit := fits P.sig P.nodes P.sortOf
  let na := negS P ta w
  let nb := negS P tb w
  match tr.symAt SP P l with
  | some (.cases c0 t0 e0 _ _, 0) =>
    0 < w && fit c0 (eqI (.same tb) (.num [] 0)) &&
      match op with
      | .sdiv =>
        (match tr.symAt SP P t0 with
          | some (.cases cn tn en _ _, 0) => fit cn na && fit tn (.num [] 1) && fit en (.num [] (2 ^ w - 1))
          | _ => false) &&
        (match tr.symAt SP P e0 with
          | some (.cases cq tq q _ _, 0) =>
            tr.magDivOk SP P ta tb w q 0 &&
              fit cq (.and [.not (.iff na nb), .le (.num [] 1) (.same q)]) && fit tq (.num [(q, -1)] (2 ^ w))
          | _ => false)
      | .srem => fit t0 (.num (lin P.nodes ta).1 (lin P.nodes ta).2) && (tr.sremOf SP P ta tb w e0).isSome
      | .smod =>
        fit t0 (.num (lin P.nodes ta).1 (lin P.nodes ta).2) &&
          match tr.symAt SP P e0 with
          | some (.cases cd td rm _ _, 0) =>
            match tr.sremOf SP P ta tb w rm, tr.symAt SP P td with
            | some r, some (.modulo v w' _ _, 0) =>
              w' == w && fit cd (.and [.not (.iff na nb), .not (eqI (.same r) (.num [] 0))]) &&
                fit v (.num ([(rm, 1)] ++ (lin P.nodes tb).1) (0 + (lin P.nodes tb).2))
            | _, _ => false
          | _ => false
      | _ => false
  | _ => false

/-- A binary bit-vector operation, not on two constants, at node `l`. -/
def Trace.binOk (op : BvBin) (w l a b : Nat) : Bool :=
  let fa := linOf P tr a
  let fb := linOf P tr b
  let isNum (c : Int) := Tab.at P.nodes (l) == some (.num c)
  match op with
  | .add => tr.modOk SP P l (fa.1 ++ fb.1, fa.2 + fb.2) w
  | .sub => tr.modOk SP P l (fa.1 ++ Lia.neg fb.1, fa.2 - fb.2) w
  | .mul =>
    match mul2 fa fb with
    | some p => tr.modOk SP P l p w
    | none => tr.productOk SP P w l (tr.at a) (tr.at b)
  | .comp =>
    tr.casesOk SP P l (eqI (.same (tr.at a)) (.same (tr.at b))) ([], 1) ([], 0) ||
      tr.casesBit SP P l fun c => tr.bitEqOk SP P c (tr.at a) (tr.at b) w
  | .and | .or | .xor | .nand | .nor | .xnor => tr.bitwiseOk SP P op w l (tr.at a) (tr.at b)
  | _ =>
    match constOf fb with
    | some c =>
      match op with
      | .shl =>
        if w ≤ c then isNum 0
        else tr.modOk SP P l (Lia.scale ((2 ^ c.toNat : Int) : Rat) fa.1, 2 ^ c.toNat * fa.2) w
      | .lshr => if w ≤ c then isNum 0 else tr.divOk SP P l fa (2 ^ c.toNat) 0
      | .udiv => if c = 0 then isNum (2 ^ w - 1) else tr.divOk SP P l fa c 0
      | .urem => if c = 0 then l == tr.at a else tr.divOk SP P l fa c 1
      | .sdiv | .srem | .smod => 0 < w && tr.sdivOk SP P op w l (tr.at a) c
      | .ashr => 0 < w && tr.ashrOk SP P w l (tr.at a) c
      | _ => false
    | none =>
      match op with
      | .shl | .lshr | .ashr => tr.shiftOk SP P op w l (tr.at a) (tr.at b)
      | .udiv => tr.symAt SP P l == some (.udiv (tr.at a) (tr.at b) w, 0)
      | .urem => tr.symAt SP P l == some (.udiv (tr.at a) (tr.at b) w, 1)
      | .sdiv | .srem | .smod => tr.sdivUnknownOk SP P op w l (tr.at a) (tr.at b)
      | _ => false

/-- The rational `p / q` (`q > 0`) that surface node `a` stands for when it is
    a literal: a `rat`, or a node whose lowering is a constant. -/
def Trace.litOf (a : Nat) : Option (Int × Nat) :=
  match Tab.at SP.nodes (a) with
  | some (.rat p q) => if 0 < q then some (p, q) else none
  | _ => if SP.isNum a then (constOf (linOf P tr a)).map fun c => (c, 1) else none

/-- Whether lowered node `l` is the rational `p / q`, `q > 0`: a number, or the
    symbol of `rat`. -/
def Trace.ratOk (l : Nat) (p : Int) (q : Nat) : Bool :=
  0 < q &&
    match Tab.at P.nodes (l) with
    | some (.num c) => c * q == p
    | _ =>
      match tr.realAt SP P l with
      | some (.rat p' q') => 0 < q' && p' * q == p * q'
      | _ => false

/-- Whether lowered node `l` is `p / q · t`, `q > 0`: an integer multiple of
    `t`, or the symbol of `ratmul`. -/
def Trace.ratmulOk (l : Nat) (p : Int) (q : Nat) (t : Nat) : Bool :=
  0 < q &&
    ((p % q == 0 &&
        fits P.sig P.nodes P.sortOf l
          (.num (Lia.scale ((p / q : Int) : Rat) (lin P.nodes t).1) (p / q * (lin P.nodes t).2))) ||
      match tr.realAt SP P l with
      | some (.ratmul p' q' t') => t' == t && 0 < q' && p' * q == p * q'
      | _ => false)

/-- The product `p / q` of the literal factors of a product, and its one
    factor that is not a literal, if any. -/
def Trace.mulLits (as : List Nat) : Option ((Int × Nat) × Option Nat) :=
  as.foldr
    (fun a r =>
      r.bind fun r =>
        match tr.litOf SP P a, r.2 with
        | some (pa, qa), o => some ((pa * r.1.1, qa * r.1.2), o)
        | none, none => some (r.1, some a)
        | none, some _ => none)
    (some ((1, 1), none))

/-- The defined symbol, the arguments, and whether it is an application, of a
    node that may use a definition. -/
def SProblem.callOf (n : SNode) : Option (Nat × List Nat × Bool) :=
  match n with
  | .const c => some (c, [], false)
  | .app f args =>
    match Tab.at SP.nodes (f) with
    | some (.const c) => some (c, args, true)
    | _ => none
  | _ => none

/-- `let`, its variables, and the uses of definitions, which the lowering
    inlines: the lowered node is that of the instance of the body. -/
def Trace.defOk (i : Nat) : Bool :=
  let l := tr.at i
  match Tab.at SP.nodes (i) with
  | some (.letIn _ b) => l == tr.at b
  | some (.bound d) => l == tr.at d
  | some n =>
    match SP.callOf n with
    | some (c, args, isApp) =>
      match SP.defs.find? (·.sym == c), tr.insts.lookup i with
      | some d, some ms =>
        isApp == !d.params.isEmpty && d.params.length == args.length && Surf.wellFormed d.nodes &&
          d.root < d.nodes.length &&
          (d.params.zip args).all (fun q => SP.sig.decls.getD q.1 0 == SP.sortOf.getD q.2 0) &&
          d.instOk SP.nodes args ms && ms.getD d.root 0 < i && l == tr.at (ms.getD d.root 0)
      | _, _ => false
    | none => false
  | none => false

/-- Whether the lowering of surface node `i`, an operation on reals, is the
    one the lowering gives it. -/
def Trace.realOk (i : Nat) : Bool :=
  let l := tr.at i
  match Tab.at SP.nodes (i) with
  | some (.rat p q) => tr.ratOk SP P l p q
  | some (.toReal a) => l == tr.at a
  | some (.toInt a) =>
    match tr.litOf SP P a with
    | some (p, q) => Tab.at P.nodes (l) == some (.num (p / q))
    | none => tr.realAt SP P l == some (.floor (tr.at a))
  | some (.isInt a) =>
    match tr.litOf SP P a with
    | some (p, q) => Tab.at P.nodes (l) == some (if p % q == 0 then .tt else .ff)
    | none =>
      match tr.realNode SP P (.floor (tr.at a)) with
      | some k => fits P.sig P.nodes P.sortOf l (eqI (.same (tr.at a)) (.same k))
      | none => false
  | some (.div [a, b]) =>
    match tr.litOf SP P b with
    | some (pb, qb) =>
      pb != 0 &&
        match tr.litOf SP P a with
        | some (pa, qa) => tr.ratOk SP P l (pa * qb * pb.sign) (qa * pb.natAbs)
        | none => tr.ratmulOk SP P l (qb * pb.sign) pb.natAbs (tr.at a)
    | none => false
  | some (.mul as) =>
    match tr.mulLits SP P as with
    | some ((p, q), none) => tr.ratOk SP P l p q
    | some ((p, q), some t) => tr.ratmulOk SP P l p q (tr.at t)
    | none => false
  | _ => tr.defOk SP i

/-- Whether the lowering of surface node `i`, a bit-vector operation, is the
    combination of rule symbols the lowering gives it. -/
def Trace.bvOk (i : Nat) : Bool :=
  let l := tr.at i
  let isNum (c : Int) := Tab.at P.nodes (l) == some (.num c)
  match Tab.at SP.nodes (i) with
  | some (.bvun op w a) =>
    let fa := linOf P tr a
    match constOf fa with
    | some ca => isNum (bvunConst op w ca)
    | none =>
      match op with
      | .neg => tr.modOk SP P l (Lia.neg fa.1, -fa.2) w
      | .extract hi lo =>
        lo ≤ hi && hi < w &&
          if hi + 1 = w then tr.extractQ SP P (tr.at a) fa lo l
          else
            match tr.symAt SP P l with
            | some (.divide v d _, 1) => d == 2 ^ (hi - lo + 1) && tr.extractQ SP P (tr.at a) fa lo v
            | _ => false
      | .rotateLeft k => tr.rotOk SP P l (tr.at a) w (k % w)
      | .rotateRight k => tr.rotOk SP P l (tr.at a) w ((w - k % w) % w)
      | .signExtend k =>
        0 < k && tr.casesOk SP P l (negS P (tr.at a) w) (fa.1, fa.2 + (2 ^ (w + k) - 2 ^ w)) fa
      | _ => false
  | some (.bvbin op w a b) =>
    let fa := linOf P tr a
    let fb := linOf P tr b
    match constOf fa, constOf fb with
    | some ca, some cb => isNum (bvbinConst op w ca cb)
    | _, _ => tr.binOk SP P op w l a b
  | some (.bv2int true w a) =>
    match constOf (linOf P tr a) with
    | some ca => 0 < w && isNum (signedI w ca)
    | none => 0 < w && tr.signedOk SP P (tr.at a) w l
  | some (.int2bv w a) =>
    match constOf (linOf P tr a) with
    | some ca => isNum (ca % 2 ^ w)
    | none => tr.symAt SP P l == some (.int2bv (tr.at a) w, 0)
  | some (.eq (a :: rest)) =>
    match SP.width a with
    | some w => tr.chainOk SP P w l (consec (a :: rest)) false
    | none => false
  | some (.distinct (a :: rest)) =>
    match SP.width a with
    | some w => tr.chainOk SP P w l (allPairs (a :: rest)) true
    | none => false
  | _ => tr.realOk SP P i

/-- The facts of the `ite` symbol `k`: `c → k = t`, or `¬c → k = e`. -/
def iteFact (k : Nat) (thn : Bool) : Option Shape :=
  if k < SP.sig.decls.length then none
  else
  match Tab.at tr.mints (k - SP.sig.decls.length) with
  | some (.ite i) =>
    match Tab.at SP.nodes (i) with
    | some (.ite c a b) =>
      if thn then some (.implies (form tr c) (eqS (SP.isArith i) (.const k) (.same (tr.at a))))
      else some (.implies (.not (form tr c)) (eqS (SP.isArith i) (.const k) (.same (tr.at b))))
    | _ => none
  | _ => none

/-! ## The checks -/

/-- Whether the surface sorts refer to declared sorts only. -/
def SProblem.sortsOk : Bool :=
  let n := SP.sig.sorts.length
  SP.sig.sorts.all (fun s =>
    match s with
    | .fn as r => as.all (· < n) && r < n
    | .array i e => i < n && e < n
    | _ => true) &&
  SP.sig.decls.all (· < n) && SP.sortOf.all (· < n) &&
  SP.datatypes.all fun (d, cs) =>
    d < n && SP.sig.sorts[d]? == some .user && cs.all fun (C, T, Ss) =>
      C < SP.sig.decls.length && T < SP.sig.decls.length && Ss.all (· < SP.sig.decls.length)

/-- Whether the lowered signature extends the surface one: its sorts lowered,
    then the sorts of stores; its symbols, then the minted ones. -/
def Trace.sigOk : Bool :=
  let ns := SP.sig.sorts.length
  P.sig.sorts.take ns == SP.sig.sorts.map lowerSort &&
  P.sig.decls.take SP.sig.decls.length == SP.sig.decls &&
  P.sig.decls.length == SP.sig.decls.length + tr.mints.length &&
  -- the sorts after those of the script are those of stores
  (List.range P.sig.sorts.length).all (fun s =>
    s < ns ||
      match Tab.at P.sig.sorts (s) with
      | some (.fn [arr, idx, el] arr') => arr' == arr && SP.sig.sorts[arr]? == some (.array idx el)
      | _ => false) &&
  -- each minted symbol, of the sort of its reason
  (List.range tr.mints.length).all (fun m =>
    let k := SP.sig.decls.length + m
    match Tab.at tr.mints (m) with
    | some (.ite i) =>
      (match Tab.at SP.nodes i with | some (.ite _ _ _) => true | _ => false) &&
        !SP.isBool i && Tab.at P.sig.decls (k) == some (SP.sort i)
    | some (.store s) =>
      match SP.sig.sorts[s]?, Tab.at P.sig.decls (k) with
      | some (.array idx el), some ds =>
        ns ≤ ds && Tab.at P.sig.sorts (ds) == some (.fn [s, idx, el] s) &&
          -- the only store of its sort
          (List.range tr.mints.length).all fun m' =>
            m' == m || match Tab.at tr.mints (m') with
              | some (.store _) => Tab.at P.sig.decls (SP.sig.decls.length + m') != some ds
              | _ => true
      | _, _ => false
    | some (.rule r j) =>
      (match Tab.at P.sig.decls (k) with
        | some s =>
          match SP.sig.sorts[s]? with
          | some .int => true
          | some (.bv w) =>
            r.bvOut j w || ivSub (r.fixedIv (tr.fixedAt SP P ((m + 1) * P.nodes.length) 2) j) 0 (2 ^ w - 1)
          | _ => false
        | none => false) &&
        r.args.all fun x => x < P.nodes.length && depthOf (depths (tr.rank SP) P.nodes) x ≤ m
    | some (.real r) =>
      (match Tab.at P.sig.decls (k) with
        | some s => SP.sig.sorts[s]? == some (if r.isInt then .int else .real)
        | none => false) &&
        r.args.all fun x => x < P.nodes.length && depthOf (depths (tr.rank SP) P.nodes) x ≤ m
    | some (.witness s) =>
      Tab.at P.sig.decls (k) == some s &&
        match SP.sig.sorts[s]? with
        | some .bool | some .int | some .real | some (.bv _) => true
        | _ => false
    | some (.pick i) => i < SP.nodes.length && Tab.at P.sig.decls (k) == some (SP.sort i)
    | none => false) &&
  P.stores.all (fun n => n ≥ SP.sig.decls.length &&
    match Tab.at tr.mints (n - SP.sig.decls.length) with
    | some (.store _) => true
    | _ => false) &&
  P.datatypes == SP.datatypes && P.bvIndex == SP.bvIndex &&
  -- the nodes of bit-vector sorts are symbols, applications, and numbers and
  -- sums in range
  (List.range P.nodes.length).all fun j =>
    match SP.bvIndex.lookup ((Tab.at P.sortOf j).getD 0) with
    | none => true
    | some w =>
      match Tab.at P.nodes j with
      | some (.const _) | some (.app _ _) => true
      | some (.num c) => 0 ≤ c && c < 2 ^ w
      -- a sum such as that of bits, in range whatever they are
      | some (.linear _ _) => ivSub (tr.fixedAt SP P (tr.mu SP P j) 2 j) 0 (2 ^ w - 1)
      | _ => false

/-- The facts of the real rule `r`, its symbol at node `k`. -/
def RRule.facts (k : Nat) : RRule → List Shape
  | .rat p q => [eqI (.num [(k, ((q : Int) : Rat))] 0) (.num [] p)]
  | .ratmul p q t => [eqI (.num [(k, ((q : Int) : Rat))] 0) (.num [(t, (p : Rat))] 0)]
  | .floor t => [.le (.same k) (.same t), .lt (.same t) (.num [(k, 1)] 1)]

/-- Whether the arguments of a real rule are those its facts need. -/
def RRule.ok : RRule → Bool
  | .rat _ q | .ratmul _ q _ => 0 < q
  | .floor _ => true

/-- Whether a lowered input holds by its reason. -/
def Trace.inputOk (f : Nat) : InputWhy → Bool
  | .assert a => SP.asserts.contains a && fits P.sig P.nodes P.sortOf f (form tr a)
  | .iteThen k => match iteFact SP tr k true with
    | some s => fits P.sig P.nodes P.sortOf f s
    | none => false
  | .iteElse k => match iteFact SP tr k false with
    | some s => fits P.sig P.nodes P.sortOf f s
    | none => false
  | .rule r j aux =>
    tr.ruleOk SP P r aux &&
      match tr.ruleFacts SP P r aux with
      | some fs =>
        match fs[j]? with
        | some s => fits P.sig P.nodes P.sortOf f s
        | none => false
      | none => false
  | .real r j =>
    r.ok &&
      match tr.realNode SP P r with
      | some k =>
        match (r.facts k)[j]? with
        | some s => fits P.sig P.nodes P.sortOf f s
        | none => false
      | none => false
  | .range i =>
    match SP.width i with
    | some w =>
      i < SP.nodes.length &&
        fits P.sig P.nodes P.sortOf f
          (.and [.le (.num [] 0) (.same (tr.at i)), .le (.same (tr.at i)) (.num [] (2 ^ w - 1))])
    | none => false

/-- Whether node `i` of the script lowers to a node of the expected shape. -/
def Trace.nodeOk (i : Nat) : Bool :=
  tr.at i < P.nodes.length &&
    ((match expect SP P tr i with
      | some s => fits P.sig P.nodes P.sortOf (tr.at i) s
      | none => false) || tr.bvOk SP P i)

/-- Whether the trace lowers the script to the problem. -/
def Trace.check (A : Answer) : Bool :=
  Surf.wellFormed SP.nodes && Surf.typed SP.sig SP.nodes SP.sortOf && SP.sortsOk && tr.sigOk SP P &&
  tr.node.length == SP.nodes.length &&
  (List.range SP.nodes.length).all (tr.nodeOk SP P) &&
  P.inputs.length == tr.inputs.length &&
  (P.inputs.zip tr.inputs).all (fun p => p.1 < P.nodes.length && tr.inputOk SP P p.1 p.2) &&
  A.assumed.length == tr.levels.length &&
  (A.assumed.zip tr.levels).all (fun p =>
    match A.levels.lookup p.1 with
    | some fs =>
      fs.length == p.2.length && (fs.zip p.2).all (fun q => q.1 < P.nodes.length && tr.inputOk SP P q.1 q.2)
    | none => true)


/-! ### The check in slices

As `Problem.accepts`, the check of a large trace runs faster in slices that
Lean checks in parallel: the nodes from `a` to `a + n`, and the rest once. -/

/-- `check` but the nodes and the inputs. -/
def Trace.checkBase (A : Answer) : Bool :=
  Surf.wellFormed SP.nodes && Surf.typed SP.sig SP.nodes SP.sortOf && SP.sortsOk && tr.sigOk SP P &&
  tr.node.length == SP.nodes.length &&
  P.inputs.length == tr.inputs.length &&
  A.assumed.length == tr.levels.length &&
  (A.assumed.zip tr.levels).all (fun p =>
    match A.levels.lookup p.1 with
    | some fs =>
      fs.length == p.2.length && (fs.zip p.2).all (fun q => q.1 < P.nodes.length && tr.inputOk SP P q.1 q.2)
    | none => true)

/-- The nodes from the `a`-th on. -/
def Trace.nodesFrom (a : Nat) : Bool := (List.range' a (SP.nodes.length - a)).all (tr.nodeOk SP P)

/-- The nodes from the `a`-th to the `a + n`-th. -/
def Trace.nodesSlice (a n : Nat) : Bool := a + n ≤ SP.nodes.length && (List.range' a n).all (tr.nodeOk SP P)

theorem Trace.nodesFrom_slice {a n : Nat} (h₁ : tr.nodesSlice SP P a n = true) (h₂ : tr.nodesFrom SP P (a + n) = true) :
    tr.nodesFrom SP P a = true := by
  unfold Trace.nodesSlice at h₁
  unfold Trace.nodesFrom at h₂ ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h₁
  rw [show SP.nodes.length - a = n + (SP.nodes.length - (a + n)) by omega, ← List.range'_append_1, List.all_append, h₁.2, h₂]
  rfl

theorem Trace.nodesFrom_end {a : Nat} (h : SP.nodes.length ≤ a) : tr.nodesFrom SP P a = true := by
  unfold Trace.nodesFrom
  rw [show SP.nodes.length - a = 0 by omega]
  rfl

/-- The inputs from the `a`-th on. -/
def Trace.inputsFrom (a : Nat) : Bool :=
  ((P.inputs.zip tr.inputs).drop a).all (fun p => p.1 < P.nodes.length && tr.inputOk SP P p.1 p.2)

/-- The inputs from the `a`-th to the `a + n`-th. -/
def Trace.inputsSlice (a n : Nat) : Bool :=
  (((P.inputs.zip tr.inputs).drop a).take n).all (fun p => p.1 < P.nodes.length && tr.inputOk SP P p.1 p.2)

theorem Trace.inputsFrom_slice {a n : Nat} (h₁ : tr.inputsSlice SP P a n = true)
    (h₂ : tr.inputsFrom SP P (a + n) = true) : tr.inputsFrom SP P a = true := by
  unfold Trace.inputsSlice at h₁
  unfold Trace.inputsFrom at h₂ ⊢
  rw [← List.take_append_drop n ((P.inputs.zip tr.inputs).drop a), List.all_append, h₁, List.drop_drop, h₂]
  rfl

theorem Trace.inputsFrom_end {a : Nat} (h : P.inputs.length ≤ a) : tr.inputsFrom SP P a = true := by
  unfold Trace.inputsFrom
  rw [List.drop_eq_nil_of_le (by simp; omega)]
  rfl

theorem Trace.check_of_slices {A : Answer} (hb : tr.checkBase SP P A = true) (hn : tr.nodesFrom SP P 0 = true)
    (hi : tr.inputsFrom SP P 0 = true) : tr.check SP P A = true := by
  unfold Trace.checkBase at hb
  unfold Trace.nodesFrom at hn
  unfold Trace.inputsFrom at hi
  unfold Trace.check
  rw [List.range_eq_range', ← Nat.sub_zero SP.nodes.length, hn]
  simp only [List.drop_zero] at hi
  simp only [Nat.sub_zero, Bool.and_true, hi] at hb ⊢
  simpa only [Bool.and_assoc] using hb
end

end Vik.Lower
