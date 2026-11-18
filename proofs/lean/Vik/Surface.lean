import Vik.Cert.Witnesses

/-!
# Surface scripts

The SMT-LIB terms and formulas Vik reads (`smtlib/Expr.scala`), as a table of
nodes like the lowered ones (`Vik/Lowered.lean`): each node refers to earlier
nodes by their index, and terms and formulas are one kind of node, told apart
by their sorts.

A model of a surface script gives values of the same type as a model of the
lowered script: numbers of an ordered field `R`, Booleans, and objects of a
type `U`. A bit-vector of width `w` takes the integer it stands for, unsigned,
in `[0, 2^w - 1]`: the value its lowering takes.
-/

set_option linter.unusedSectionVars false

namespace Vik.Surf

open Lean.Grind Vik.Real Vik.Low

/-- The unary operations on bit-vectors, with their indices. -/
inductive BvUn where
  | neg
  | not
  | extract (i j : Nat)
  | zeroExtend (k : Nat)
  | signExtend (k : Nat)
  | repeat (k : Nat)
  | rotateLeft (k : Nat)
  | rotateRight (k : Nat)
  deriving DecidableEq, Repr

/-- The binary operations on bit-vectors of one width. -/
inductive BvBin where
  | add | sub | mul | and | or | xor | nand | nor | xnor
  | shl | lshr | ashr | udiv | urem | sdiv | srem | smod | comp
  deriving DecidableEq, Repr

/-- The comparisons of bit-vectors. -/
inductive BvCmp where
  | ult | ule | ugt | uge | slt | sle | sgt | sge
  deriving DecidableEq, Repr

/-- A surface term or formula, over the nodes before it. -/
inductive SNode where
  | const (n : Nat)
  /-- A function, constructor, selector or tester applied to arguments. -/
  | app (f : Nat) (args : List Nat)
  | num (v : Int)
  | tt
  | ff
  | not (a : Nat)
  | and (as : List Nat)
  | or (as : List Nat)
  /-- `(=> a₁ … aₙ)`, to the right. -/
  | implies (as : List Nat)
  /-- `(= a₁ … aₙ)` on Booleans: each pair in turn. -/
  | iff (as : List Nat)
  /-- `(xor a₁ … aₙ)`, to the left. -/
  | xor (as : List Nat)
  /-- `(= a₁ … aₙ)`: each pair in turn. -/
  | eq (as : List Nat)
  | distinct (as : List Nat)
  /-- `ite` on terms or formulas. -/
  | ite (c a b : Nat)
  | add (as : List Nat)
  /-- `(- a₁ a₂ … aₙ)`, `a₁` minus the others. -/
  | sub (as : List Nat)
  | neg (a : Nat)
  | mul (as : List Nat)
  /-- Comparisons, each pair in turn. -/
  | le (as : List Nat)
  | lt (as : List Nat)
  | ge (as : List Nat)
  | gt (as : List Nat)
  | select (a i : Nat)
  | store (a i v : Nat)
  /-- `(_ bvv w)`, below `2^w`. -/
  | bvlit (w v : Nat)
  /-- A unary operation on a bit-vector of width `w`. -/
  | bvun (op : BvUn) (w a : Nat)
  /-- A binary operation on bit-vectors of width `w`. -/
  | bvbin (op : BvBin) (w a b : Nat)
  | bvcmp (op : BvCmp) (w a b : Nat)
  /-- `(concat a b)`, of widths `wa` and `wb`. -/
  | concat (wa wb a b : Nat)
  /-- `ubv_to_int`, or `sbv_to_int` when `signed`, of width `w`. -/
  | bv2int (signed : Bool) (w a : Nat)
  /-- `((_ int_to_bv w) a)`. -/
  | int2bv (w a : Nat)
  /-- The rational `p / q`, `q > 0`: a decimal literal or `(/ p q)` of literals. -/
  | rat (p : Int) (q : Nat)
  /-- `(/ a₁ a₂ … aₙ)`, `a₁` divided by the others. -/
  | div (as : List Nat)
  | toReal (a : Nat)
  | toInt (a : Nat)
  | isInt (a : Nat)
  /-- `(let ((x₁ t₁) … (xₙ tₙ)) body)`, with the terms `bs` bound: the value of
      `body`, where each use of `xⱼ` is a `bound` node. -/
  | letIn (bs : List Nat) (body : Nat)
  /-- A use of a variable that `let` binds to the term `d`. -/
  | bound (d : Nat)
  deriving DecidableEq, Repr

def SNode.children : SNode → List Nat
  | .const _ | .num _ | .tt | .ff | .bvlit _ _ | .rat _ _ => []
  | .app f args => f :: args
  | .not a | .neg a | .bvun _ _ a | .bv2int _ _ a | .int2bv _ a | .toReal a | .toInt a | .isInt a | .bound a => [a]
  | .letIn bs b => bs ++ [b]
  | .bvbin _ _ a b | .bvcmp _ _ a b | .concat _ _ a b => [a, b]
  | .and as | .or as | .implies as | .iff as | .xor as | .eq as | .distinct as
  | .add as | .sub as | .mul as | .le as | .lt as | .ge as | .gt as | .div as => as
  | .ite c a b => [c, a, b]
  | .select a i => [a, i]
  | .store a i v => [a, i, v]

def wellFormed (nodes : List SNode) : Bool :=
  (List.range nodes.length).all fun i =>
    match Tab.at nodes i with
    | some n => n.children.all (· < i)
    | none => false

/-! ## Semantics -/

/-- What a model gives the symbols, the applications and the stores. -/
structure Interp (R U : Type) where
  const : Nat → Val R U
  app : Val R U → List (Val R U) → Val R U
  store : Val R U → Val R U → Val R U → Val R U

variable {R U : Type} [Field R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R]
  [OrderedRing R] [IsCharP R 0]

attribute [local instance low] Lean.Grind.Ring.intCast

/-- Each pair of consecutive elements in relation `r`. -/
def chainP {α : Type} (r : α → α → Prop) : List α → Prop
  | a :: b :: rest => r a b ∧ chainP r (b :: rest)
  | _ => True

/-- Every two elements in relation `r`. -/
def pairwiseP {α : Type} (r : α → α → Prop) : List α → Prop
  | [] => True
  | a :: rest => (∀ b ∈ rest, r a b) ∧ pairwiseP r rest

def impliesR : List Bool → Bool
  | [] => true
  | [a] => a
  | a :: rest => !a || impliesR rest

def xorL : List Bool → Bool
  | [] => false
  | a :: rest => rest.foldl (fun x y => x != y) a

def sumR : List (Val R U) → R
  | [] => 0
  | v :: vs => v.toR + sumR vs

def prodR : List (Val R U) → R
  | [] => 1
  | v :: vs => v.toR * prodR vs

def BvUn.width : BvUn → Nat → Nat
  | .extract i j, _ => i - j + 1
  | .zeroExtend k, w | .signExtend k, w => w + k
  | .repeat k, w => w * k
  | _, w => w

def BvUn.apply : (op : BvUn) → {w : Nat} → BitVec w → BitVec (op.width w)
  | .neg, _, x => -x
  | .not, _, x => ~~~x
  | .extract i j, _, x => x.extractLsb i j
  | .zeroExtend k, w, x => x.setWidth (w + k)
  | .signExtend k, w, x => x.signExtend (w + k)
  | .repeat k, _, x => BitVec.replicate k x
  | .rotateLeft k, _, x => x.rotateLeft k
  | .rotateRight k, _, x => x.rotateRight k

def BvBin.width : BvBin → Nat → Nat
  | .comp, _ => 1
  | _, w => w

def BvBin.apply : (op : BvBin) → {w : Nat} → BitVec w → BitVec w → BitVec (op.width w)
  | .add, _, x, y => x + y
  | .sub, _, x, y => x - y
  | .mul, _, x, y => x * y
  | .and, _, x, y => x &&& y
  | .or, _, x, y => x ||| y
  | .xor, _, x, y => x ^^^ y
  | .nand, _, x, y => ~~~(x &&& y)
  | .nor, _, x, y => ~~~(x ||| y)
  | .xnor, _, x, y => ~~~(x ^^^ y)
  | .shl, _, x, y => x <<< y
  | .lshr, _, x, y => x >>> y
  | .ashr, _, x, y => x.sshiftRight' y
  | .udiv, _, x, y => x.smtUDiv y
  | .urem, _, x, y => x.umod y
  | .sdiv, _, x, y => x.smtSDiv y
  | .srem, _, x, y => x.srem y
  | .smod, _, x, y => x.smod y
  | .comp, _, x, y => if x = y then 1#1 else 0#1

def BvCmp.apply : BvCmp → {w : Nat} → BitVec w → BitVec w → Bool
  | .ult, _, x, y => x.ult y
  | .ule, _, x, y => x.ule y
  | .ugt, _, x, y => y.ult x
  | .uge, _, x, y => y.ule x
  | .slt, _, x, y => x.slt y
  | .sle, _, x, y => x.sle y
  | .sgt, _, x, y => y.slt x
  | .sge, _, x, y => y.sle x

open Classical in
/-- The integer a value stands for, if it is one. -/
noncomputable def intOf (v : Val R U) : Int := if h : ∃ k : Int, v = .num (k : R) then h.choose else 0

/-- The bit-vector of width `w` a value stands for: its integer modulo `2^w`. -/
noncomputable def bvOf (w : Nat) (v : Val R U) : BitVec w := BitVec.ofInt w (intOf v)

/-- The value of a bit-vector: its unsigned integer. -/
def ofBv {w : Nat} (x : BitVec w) : Val R U := .num ((x.toNat : Int) : R)

theorem intOf_num (k : Int) : intOf (.num (k : R) : Val R U) = k := by
  have h : ∃ j : Int, (.num (k : R) : Val R U) = .num (j : R) := ⟨k, rfl⟩
  simp only [intOf, h, dite_true]
  have := h.choose_spec
  injection this with e
  exact (cast_inj e).symm

/-- A value in the range of width `w` is that of its bit-vector. -/
theorem ofBv_bvOf {w : Nat} {k : Int} (h0 : 0 ≤ k) (h1 : k < 2 ^ w) :
    (ofBv (bvOf w (.num (k : R) : Val R U)) : Val R U) = .num (k : R) := by
  simp only [ofBv, bvOf, intOf_num, BitVec.toNat_ofInt]
  congr 2
  have : k % ((2 ^ w : Nat) : Int) = k := Int.emod_eq_of_lt h0 (by simpa using h1)
  rw [this]; omega

open Classical in
/-- The floor of `r`, if it has one (in the reals, always). -/
noncomputable def floorOf (r : R) : Int := if h : ∃ k : Int, IsFloor r k then h.choose else 0

theorem floorOf_spec {r : R} (h : ∃ k : Int, IsFloor r k) : IsFloor r (floorOf r) := by
  simp only [floorOf, h, dite_true]; exact h.choose_spec

/-- `a / b₁ / … / bₙ`. -/
def divR (a : R) : List (Val R U) → R
  | [] => a
  | b :: bs => divR (a / b.toR) bs

open Classical in
/-- The value of a node, over the values of the nodes before it. -/
noncomputable def evalNode (I : Interp R U) (vals : List (Val R U)) : SNode → Val R U
  | .const n => I.const n
  | .app f args => I.app (get vals f) (args.map (get vals))
  | .num v => .num (v : R)
  | .tt => .bool true
  | .ff => .bool false
  | .not a => .bool !(get vals a).truth
  | .and as => .bool (as.all fun a => (get vals a).truth)
  | .or as => .bool (as.any fun a => (get vals a).truth)
  | .implies as => .bool (impliesR (as.map fun a => (get vals a).truth))
  | .iff as => .bool (decide (chainP (· = ·) (as.map fun a => (get vals a).truth)))
  | .xor as => .bool (xorL (as.map fun a => (get vals a).truth))
  | .eq as => .bool (decide (chainP (· = ·) (as.map (get vals))))
  | .distinct as => .bool (decide (pairwiseP (· ≠ ·) (as.map (get vals))))
  | .ite c a b => if (get vals c).truth then get vals a else get vals b
  | .add as => .num (sumR (as.map (get vals)))
  | .sub as =>
    match as with
    | [] => .num 0
    | a :: rest => .num ((get vals a).toR - sumR (rest.map (get vals)))
  | .neg a => .num (-(get vals a).toR)
  | .mul as => .num (prodR (as.map (get vals)))
  | .le as => .bool (decide (chainP (fun x y => x ≤ y) (as.map fun a => (get vals a).toR)))
  | .lt as => .bool (decide (chainP (fun x y => x < y) (as.map fun a => (get vals a).toR)))
  | .ge as => .bool (decide (chainP (fun x y => y ≤ x) (as.map fun a => (get vals a).toR)))
  | .gt as => .bool (decide (chainP (fun x y => y < x) (as.map fun a => (get vals a).toR)))
  | .select a i => I.app (get vals a) [get vals i]
  | .store a i v => I.store (get vals a) (get vals i) (get vals v)
  | .bvlit w v => ofBv (BitVec.ofNat w v)
  | .bvun op w a => ofBv (op.apply (bvOf w (get vals a)))
  | .bvbin op w a b => ofBv (op.apply (bvOf w (get vals a)) (bvOf w (get vals b)))
  | .bvcmp op w a b => .bool (op.apply (bvOf w (get vals a)) (bvOf w (get vals b)))
  | .concat wa wb a b => ofBv (bvOf wa (get vals a) ++ bvOf wb (get vals b))
  | .bv2int signed w a =>
    .num (if signed then ((bvOf w (get vals a)).toInt : R) else (((bvOf w (get vals a)).toNat : Int) : R))
  | .int2bv w a => ofBv (BitVec.ofInt w (intOf (get vals a)))
  | .rat p q => .num ((p : R) / ((q : Int) : R))
  | .div as =>
    match as with
    | [] => .num 0
    | a :: rest => .num (divR (get vals a).toR (rest.map (get vals)))
  | .toReal a => .num (get vals a).toR
  | .toInt a => .num ((floorOf (get vals a).toR : Int) : R)
  | .isInt a => .bool (decide ((get vals a).toR = ((floorOf (get vals a).toR : Int) : R)))
  | .letIn _ b => get vals b
  | .bound d => get vals d

/-- The values of the nodes, in order. -/
noncomputable def values (I : Interp R U) (nodes : List SNode) : List (Val R U) :=
  nodes.foldl (fun vals n => vals ++ [evalNode I vals n]) []

noncomputable def val (I : Interp R U) (nodes : List SNode) (i : Nat) : Val R U := get (values I nodes) i

def holds (I : Interp R U) (nodes : List SNode) (i : Nat) : Prop := val I nodes i = .bool true

theorem values_length (I : Interp R U) (nodes : List SNode) : (values I nodes).length = nodes.length := by
  unfold values
  suffices ∀ (acc : List (Val R U)),
      (nodes.foldl (fun vals n => vals ++ [evalNode I vals n]) acc).length = acc.length + nodes.length by
    simpa using this []
  induction nodes with
  | nil => intro acc; simp
  | cons n ns ih => intro acc; simp only [List.foldl_cons]; rw [ih]; simp; omega

theorem values_prefix (I : Interp R U) (nodes : List SNode) :
    ∀ acc : List (Val R U), ∀ i < acc.length,
      (nodes.foldl (fun vals n => vals ++ [evalNode I vals n]) acc)[i]? = acc[i]? := by
  induction nodes with
  | nil => intro acc i _; rfl
  | cons n ns ih =>
    intro acc i hi
    simp only [List.foldl_cons]
    rw [ih _ i (by simp; omega)]
    simp [List.getElem?_append_left hi]

theorem values_get (I : Interp R U) (nodes : List SNode) (i : Nat) (n : SNode) (h : nodes[i]? = some n) :
    (values I nodes)[i]? = some (evalNode I (values I (nodes.take i)) n) := by
  have hi : i < nodes.length := by
    rcases Nat.lt_or_ge i nodes.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at h; cases h
  have split : nodes = nodes.take i ++ n :: nodes.drop (i + 1) := by
    conv => lhs; rw [← List.take_append_drop i nodes]
    congr 1
    rw [List.drop_eq_getElem_cons hi]
    congr 1
    rw [List.getElem?_eq_getElem hi] at h; cases h; rfl
  unfold values
  conv => lhs; rw [split]
  rw [List.foldl_append, List.foldl_cons]
  have hl : (List.foldl (fun vals n => vals ++ [evalNode I vals n]) [] (List.take i nodes)).length = i := by
    have := values_length I (nodes.take i); unfold values at this; rw [this]; simp; omega
  rw [values_prefix I _ _ i (by simp [hl])]
  simp [hl]

theorem get_take (I : Interp R U) (nodes : List SNode) {i j : Nat} (hj : j < i) (hi : i ≤ nodes.length) :
    get (values I (nodes.take i)) j = get (values I nodes) j := by
  unfold Low.get
  congr 1
  have hl : (values I (nodes.take i)).length = i := by rw [values_length]; simp; omega
  conv => rhs; unfold values; rw [← List.take_append_drop i nodes, List.foldl_append]
  rw [values_prefix I _ _ j (by unfold values at hl; rw [hl]; exact hj)]
  rfl

theorem map_get_congr {β : Type} {v1 v2 : List (Val R U)} (F : Val R U → β) (as : List Nat)
    (h : ∀ j ∈ as, get v1 j = get v2 j) : as.map (fun a => F (get v1 a)) = as.map (fun a => F (get v2 a)) :=
  List.map_congr_left (fun a m => by rw [h a m])

theorem evalNode_congr (I : Interp R U) {v1 v2 : List (Val R U)} (n : SNode)
    (h : ∀ j ∈ n.children, get v1 j = get v2 j) : evalNode I v1 n = evalNode I v2 n := by
  have hl : ∀ (as : List Nat), (∀ j ∈ as, get v1 j = get v2 j) → as.map (get v1) = as.map (get v2) :=
    fun as h => List.map_congr_left h
  cases n <;> simp only [SNode.children, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at h <;> simp only [evalNode]
  case app f args => rw [h.1, hl args h.2]
  case not a => rw [h]
  case neg a => rw [h]
  case ite c a b => rw [h.1, h.2.1, h.2.2]
  case select a i => rw [h.1, h.2]
  case store a i v => rw [h.1, h.2.1, h.2.2]
  case bvun => rw [h]
  case bv2int => rw [h]
  case int2bv => rw [h]
  case bvbin => rw [h.1, h.2]
  case bvcmp => rw [h.1, h.2]
  case concat => rw [h.1, h.2]
  case sub as =>
    cases as with
    | nil => rfl
    | cons a rest =>
      simp only [List.mem_cons, forall_eq_or_imp] at h
      simp only [h.1, hl rest h.2]
  case div as =>
    cases as with
    | nil => rfl
    | cons a rest =>
      simp only [List.mem_cons, forall_eq_or_imp] at h
      simp only [h.1, hl rest h.2]
  case toReal => rw [h]
  case toInt => rw [h]
  case isInt => rw [h]
  case bound => rw [h]
  case letIn bs b => exact h b (by simp)
  all_goals first
    | rw [hl _ h]
    | (have e := map_get_congr (fun v : Val R U => v.truth) _ h; simp only at e; rw [e])
    | (have e := map_get_congr (fun v : Val R U => v.toR) _ h; simp only at e; rw [e])
    | rw [all_congr' (fun a m => by rw [h a m])]
    | rw [any_congr' (fun a m => by rw [h a m])]

/-- In a well-formed table, node `i` takes the value of its node over the
    values of all nodes. -/
theorem val_node {I : Interp R U} {nodes : List SNode} (hw : wellFormed nodes = true) {i : Nat} {n : SNode}
    (h : nodes[i]? = some n) : val I nodes i = evalNode I (values I nodes) n := by
  have hi : i < nodes.length := by
    rcases Nat.lt_or_ge i nodes.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at h; cases h
  have hc : ∀ j ∈ n.children, j < i := by
    have := List.all_eq_true.mp hw i (List.mem_range.mpr hi)
    rw [Tab.at_eq, h] at this
    simpa using this
  unfold val Low.get
  rw [values_get I nodes i n h]
  simp only [Option.getD_some]
  exact evalNode_congr I n (fun j m => get_take I nodes (hc j m) (Nat.le_of_lt hi))

/-! ## Sorts and models -/

inductive SSort where
  | bool
  | int
  | real
  /-- An uninterpreted sort or a datatype. -/
  | user
  | bv (w : Nat)
  /-- Functions from the sorts `args` to `res`. -/
  | fn (args : List Nat) (res : Nat)
  | array (idx el : Nat)
  deriving DecidableEq, Repr

/-- The sorts, by number, and the sort of each symbol. -/
structure SSig where
  sorts : List SSort
  decls : List Nat

/-- A model: an interpretation with a domain for each sort. -/
structure Model (R U : Type) extends Interp R U where
  dom : Nat → Val R U → Prop

/-- What a model of the sorts, the symbols and the arrays satisfies. -/
structure Model.Sound (sig : SSig) (M : Model R U) : Prop where
  bool : ∀ s v, sig.sorts[s]? = some .bool → (M.dom s v ↔ ∃ b, v = .bool b)
  int : ∀ s v, sig.sorts[s]? = some .int → (M.dom s v ↔ ∃ k : Int, v = .num (k : R))
  real : ∀ s v, sig.sorts[s]? = some .real → (M.dom s v ↔ ∃ r, v = .num r)
  bv : ∀ s w v, sig.sorts[s]? = some (.bv w) →
    (M.dom s v ↔ ∃ k : Int, v = .num (k : R) ∧ 0 ≤ k ∧ k < 2 ^ w)
  fn : ∀ s as r f xs, sig.sorts[s]? = some (.fn as r) → M.dom s f →
    Forall2 M.dom as xs → M.dom r (M.app f xs)
  select : ∀ s i e a x, sig.sorts[s]? = some (.array i e) → M.dom s a → M.dom i x → M.dom e (M.app a [x])
  store : ∀ s i e a x v, sig.sorts[s]? = some (.array i e) → M.dom s a → M.dom i x → M.dom e v →
    M.dom s (M.store a x v) ∧ ∀ y, M.dom i y →
      (y = x → M.app (M.store a x v) [y] = v) ∧ (y ≠ x → M.app (M.store a x v) [y] = M.app a [y])
  /-- Arrays and functions are extensional. -/
  ext : ∀ s as r f g, (sig.sorts[s]? = some (.fn as r) ∨ ∃ i, as = [i] ∧ sig.sorts[s]? = some (.array i r)) →
    M.dom s f → M.dom s g → (∀ xs, Forall2 M.dom as xs → M.app f xs = M.app g xs) → f = g
  const : ∀ k s, sig.decls[k]? = some s → M.dom s (M.const k)

/-! ## Typing -/

def SSig.is (sig : SSig) (s : Nat) (d : SSort) : Bool := sig.sorts[s]? == some d

def SSig.numeric (sig : SSig) (s : Nat) : Bool := sig.is s .int || sig.is s .real

/-- The sort of the nodes of an arithmetic operation: integers of integers,
    reals of numbers. -/
def arithTyped (sig : SSig) (so : Nat → Nat) (as : List Nat) (s : Nat) : Bool :=
  (sig.is s .int && as.all (fun a => sig.is (so a) .int)) || (sig.is s .real && as.all (fun a => sig.numeric (so a)))

/-- Whether node `n` has sort `s`, its children those of `sortOf`. -/
def nodeTyped (sig : SSig) (sortOf : List Nat) (n : SNode) (s : Nat) : Bool :=
  let so (i : Nat) := (Tab.at sortOf i).getD 0
  let isBool (i : Nat) := sig.is (so i) .bool
  let bool := sig.is s .bool
  match n with
  | .const k => sig.decls[k]? == some s
  | .app f args =>
    match sig.sorts[so f]? with
    | some (.fn as r) => r == s && args.map so == as
    | _ => false
  | .num _ => sig.is s .int
  | .tt | .ff => bool
  | .not a => bool && isBool a
  | .and as | .or as | .implies as | .iff as | .xor as => bool && as.all isBool
  | .eq as | .distinct as =>
    bool && match as with
      | [] => true
      | a :: rest => rest.all (fun b => so b == so a)
  | .ite c a b => isBool c && so a == s && so b == s
  | .add as | .sub as | .mul as => arithTyped sig so as s
  | .neg a => arithTyped sig so [a] s
  | .le as | .lt as | .ge as | .gt as => bool && as.all (fun a => sig.numeric (so a))
  | .select a i =>
    match sig.sorts[so a]? with
    | some (.array idx el) => so i == idx && el == s
    | _ => false
  | .store a i v =>
    match sig.sorts[so a]? with
    | some (.array idx el) => so a == s && so i == idx && so v == el
    | _ => false
  | .bvlit w _ => sig.is s (.bv w)
  | .bvun op w a => sig.is (so a) (.bv w) && sig.is s (.bv (op.width w))
  | .bvbin op w a b => sig.is (so a) (.bv w) && sig.is (so b) (.bv w) && sig.is s (.bv (op.width w))
  | .bvcmp _ w a b => sig.is (so a) (.bv w) && sig.is (so b) (.bv w) && bool
  | .concat wa wb a b => sig.is (so a) (.bv wa) && sig.is (so b) (.bv wb) && sig.is s (.bv (wa + wb))
  | .bv2int _ w a => sig.is (so a) (.bv w) && sig.is s .int
  | .int2bv w a => sig.is (so a) .int && sig.is s (.bv w)
  | .rat _ q => sig.is s .real && 0 < q
  | .div as => sig.is s .real && as.all (fun a => sig.numeric (so a))
  | .toReal a => sig.is s .real && sig.numeric (so a)
  | .toInt a => sig.is s .int && sig.numeric (so a)
  | .isInt a => bool && sig.numeric (so a)
  | .letIn _ b => so b == s
  | .bound d => so d == s

def typed (sig : SSig) (nodes : List SNode) (sortOf : List Nat) : Bool :=
  sortOf.length == nodes.length &&
    (List.range nodes.length).all fun i =>
      match Tab.at nodes i with
      | some n => nodeTyped sig sortOf n ((Tab.at sortOf i).getD 0)
      | none => false

theorem sumR_int : ∀ (vs : List (Val R U)), (∀ v ∈ vs, ∃ k : Int, v = .num (k : R)) →
    ∃ k : Int, sumR vs = (k : R)
  | [], _ => ⟨0, by simp [sumR]; grind⟩
  | v :: vs, h => by
    obtain ⟨k, rfl⟩ := h v (by simp)
    obtain ⟨m, hm⟩ := sumR_int vs (fun w m => h w (by simp [m]))
    exact ⟨k + m, by simp only [sumR, hm, Val.toR, Ring.intCast_add]⟩

theorem prodR_int : ∀ (vs : List (Val R U)), (∀ v ∈ vs, ∃ k : Int, v = .num (k : R)) →
    ∃ k : Int, prodR vs = (k : R)
  | [], _ => ⟨1, by simp [prodR]; grind⟩
  | v :: vs, h => by
    obtain ⟨k, rfl⟩ := h v (by simp)
    obtain ⟨m, hm⟩ := prodR_int vs (fun w m => h w (by simp [m]))
    exact ⟨k * m, by simp only [prodR, hm, Val.toR, Ring.intCast_mul]⟩

section
variable {sig : SSig} {M : Model R U} (hM : M.Sound sig)
include hM

theorem dom_num_of_numeric {s : Nat} {v : Val R U} (hs : sig.numeric s = true) (h : M.dom s v) :
    ∃ r, v = .num r := by
  simp only [SSig.numeric, SSig.is, Bool.or_eq_true, beq_iff_eq] at hs
  rcases hs with hs | hs
  · obtain ⟨k, rfl⟩ := (hM.int _ _ hs).mp h; exact ⟨_, rfl⟩
  · exact (hM.real _ _ hs).mp h

/-- In a well-sorted table, every node takes a value of its sort. -/
theorem val_dom {nodes : List SNode} {sortOf : List Nat} (hw : wellFormed nodes = true)
    (ht : typed sig nodes sortOf = true) :
    ∀ i, i < nodes.length → M.dom (sortOf[i]?.getD 0) (val M.toInterp nodes i) := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
  intro hi
  simp only [typed, Tab.at_eq, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at ht
  have hn := ht.2 i hi
  obtain ⟨n, hn'⟩ : ∃ n, nodes[i]? = some n := ⟨nodes[i], List.getElem?_eq_getElem hi⟩
  rw [hn'] at hn
  have hc : ∀ j ∈ n.children, j < i := by
    have := List.all_eq_true.mp hw i (List.mem_range.mpr hi)
    rw [Tab.at_eq, hn'] at this; simpa using this
  have ihc : ∀ j ∈ n.children, M.dom (sortOf[j]?.getD 0) (val M.toInterp nodes j) :=
    fun j m => ih j (hc j m) (Nat.lt_trans (hc j m) hi)
  have hv := val_node (I := M.toInterp) hw hn'
  generalize sortOf[i]?.getD 0 = s at *
  have boolv : sig.is s .bool = true → ∀ b : Bool, M.dom s (.bool b) := by
    intro hb b
    simp only [SSig.is, beq_iff_eq] at hb
    exact (hM.bool _ _ hb).mpr ⟨b, rfl⟩
  have bvv : ∀ {w}, sig.is s (.bv w) = true → ∀ x : BitVec w, M.dom s (ofBv x) := by
    intro w hb x
    simp only [SSig.is, beq_iff_eq] at hb
    refine (hM.bv _ _ _ hb).mpr ⟨_, rfl, by omega, ?_⟩
    have := x.isLt
    exact_mod_cast this
  -- the arithmetic operations
  have arith : ∀ as : List Nat, (∀ j ∈ as, j ∈ n.children) → arithTyped sig (fun i => sortOf[i]?.getD 0) as s = true →
      ∀ r : R, (sig.is s .int = true → (∀ a ∈ as, ∃ k : Int, val M.toInterp nodes a = .num (k : R)) →
        ∃ k : Int, r = (k : R)) → M.dom s (.num r) := by
    intro as hsub ht' r hr
    simp only [arithTyped, Bool.or_eq_true, Bool.and_eq_true, List.all_eq_true] at ht'
    rcases ht' with ⟨hs, has⟩ | ⟨hs, _⟩
    · obtain ⟨k, hk⟩ := hr hs (fun a m => by
        have := has a m
        simp only [SSig.is, beq_iff_eq] at this
        exact (hM.int _ _ this).mp (ihc a (hsub a m)))
      simp only [SSig.is, beq_iff_eq] at hs
      exact (hM.int _ _ hs).mpr ⟨k, by rw [hk]⟩
    · simp only [SSig.is, beq_iff_eq] at hs
      exact (hM.real _ _ hs).mpr ⟨r, rfl⟩
  cases n with
  | const k =>
    simp only [Tab.at_eq, nodeTyped, beq_iff_eq] at hn
    rw [hv]; exact hM.const _ _ hn
  | app f args =>
    simp only [Tab.at_eq, nodeTyped] at hn
    split at hn
    · rename_i as r hs
      simp only [Bool.and_eq_true, beq_iff_eq] at hn
      obtain ⟨rfl, hargs⟩ := hn
      rw [hv]
      apply hM.fn _ as _ _ _ hs (ihc f (by simp [SNode.children]))
      rw [← hargs]
      exact forall2_map _ _ _ args (fun j m => ihc j (by simp [SNode.children, m]))
    · cases hn
  | num v =>
    simp only [Tab.at_eq, nodeTyped, SSig.is, beq_iff_eq] at hn
    rw [hv]; exact (hM.int _ _ hn).mpr ⟨v, rfl⟩
  | ite c a b =>
    simp only [Tab.at_eq, nodeTyped, Bool.and_eq_true, beq_iff_eq] at hn
    obtain ⟨⟨_, ha⟩, hb⟩ := hn
    rw [hv]; simp only [evalNode]
    split
    · rw [← ha]; exact ihc a (by simp [SNode.children])
    · rw [← hb]; exact ihc b (by simp [SNode.children])
  | add as =>
    simp only [Tab.at_eq, nodeTyped] at hn
    rw [hv]; simp only [evalNode]
    exact arith as (fun j m => m) hn _ (fun _ h => sumR_int _ (fun v m => by
      obtain ⟨a, ma, rfl⟩ := List.mem_map.mp m; exact h a ma))
  | mul as =>
    simp only [Tab.at_eq, nodeTyped] at hn
    rw [hv]; simp only [evalNode]
    exact arith as (fun j m => m) hn _ (fun _ h => prodR_int _ (fun v m => by
      obtain ⟨a, ma, rfl⟩ := List.mem_map.mp m; exact h a ma))
  | sub as =>
    simp only [Tab.at_eq, nodeTyped] at hn
    rw [hv]; simp only [evalNode]
    cases as with
    | nil => exact arith [] (fun j m => by simp at m) hn _ (fun _ _ => ⟨0, by rw [Ring.intCast_zero]⟩)
    | cons a rest =>
      exact arith (a :: rest) (fun j m => m) hn _ (fun _ h => by
        obtain ⟨k, hk⟩ := h a (by simp)
        obtain ⟨m, hm⟩ := sumR_int (rest.map (Low.get (values M.toInterp nodes))) (fun v mv => by
          obtain ⟨b, mb, rfl⟩ := List.mem_map.mp mv; exact h b (List.mem_cons_of_mem _ mb))
        simp only [val] at hk
        exact ⟨k - m, by rw [hk, hm, Ring.intCast_sub]; rfl⟩)
  | neg a =>
    simp only [Tab.at_eq, nodeTyped] at hn
    rw [hv]; simp only [evalNode]
    exact arith [a] (fun j m => by simp at m; subst m; simp [SNode.children]) hn _ (fun _ h => by
      obtain ⟨k, hk⟩ := h a (by simp)
      simp only [val] at hk
      exact ⟨-k, by rw [hk, Ring.intCast_neg]; rfl⟩)
  | select a i =>
    simp only [Tab.at_eq, nodeTyped] at hn
    split at hn
    · rename_i idx el hs
      simp only [Bool.and_eq_true, beq_iff_eq] at hn
      obtain ⟨hi', rfl⟩ := hn
      rw [hv]; simp only [evalNode]
      have di := ihc i (by simp [SNode.children]); rw [hi'] at di
      exact hM.select _ _ _ _ _ hs (ihc a (by simp [SNode.children])) di
    · cases hn
  | store a i v =>
    simp only [Tab.at_eq, nodeTyped] at hn
    split at hn
    · rename_i idx el hs
      simp only [Bool.and_eq_true, beq_iff_eq] at hn
      obtain ⟨⟨ha, hi'⟩, hv'⟩ := hn
      rw [hv]; simp only [evalNode]
      have da := ihc a (by simp [SNode.children])
      have di := ihc i (by simp [SNode.children]); rw [hi'] at di
      have dv := ihc v (by simp [SNode.children]); rw [hv'] at dv
      rw [← ha]
      exact (hM.store _ _ _ _ _ _ hs da di dv).1
    · cases hn
  | bvlit w v =>
    simp only [Tab.at_eq, nodeTyped] at hn
    rw [hv]; exact bvv hn _
  | bvun op w a =>
    simp only [Tab.at_eq, nodeTyped, Bool.and_eq_true] at hn
    rw [hv]; exact bvv hn.2 _
  | bvbin op w a b =>
    simp only [Tab.at_eq, nodeTyped, Bool.and_eq_true] at hn
    rw [hv]; exact bvv hn.2 _
  | concat wa wb a b =>
    simp only [Tab.at_eq, nodeTyped, Bool.and_eq_true] at hn
    rw [hv]; exact bvv hn.2 _
  | int2bv w a =>
    simp only [Tab.at_eq, nodeTyped, Bool.and_eq_true] at hn
    rw [hv]; exact bvv hn.2 _
  | bv2int sg w a =>
    simp only [Tab.at_eq, nodeTyped, Bool.and_eq_true, SSig.is, beq_iff_eq] at hn
    rw [hv]; simp only [evalNode]
    refine (hM.int _ _ hn.2).mpr ?_
    split
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  | bvcmp _ _ _ _ =>
    simp only [Tab.at_eq, nodeTyped, Bool.and_eq_true] at hn
    rw [hv]; simp only [evalNode]
    exact boolv hn.2 _
  | rat _ _ | div _ | toReal _ =>
    simp only [Tab.at_eq, nodeTyped, Bool.and_eq_true, SSig.is, beq_iff_eq] at hn
    rw [hv]; simp only [evalNode]
    first
      | exact (hM.real _ _ hn.1).mpr ⟨_, rfl⟩
      | (split <;> exact (hM.real _ _ hn.1).mpr ⟨_, rfl⟩)
  | toInt _ =>
    simp only [Tab.at_eq, nodeTyped, Bool.and_eq_true, SSig.is, beq_iff_eq] at hn
    rw [hv]; simp only [evalNode]
    exact (hM.int _ _ hn.1).mpr ⟨_, rfl⟩
  | isInt _ =>
    simp only [Tab.at_eq, nodeTyped, Bool.and_eq_true] at hn
    rw [hv]; simp only [evalNode]
    exact boolv hn.1 _
  | letIn bs b =>
    simp only [Tab.at_eq, nodeTyped, beq_iff_eq] at hn
    rw [hv]; simp only [evalNode]; rw [← hn]
    exact ihc b (by simp [SNode.children])
  | bound d =>
    simp only [Tab.at_eq, nodeTyped, beq_iff_eq] at hn
    rw [hv]; simp only [evalNode]; rw [← hn]
    exact ihc d (by simp [SNode.children])
  | tt | ff | not _ | and _ | or _ | implies _ | iff _ | xor _ | eq _ | distinct _
  | le _ | lt _ | ge _ | gt _ =>
    simp only [Tab.at_eq, nodeTyped, Bool.and_eq_true] at hn
    rw [hv]; simp only [evalNode]
    first
      | exact boolv hn _
      | exact boolv hn.1 _

end

/-! ## Definitions

`(define-fun f ((x₁ s₁) … (xₙ sₙ)) s t)` is, by SMT-LIB, the declaration of `f`
with the assertion that `f(x₁, …, xₙ) = t` for all `x₁, …, xₙ` of their
sorts. A definition here is the symbol `f`, the symbols of its parameters, and
the table of its body `t`, whose nodes use the parameters as constants. A use
of `f` is an `app` of a `const f` node, or `const f` when `f` has no
parameters. -/

structure SDef where
  sym : Nat
  params : List Nat
  nodes : List SNode
  root : Nat
  deriving DecidableEq, Repr

/-- Node `n` with each child `c` replaced by `m c`. -/
def SNode.rename (m : Nat → Nat) : SNode → SNode
  | .const k => .const k
  | .app f args => .app (m f) (args.map m)
  | .num v => .num v
  | .tt => .tt
  | .ff => .ff
  | .not a => .not (m a)
  | .and as => .and (as.map m)
  | .or as => .or (as.map m)
  | .implies as => .implies (as.map m)
  | .iff as => .iff (as.map m)
  | .xor as => .xor (as.map m)
  | .eq as => .eq (as.map m)
  | .distinct as => .distinct (as.map m)
  | .ite c a b => .ite (m c) (m a) (m b)
  | .add as => .add (as.map m)
  | .sub as => .sub (as.map m)
  | .neg a => .neg (m a)
  | .mul as => .mul (as.map m)
  | .le as => .le (as.map m)
  | .lt as => .lt (as.map m)
  | .ge as => .ge (as.map m)
  | .gt as => .gt (as.map m)
  | .select a i => .select (m a) (m i)
  | .store a i v => .store (m a) (m i) (m v)
  | .bvlit w v => .bvlit w v
  | .bvun op w a => .bvun op w (m a)
  | .bvbin op w a b => .bvbin op w (m a) (m b)
  | .bvcmp op w a b => .bvcmp op w (m a) (m b)
  | .concat wa wb a b => .concat wa wb (m a) (m b)
  | .bv2int sg w a => .bv2int sg w (m a)
  | .int2bv w a => .int2bv w (m a)
  | .rat p q => .rat p q
  | .div as => .div (as.map m)
  | .toReal a => .toReal (m a)
  | .toInt a => .toInt (m a)
  | .isInt a => .isInt (m a)
  | .letIn bs b => .letIn (bs.map m) (m b)
  | .bound d => .bound (m d)

/-- The interpretation `I` with the parameters `ps` taking the values `vs`. -/
def Interp.bind (I : Interp R U) (ps : List Nat) (vs : List (Val R U)) : Interp R U :=
  { I with const := fun c => ((ps.zip vs).lookup c).getD (I.const c) }

/-- The assertion of definition `d` in model `M`. -/
def SDef.Holds (sig : SSig) (M : Model R U) (d : SDef) : Prop :=
  ∀ vs, Forall2 M.dom (d.params.map fun p => sig.decls.getD p 0) vs →
    (if d.params = [] then M.const d.sym else M.app (M.const d.sym) vs) =
      val (M.toInterp.bind d.params vs) d.nodes d.root

theorem evalNode_rename (I J : Interp R U) (happ : I.app = J.app) (hst : I.store = J.store)
    {v1 v2 : List (Val R U)} (m : Nat → Nat) (n : SNode) (hn : ∀ k, n ≠ .const k)
    (h : ∀ c ∈ n.children, get v1 (m c) = get v2 c) : evalNode I v1 (n.rename m) = evalNode J v2 n := by
  have hl : ∀ (as : List Nat), (∀ j ∈ as, get v1 (m j) = get v2 j) → (as.map m).map (get v1) = as.map (get v2) :=
    fun as h => by rw [List.map_map]; exact List.map_congr_left h
  have hF : ∀ {β : Type} (F : Val R U → β) (as : List Nat), (∀ j ∈ as, get v1 (m j) = get v2 j) →
      (as.map m).map (fun a => F (get v1 a)) = as.map (fun a => F (get v2 a)) :=
    fun F as h => by rw [List.map_map]; exact List.map_congr_left (fun a ma => by simp only [Function.comp_apply, h a ma])
  have hall : ∀ (l : List Nat) (v : List (Val R U)),
      l.all (fun a => (get v a).truth) = (l.map fun a => (get v a).truth).all id := by
    intro l v; simp [List.all_map, Function.comp_def]
  have hany : ∀ (l : List Nat) (v : List (Val R U)),
      l.any (fun a => (get v a).truth) = (l.map fun a => (get v a).truth).any id := by
    intro l v; simp [List.any_map, Function.comp_def]
  cases n <;> simp only [SNode.children, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at h <;> simp only [SNode.rename, evalNode]
  case const k => exact absurd rfl (hn k)
  case and as => rw [hall, hall, hF _ _ h]
  case or as => rw [hany, hany, hF _ _ h]
  case app f args => rw [happ, h.1, hl args h.2]
  case not a => rw [h]
  case neg a => rw [h]
  case ite c a b => rw [h.1, h.2.1, h.2.2]
  case select a i => rw [happ, h.1, h.2]
  case store a i v => rw [hst, h.1, h.2.1, h.2.2]
  case bvun => rw [h]
  case bv2int => rw [h]
  case int2bv => rw [h]
  case bvbin => rw [h.1, h.2]
  case bvcmp => rw [h.1, h.2]
  case concat => rw [h.1, h.2]
  case toReal => rw [h]
  case toInt => rw [h]
  case isInt => rw [h]
  case bound => rw [h]
  case letIn bs b => exact h b (by simp)
  case sub as =>
    cases as with
    | nil => rfl
    | cons a rest =>
      simp only [List.mem_cons, forall_eq_or_imp] at h
      simp only [List.map_cons, h.1, hl rest h.2]
  case div as =>
    cases as with
    | nil => rfl
    | cons a rest =>
      simp only [List.mem_cons, forall_eq_or_imp] at h
      simp only [List.map_cons, h.1, hl rest h.2]
  all_goals first
    | rw [hl _ h]
    | rw [hF (fun v : Val R U => v.truth) _ h]
    | rw [hF (fun v : Val R U => v.toR) _ h]

/-- Whether nodes `ms` of `nodes` are an instance of the body of `d`, with its
    parameters replaced by the nodes `args`: node `ms[b]` is node `b` of the
    body, its children those of `ms`. -/
def SDef.instOk (nodes : List SNode) (d : SDef) (args ms : List Nat) : Bool :=
  ms.length == d.nodes.length &&
    (List.range d.nodes.length).all fun b =>
      match d.nodes[b]?, ms[b]? with
      | some (.const p), some j =>
        match (d.params.zip args).lookup p with
        | some a => j == a
        | none => nodes[j]? == some (.const p)
      | some n, some j => nodes[j]? == some (n.rename fun c => ms.getD c 0)
      | _, _ => false

theorem lookup_zip_map {β γ : Type} (f : β → γ) :
    ∀ (ps : List Nat) (xs : List β) (c : Nat), (ps.zip (xs.map f)).lookup c = ((ps.zip xs).lookup c).map f
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | p :: ps, x :: xs, c => by
    simp only [List.map_cons, List.zip_cons_cons, List.lookup_cons]
    split
    · rfl
    · exact lookup_zip_map f ps xs c

/-- An instance of the body of a definition takes the value of the body, with
    the parameters taking the values of the arguments. -/
theorem inst_val {nodes : List SNode} {d : SDef} {args ms : List Nat} (I : Interp R U)
    (hw : wellFormed nodes = true) (hwd : wellFormed d.nodes = true) (h : d.instOk nodes args ms = true) :
    ∀ b < d.nodes.length,
      val I nodes (ms.getD b 0) = val (I.bind d.params (args.map (val I nodes))) d.nodes b := by
  simp only [SDef.instOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨hlen, hb⟩ := h
  intro b
  induction b using Nat.strongRecOn with
  | ind b ih =>
  intro hbl
  have hb' := hb b hbl
  obtain ⟨n, hn⟩ : ∃ n, d.nodes[b]? = some n := ⟨_, List.getElem?_eq_getElem hbl⟩
  have hms : ms[b]? = some (ms.getD b 0) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
  rw [hn, hms] at hb'
  have hc : ∀ j ∈ n.children, j < b := by
    have := List.all_eq_true.mp hwd b (List.mem_range.mpr hbl)
    rw [Tab.at_eq, hn] at this; simpa using this
  rw [val_node (I := I.bind d.params (args.map (val I nodes))) hwd hn]
  split at hb'
  · rename_i q j e1 e2
    simp only [Option.some.injEq] at e1 e2
    subst e1; subst e2
    simp only [evalNode, Interp.bind, lookup_zip_map]
    split at hb'
    · rename_i a ha
      rw [ha, beq_iff_eq.mp hb']; rfl
    · rename_i ha
      rw [ha, val_node hw (beq_iff_eq.mp hb')]; rfl
  · rename_i n' j hnc e1 e2
    simp only [Option.some.injEq] at e1 e2
    subst e1; subst e2
    rw [val_node hw (beq_iff_eq.mp hb')]
    refine evalNode_rename I (I.bind d.params (args.map (val I nodes))) rfl rfl _ n (fun k e => hnc k e) (fun c mc => ?_)
    exact ih c (hc c mc) (Nat.lt_trans (hc c mc) hbl)
  · cases hb'


end Vik.Surf
