import Lean

/-!
# Certificates as S-expressions

An exported proof gives its data (the script, the lowered problem, the answer
and the trace) as S-expressions, which `sexp% "…"` turns into terms of the
expected type. Lean's term parser and elaborator are slow on large literals;
this reads the text in one pass and builds the terms directly.

The reader is not trusted: the kernel checks the terms it builds like any
other, and the statement of an exported theorem is about the terms, whatever
built them.

The format, for an expected type `T`:
- `Nat`, `Int`: a numeral, `-` in front for a negative integer.
- `Rat`: a numeral, or `n/d`.
- `List α`: `(x₁ … xₙ)`.
- `α × β`: `(a b)`, and `(a b c)` for `α × β × γ`.
- an inductive type: a constructor's name alone, or `(name a₁ … aₙ)`, its
  arguments after the type's parameters; a structure also as `(a₁ … aₙ)`, or
  as `((field₁ v₁) … (fieldₙ vₙ))` with every field named, in any order.
- `;` starts a comment, to the end of the line.
-/

namespace Vik.Sexp

open Lean Meta Elab Term

inductive Sexp where
  | atom (s : String)
  | list (xs : Array Sexp)
  deriving Inhabited

partial def Sexp.toString : Sexp → String
  | .atom s => s
  | .list xs => "(" ++ " ".intercalate (xs.toList.map Sexp.toString) ++ ")"

private def isSpace (b : UInt8) : Bool := b == 32 || b == 10 || b == 13 || b == 9

/-- The S-expressions of `s`, from byte `i`. -/
partial def parseMany (s : ByteArray) : Except String (Array Sexp) := do
  let mut stack : Array (Array Sexp) := #[#[]]
  let mut i := 0
  while i < s.size do
    let b := s[i]!
    if isSpace b then
      i := i + 1
    else if b == 59 then -- ;
      while i < s.size && s[i]! != 10 do i := i + 1
    else if b == 40 then -- (
      stack := stack.push #[]
      i := i + 1
    else if b == 41 then -- )
      if stack.size ≤ 1 then throw s!"unbalanced ')' at byte {i}"
      let top := stack.back!
      stack := stack.pop
      stack := stack.modify (stack.size - 1) (·.push (.list top))
      i := i + 1
    else
      let j := i
      while i < s.size && !isSpace s[i]! && s[i]! != 40 && s[i]! != 41 && s[i]! != 59 do i := i + 1
      let tok := String.fromUTF8! (s.extract j i)
      stack := stack.modify (stack.size - 1) (·.push (.atom tok))
  if stack.size != 1 then throw "unbalanced '('"
  return stack[0]!

def parse (s : String) : Except String Sexp := do
  match ← parseMany s.toUTF8 with
  | #[e] => return e
  | es => throw s!"expected one S-expression, got {es.size}"

private def natOf (s : String) : MetaM Nat :=
  match s.toNat? with
  | some n => return n
  | none => throwError "sexp%: expected a natural number, got '{s}'"

private def intOf (s : String) : MetaM Int :=
  match s.toInt? with
  | some n => return n
  | none => throwError "sexp%: expected an integer, got '{s}'"

/-- An integer as a constructor of `Int` on a literal. -/
def intExpr (k : Int) : Expr :=
  if k ≥ 0 then mkApp (Lean.mkConst ``Int.ofNat) (mkRawNatLit k.toNat)
  else mkApp (Lean.mkConst ``Int.negSucc) (mkRawNatLit (-k - 1).toNat)

register_option vik.sexp.chunk : Nat := {
  defValue := 0
  descr := "if positive, `sexp%` builds a list in compiled definitions of about this many atoms each, which Lean's compiler handles far faster than one large term"
}

structure State where
  rats : Std.HashMap String Expr := {}
  /-- The atoms in a definition of a list, `0` not to split. -/
  chunk : Nat := 0
  /-- The definition being elaborated, and the auxiliary definitions so far. -/
  base : Name := .anonymous
  aux : Nat := 0

abbrev M := StateRefT State MetaM

private def ratExpr (s : String) : M Expr := do
  if let some e := (← get).rats[s]? then return e
  let ratT := Lean.mkConst ``Rat
  let num (t : String) : MetaM Expr := do
    let k ← intOf t
    let n ← mkNumeral ratT k.natAbs
    if k < 0 then mkAppM ``Neg.neg #[n] else return n
  let e ← match s.splitOn "/" with
    | [a] => num a
    | [a, b] => do mkAppM ``HDiv.hDiv #[← num a, ← mkNumeral ratT (← natOf b)]
    | _ => throwError "sexp%: expected a rational, got '{s}'"
  modify fun st => { st with rats := st.rats.insert s e }
  return e

/-- The atoms of `e`. -/
partial def Sexp.weight : Sexp → Nat
  | .atom _ => 1
  | .list xs => xs.foldl (fun n x => n + x.weight) 1

/-- A compiled definition of `e`, of the closed type `ty`. -/
def auxDef (ty e : Expr) : M Expr := do
  let st ← get
  let n := st.base ++ Name.mkSimple s!"_sexp{st.aux}"
  set { st with aux := st.aux + 1 }
  let d : DefinitionVal :=
    { name := n, levelParams := [], type := ty, value := e, hints := .regular 0, safety := .safe }
  addAndCompile (.defnDecl d)
  return Lean.mkConst n

mutual

/-- The term of type `ty` that `e` describes. -/
partial def build (ty : Expr) (e : Sexp) : M Expr := do
  -- `@c`: the constant `c`, of type `ty`, so that a large term can be split
  -- across declarations
  if let .atom s := e then
    if s.startsWith "@" then
      let c ← resolveGlobalConstNoOverload (mkIdent (s.drop 1).toName)
      let e := Lean.mkConst c ((← getConstInfo c).levelParams.map fun _ => levelZero)
      unless ← isDefEq (← inferType e) ty do throwError "sexp%: {c} is not of type {ty}"
      return e
  let ty ← whnf ty
  let .const n lvls := ty.getAppFn | throwError "sexp%: unsupported type {ty}"
  let args := ty.getAppArgs
  match n, e with
  | ``Nat, .atom s => return mkRawNatLit (← natOf s)
  | ``Int, .atom s => return intExpr (← intOf s)
  | ``Rat, .atom s => ratExpr s
  | ``List, .list xs => do
    let α := args[0]!
    let chunk := (← get).chunk
    let mut acc := mkApp (Lean.mkConst ``List.nil lvls) α
    let mut w := 0
    for x in xs.reverse do
      acc := mkApp3 (Lean.mkConst ``List.cons lvls) α (← build α x) acc
      if chunk > 0 then
        w := w + x.weight
        if w ≥ chunk then
          acc ← auxDef ty acc
          w := 0
    return acc
  | ``Prod, .list xs => do
    if xs.size < 2 then throwError "sexp%: expected a pair, got {e.toString}"
    let a ← build args[0]! xs[0]!
    let b ← build args[1]! (if xs.size == 2 then xs[1]! else .list (xs.extract 1 xs.size))
    return mkApp4 (Lean.mkConst ``Prod.mk lvls) args[0]! args[1]! a b
  | _, _ => buildCtor ty n lvls args e

/-- A constructor of the inductive type `I` applied to the arguments `e`
    describes. -/
partial def buildCtor (ty : Expr) (I : Name) (lvls : List Level) (args : Array Expr) (e : Sexp) : M Expr := do
  let some (.inductInfo info) := (← getEnv).find? I | throwError "sexp%: {ty} is not an inductive type"
  let params := args.extract 0 info.numParams
  let ctorOf (s : String) : Option Name :=
    let c := I ++ Name.mkSimple s
    if info.ctors.contains c then some c else none
  let (ctor, xs) ← match e with
    | .atom s =>
      match ctorOf s with
      | some c => pure (c, #[])
      | none => throwError "sexp%: no constructor '{s}' of {I}"
    | .list xs =>
      match xs[0]? with
      | some (Sexp.atom s) =>
        match ctorOf s with
        | some c => pure (c, xs.extract 1 xs.size)
        | none =>
          if info.ctors.length == 1 then pure (info.ctors[0]!, xs)
          else throwError "sexp%: no constructor '{s}' of {I}"
      | _ =>
        if info.ctors.length == 1 then pure (info.ctors[0]!, xs)
        else throwError "sexp%: expected a constructor of {I}, got {e.toString}"
  -- a structure with its fields named: `((field value) …)`, in any order
  let xs ← if isStructure (← getEnv) I && ctor == info.ctors[0]! && !xs.isEmpty then do
      let fields := getStructureFields (← getEnv) I
      let named := xs.filterMap fun
        | .list #[.atom f, v] => if fields.contains (Name.mkSimple f) then some (Name.mkSimple f, v) else none
        | _ => none
      if named.size == xs.size then
        fields.mapM fun f => match named.find? (·.1 == f) with
          | some (_, v) => pure v
          | none => throwError "sexp%: no field '{f}' for {I}"
      else pure xs
    else pure xs
  let mut c := mkAppN (Lean.mkConst ctor lvls) params
  let mut t ← instantiateForall (← inferType (Lean.mkConst ctor lvls)) params
  for x in xs do
    let t' ← whnf t
    let .forallE _ d b _ := t' | throwError "sexp%: too many arguments for {ctor}: {e.toString}"
    let a ← build d x
    c := mkApp c a
    t := b.instantiate1 a
  if (← whnf t).isForall then throwError "sexp%: too few arguments for {ctor}: {e.toString}"
  return c

end

syntax (name := sexpElab) "sexp% " str : term

/-- `sexp% "…"`: the term of the expected type that the S-expression describes. -/
@[term_elab sexpElab] def elabSexp : TermElab := fun stx expectedType? => do
  let some ty := expectedType? | throwError "sexp%: the expected type is unknown"
  let some s := stx[1].isStrLit? | throwError "sexp%: expected a string literal"
  match parse s with
  | .ok e => do
    let ty ← instantiateMVars ty
    let opts ← getOptions
    let chunk := if ty.hasMVar || ty.hasFVar then 0 else vik.sexp.chunk.get opts
    let base := (← getDeclName?).getD `sexp
    (build ty e).run' { chunk, base }
  | .error m => throwError "sexp%: {m}"

end Vik.Sexp
