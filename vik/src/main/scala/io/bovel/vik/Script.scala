package io.bovel.vik

import io.bovel.smtlib.sexpr.SExpr

/** A command of a lowered script: the player's instruction set, over the
 *  solver's [[Term]]s and [[Formula]]s. [[Lowering]] produces these from the
 *  surface commands of `io.bovel.smtlib`.
 */
enum Command:
  case SetLogic(logic: String)
  case SetInfo(key: String, value: String)
  case DeclareSort(name: String, arity: Int)

  /** `auxiliary`: a bit the lowering introduced to define a bitwise operation,
   *  not a constant the problem reasons about — the search decides its atoms
   *  last (see [[Solver.declare]]).
   */
  case DeclareFun(name: String, argSorts: List[Sort], sort: Sort, auxiliary: Boolean = false)
  case DeclareDatatypes(datatypes: List[Datatype])

  /** The declaration of a `.array.map!N` symbol of sort `sort`, with what the
   *  map holds at an index. It is the lowering's and stays declared past the
   *  `pop` of its level, as the symbol stays the lowering's for the operator.
   */
  case DeclareMap(name: String, sort: Sort, pointwise: Pointwise)

  /** That the index sort `sort` of a constant array or a map has `size` values,
   *  the `k`-th of which `value(k)` builds (for `0 ≤ k < size`): the
   *  lowering's, which counts the values of a datatype, and kept past the `pop`
   *  of its level, as a [[DeclareMap]] is.
   */
  case DeclareFinite(sort: Sort, size: BigInt, value: BigInt => Term)
  case Assert(formula: Formula)

  /** `(assert (! formula :named name))`: an assertion that [[GetUnsatCore]] can
   *  name.
   */
  case AssertNamed(name: String, formula: Formula)
  case CheckSat

  /** `check-sat-assuming`: `check-sat` with the assumptions asserted in a level
   *  of their own.
   */
  case CheckSatAssuming(assumptions: List[Formula])
  case Push(levels: Int)
  case Pop(levels: Int)

  /** `reset-assertions`: the assertions and levels go, the declarations stay.
   */
  case ResetAssertions

  /** `reset`: everything goes. */
  case Reset
  case GetModel

  /** `get-value`: each item as written (for the echo) and as lowered. */
  /** `definitions`: the defining assertions of the fresh constants the items
   *  introduced (a term-level `ite`), evaluated under the model, not asserted.
   */
  case GetValue(items: List[(String, Formula | Term)], definitions: List[Formula])
  case GetUnsatCore

  /** `get-assertions`: the current assertion stack, as the solver holds it —
   *  after the lowerings (bit-vectors to integers, rational literals to
   *  constants).
   */
  case GetAssertions
  case Exit

  /** `set-option`: `:rlimit` (the fuel of each `check-sat`) and `:timeout`
   *  (milliseconds) matter to the player.
   */
  case SetOption(key: String, value: String)

  /** `get-info`: `:reason-unknown` is answered by the player. */
  case GetInfo(key: String)

  /** A command with no effect on solving (`echo`, ...). */
  case Other(sexpr: SExpr)

/** What a map of arrays holds at an index, as a template the solver's array
 *  lemmas instantiate there: `value`, over `params` — a constant standing for
 *  the element of each array at the index, or the numeral that a constant array
 *  of it holds everywhere — and over `auxiliaries`, the constants the lowering
 *  of the operator minted (a quotient, the constant of an `ite`), which
 *  `definitions` define. At an index, each auxiliary is the function declared
 *  here (its name, argument sorts and sort), applied to the elements there.
 *  `sort` is the sort of the map, for the models.
 */
final case class Pointwise(
    params: List[Term],
    auxiliaries: List[(String, List[Sort], Sort)],
    value: Term,
    definitions: List[Formula],
    sort: Sort
):
  /** The template at the elements `elements` of the arrays: the definitions and
   *  the value, with `auxiliary` giving an auxiliary constant there.
   */
  def at(elements: List[Term], auxiliary: (Term.Const, List[Term]) => Term): (List[Formula], Term) =
    val formals = params.zip(elements).collect { case (x: Term.Const, e) => x -> e }
    val (bound, actuals) = (formals.toMap[Term, Term], formals.map(_._2))
    val minted = auxiliaries.map(_._1).toSet
    // With no element left to vary (every array a constant array of a numeral), an auxiliary is a
    // constant: the same everywhere.
    def substitute(t: Term): Term = t match
      case c @ Term.Const(name) =>
        bound.getOrElse(c, if minted(name) && actuals.nonEmpty then auxiliary(c, actuals) else c)
      case Term.App(fun, args) => Term.App(substitute(fun), args.map(substitute))
      case Term.Num(_) => t
      case Term.Linear(terms, constant) => Term.linear(terms.map((a, u) => (a, substitute(u))), constant)
      case Term.Bool(formula) => Term.boolean(formula.mapTerms(substitute))
    (definitions.map(_.mapTerms(substitute)), substitute(value))

  /** The template with its parameters and auxiliaries renamed by their
   *  position: the same for two operators that make the same template, whatever
   *  the names the lowering gave them.
   */
  def canonical: Pointwise =
    val renaming =
      (params.collect { case Term.Const(name) => name }.zipWithIndex.map((n, i) => n -> s"#$i") ++
        auxiliaries.map(_._1).zipWithIndex.map((n, j) => n -> s"#a$j")).toMap
    def rename(t: Term): Term = t match
      case Term.Const(name) => renaming.get(name).fold(t)(Term.Const(_))
      case Term.App(fun, args) => Term.App(rename(fun), args.map(rename))
      case Term.Num(_) => t
      case Term.Linear(terms, constant) => Term.linear(terms.map((a, u) => (a, rename(u))), constant)
      case Term.Bool(formula) => Term.boolean(formula.mapTerms(rename))
    Pointwise(
      params.map(rename),
      auxiliaries.map((n, args, result) => (renaming(n), args, result)),
      rename(value),
      definitions.map(_.mapTerms(rename)),
      sort
    )

final case class Script(commands: List[Command])
