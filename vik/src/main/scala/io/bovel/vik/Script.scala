package io.bovel.vik

import io.bovel.smtlib.Datatype
import io.bovel.smtlib.sexpr.SExpr

/** A command of a lowered script: the player's instruction set, over the
 *  solver's [[Term]]s and [[Formula]]s. [[Lowering]] produces these from the
 *  surface commands of `io.bovel.smtlib`.
 */
enum Command:
  case SetLogic(logic: String)
  case SetInfo(key: String, value: String)
  case DeclareSort(name: String, arity: Int)
  case DeclareFun(name: String, argSorts: List[String], sort: String)
  case DeclareDatatypes(datatypes: List[Datatype])

  /** The declaration of a `map!N` symbol of sort `sort`, with what the map
   *  holds at an index. It is the lowering's and stays declared past the `pop`
   *  of its level, as the symbol stays the lowering's for the operator.
   */
  case DeclareMap(name: String, sort: String, pointwise: Pointwise)
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
 *  `sort` is the sort of the map as SMT-LIB writes it, for the models.
 */
final case class Pointwise(
    params: List[Term],
    auxiliaries: List[(String, List[String], String)],
    value: Term,
    definitions: List[Formula],
    sort: String
):
  /** The template at the elements `elements` of the arrays: the definitions and
   *  the value, with `auxiliary` giving an auxiliary constant there.
   */
  def at(elements: List[Term], auxiliary: (Term.Const, List[Term]) => Term): (List[Formula], Term) =
    val formals = params.zip(elements).collect { case (x: Term.Const, e) => x -> e }
    val (bound, actuals) = (formals.toMap[Term, Term], formals.map(_._2))
    val minted = auxiliaries.map(_._1).toSet
    def substitute(t: Term): Term = t match
      case c @ Term.Const(name) => bound.getOrElse(c, if minted(name) then auxiliary(c, actuals) else c)
      case Term.App(fun, args) => Term.App(substitute(fun), args.map(substitute))
      case Term.Num(_) => t
      case Term.Linear(terms, constant) => Term.linear(terms.map((a, u) => (a, substitute(u))), constant)
      case Term.Bool(formula) => Term.boolean(formula.mapTerms(substitute))
    (definitions.map(_.mapTerms(substitute)), substitute(value))

final case class Script(commands: List[Command])
