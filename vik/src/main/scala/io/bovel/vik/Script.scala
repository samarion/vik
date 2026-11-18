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
  case Assert(formula: Formula)

  /** An assertion below every level, which no `pop` takes back: what a
   *  declaration says of a symbol that outlives the levels under
   *  `:global-declarations` — a bit-vector constant's range, which went with
   *  the level it was asserted in while the constant stayed (issue 145).
   *  Printed `(assert-global F)`: a command of VIK's own, SMT-LIB having none
   *  that asserts below the current level.
   */
  case AssertGlobal(formula: Formula)

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

final case class Script(commands: List[Command])
