package io.bovel.vik
import scala.collection.mutable.ArrayBuffer

import io.bovel.smtlib as s2

/** A solver with the language attached: one parser, one lowering and one
 *  [[Solver]] kept alive together, so a script arrives piece by piece — as
 *  text, as `io.bovel.smtlib` trees or as lowered [[Command]]s — each piece in
 *  the scope the earlier ones declared. The responses come back as SMT-LIB
 *  text, one per command that answers (`check-sat`, `get-model`, ...), and
 *  `(get-info :reason-unknown)` says `resourceout` when the fuel is spent
 *  (`:rlimit`, or `fuel` here), `timeout` when the `:timeout` (milliseconds)
 *  passed, `canceled` when the caller stopped it, and the finding of a failed
 *  model check as a string (below). A whole script in a session of its own is
 *  [[Session.run]], or [[Session.answers]] for just its `check-sat`s.
 *
 *  With `checkModels` on, or `(set-option :check-models true)` (cvc5's name),
 *  each `sat` is checked before it is answered: the solver builds the model,
 *  and the assertions in force, with the assumptions of a `check-sat-assuming`,
 *  are evaluated in it twice. Once as lowered, by the solver itself
 *  ([[Solver.checkModels]]): the search against the problem it was given, which
 *  also covers lowered commands given to [[play]]. Once as the script wrote
 *  them, the way `get-value` evaluates an item: the lowering along with the
 *  search. When an assertion is not true at either level (false, or beyond the
 *  evaluation), the answer is `unknown`, followed by
 *  `(error "model check: ...")` naming the assertion — a bug of VIK, to report
 *  — which `(get-info :reason-unknown)` repeats, and there is no model. It is
 *  off by default, since it costs a model per sat and two walks of the
 *  assertions.
 *
 *  {{{
 *  val s = Session()
 *  s.run("(declare-const x Int) (declare-const y Int)")
 *  s.assert("(< x y)")
 *  s.checkSat() // Some(true)
 *  }}}
 */
final class Session(
    initial: Solver = Solver(),
    fuel: Long = Long.MaxValue,
    timeoutMs: Option[Long] = None,
    deadline: Option[Long] = None, // a point in `System.nanoTime`: no check-sat searches past it
    checkModels: Boolean = false // every sat's model checked against the assertions (see above)
):
  private val parser = s2.Parser()
  private val lowerer = Lowerer()
  private var current = initial
  private var checking = checkModels
  current.produceModels = false // a walk per sat: paid only once the commands ask (see play)
  current.checkModels = checking

  /** The solver underneath (`reset` replaces it). */
  def solver: Solver = current

  // The assertion stack as asserted, one buffer per level: what get-assertions prints.
  private val asserted = ArrayBuffer(ArrayBuffer.empty[Formula])
  // The same stack as the script wrote it, what the model check evaluates; `play` keeps its levels.
  private val written = ArrayBuffer(ArrayBuffer.empty[s2.Formula])
  private val declarations = ArrayBuffer.empty[Command] // replayed by `reset-assertions`
  // The declarations of each open level, undone with its `pop` unless `:global-declarations` is true
  // (issue 40); the first level's are never popped.
  private val declaredAt = ArrayBuffer(ArrayBuffer.empty[Command])
  private var globalDeclarations = false
  private var rlimit = fuel
  private var timeout = timeoutMs // milliseconds per check-sat, as `(set-option :timeout ...)` sets it
  private var reason = Option.empty[String]
  private var replaced = -initial.spent // the work of the solvers `reset` replaced, less the initial one's before

  /** The work the session did so far, in the units of the fuel (see
   *  [[Solver.spent]]), the same on every machine: its solvers', and the
   *  lowering's, which no `check-sat` budget covers.
   */
  def spent: Long = replaced + current.spent + lowerer.visits * Solver.loweredCost

  /** How much of each kind of work the session's solvers did (see
   *  [[Solver.statistics]]), and the terms and formulas it lowered.
   */
  def statistics: List[(String, Long)] =
    current.statistics.lazyZip(replacedCounts).map((kv, r) => (kv._1, kv._2 + r)) :+ ("lowered" -> lowerer.visits)
  private val replacedCounts = new Array[Long](Solver.kinds.length)

  /** Runs SMT-LIB text, any commands, and answers it. */
  def run(text: String): List[String] = run(parser.parse(text))
  def run(script: s2.Script): List[String] =
    // Models cost a walk per sat, and the script says up front whether it will ask for one.
    if script.commands.exists {
        case s2.Command.GetModel | s2.Command.GetValue(_) => true
        case s2.Command.SetOption(":produce-models", "true") => true
        case _ => false
      }
    then current.produceModels = true
    script.commands.flatMap(command)

  /** One surface command, lowered and played. `get-value` is answered here and
   *  not by the lowered command: the value of a term the lowering gives fresh
   *  constants — every bit-vector operation — is not in the model, which knows
   *  the declared symbols; the lowering computes it from them instead
   *  ([[Lowerer.evaluate]]), and the lowered command answers what it cannot.
   */
  private def command(c: s2.Command): List[String] = c match
    case s2.Command.GetValue(items) =>
      val lowered = lowerer.commands(List(c))
      play(lowered.init) // the declarations the lowering minted, kept whichever way the query is answered
      current.model() match
        case Some(m) =>
          List(items.map((source, item) => s"($source ${lowerer.evaluate(item, m)})").mkString("(", " ", ")"))
        case None => play(List(lowered.last))
    case s2.Command.Assert(f) => asserting(c, f)
    case s2.Command.AssertNamed(_, f) => asserting(c, f)
    case s2.Command.CheckSat => checked(play(lowerer.commands(List(c))), Nil)
    case s2.Command.CheckSatAssuming(assumptions) => checked(play(lowerer.commands(List(c))), assumptions)
    case _ => play(lowerer.commands(List(c)))

  private def asserting(c: s2.Command, formula: s2.Formula): List[String] =
    val responses = play(lowerer.commands(List(c)))
    written.last += formula // once lowered and asserted: an assertion the lowering refuses is not in force
    responses

  /** A check-sat's responses, and in the model-check mode, when the solver
   *  answered `sat` (its own check of the lowered assertions passed, see
   *  [[Solver.checkModels]]), the check of the assertions in force and the
   *  assumptions as written: evaluated by the lowering's evaluation that
   *  `get-value` uses, so that a wrong lowering shows. The first one that is
   *  not true turns the answer into `unknown`, with the error.
   */
  private def checked(responses: List[String], assumptions: List[s2.Formula]): List[String] =
    if !checking || !responses.contains("sat") then responses
    else
      val items = written.flatten.zipWithIndex.map((f, i) => (s"assertion ${i + 1}", f)) ++
        assumptions.zipWithIndex.map((f, i) => (s"assumption ${i + 1}", f))
      val found = current.model() match
        case None => Some("no model")
        case Some(m) =>
          items.iterator.flatMap { (what, f) =>
            val value =
              try lowerer.evaluate(f, m)
              catch case e: Exception => s"not evaluable (${e.getClass.getSimpleName}: ${e.getMessage})"
            Option.when(value != "true") {
              val text = s2.Printer.print(f)
              s"$what ${if text.length > 200 then text.take(200) + "..." else text} is $value"
            }
          }.nextOption()
      found match
        case None => responses
        case Some(what) =>
          failed(what)
          lastCheck = "unknown"
          current.dropModel()
          responses.map(r => if r == "sat" then "unknown" else r) ++ modelError

  // The model check's finding at the last check-sat, at either level: the reason of its `unknown`.
  private var failure = Option.empty[String]
  private def failed(what: String): Unit =
    failure = Some(what)
    reason = Some(quoted(s"model check: $what"))
  private def modelError: Option[String] = failure.map(f => s"(error ${quoted(s"model check: $f")})")
  private def quoted(text: String): String = "\"" + text.replace("\"", "\"\"") + "\""

  def assert(text: String): Unit = run(s"(assert $text)")
  def assert(formula: s2.Formula): Unit = run(s2.Script(List(s2.Command.Assert(formula))))
  // Through the lowerer, like the script commands: a `pop` drops the memo entries whose defining
  // assertions die with the level, and a `pop` that bypassed it left a cached rational constant
  // without its definition (issue 22).
  def push(): Unit = run(s2.Script(List(s2.Command.Push(1))))
  def pop(): Unit = run(s2.Script(List(s2.Command.Pop(1))))

  /** `check-sat`: `Some(true)` for sat, `None` for unknown. */
  def checkSat(): Option[Boolean] = decision(checked(play(List(Command.CheckSat)), Nil))

  /** `check-sat-assuming`: [[checkSat]] with `assumptions` holding for this
   *  check alone.
   */
  def checkSatAssuming(assumptions: List[s2.Formula]): Option[Boolean] =
    decision(run(s2.Script(List(s2.Command.CheckSatAssuming(assumptions)))))

  private def decision(responses: List[String]): Option[Boolean] = Session.decisions(responses).head

  /** The model of the last `check-sat`, when it was sat and models were asked
   *  for — `(set-option :produce-models true)`, or a `get-model` or `get-value`
   *  anywhere in the commands given so far: a script that never asks pays
   *  nothing for them.
   */
  def model(): Option[Model] = current.model()
  def unsatCore: List[String] = current.unsatCore

  // What the last check-sat answered: a core is asked for after an unsat one, and before anything that
  // changes the problem — an assertion, a declaration, a level, a reset — which SMT-LIB makes an error
  // and VIK answered with the stale core (issue 51).
  private var lastCheck = ""

  private def answer(): String =
    val a = answered()
    lastCheck = a
    a

  private def answered(): String =
    val s = current
    // The check-sat's own timeout, and the session's deadline: whichever comes first.
    val stop = (timeout.map(ms => System.nanoTime() + ms * 1000000).toList ++ deadline).minOption
    val start = s.spent
    val limit = rlimit
    var calls = 0
    var late = false
    var out = false
    reason = None
    failure = None
    s.solve(() =>
      calls += 1
      if (calls & 15) == 1 then // the first step and every 16th: the sum is a dozen products, the clock a system call
        late = stop.exists(_ < System.nanoTime())
        out = s.spent - start > limit
      !out && !late
    ) match
      case s.Result.Sat => "sat"
      case s.Result.Unsat => "unsat"
      case s.Result.Unknown(s.Reason.Model(what)) =>
        failed(s"lowered $what")
        "unknown"
      case s.Result.Unknown(_) =>
        reason = Some(if late then "timeout" else if out then "resourceout" else "canceled")
        "unknown"

  private def declare(command: Command): Unit = command match
    case Command.DeclareFun(name, argSorts, sort) => current.declare(name, argSorts, sort)
    case Command.DeclareMap(name, sort, pointwise) => current.declare(name, sort, pointwise)
    case Command.DeclareDatatypes(datatypes) => datatypes.foreach(current.declare)
    case _ => ()

  private def undeclare(command: Command): Unit =
    command match
      case Command.DeclareFun(name, _, _) => current.undeclare(name)
      case Command.DeclareDatatypes(datatypes) => datatypes.foreach(current.undeclare)
      case _ => ()
    val i = declarations.lastIndexOf(command)
    if i >= 0 then declarations.remove(i)

  private def withModel(text: Model => String): String = current.model().map(text).getOrElse("(error \"no model\")")

  /** The model with a fresh constant valued by its definition — `k = t`, or
   *  `c ⇒ k = t` when `c` holds — the way the lowering states one for a
   *  term-level `ite`; another shape defines nothing.
   */
  private def valueText(m: Model, item: Formula | Term): String = item match
    case f: Formula => if m.holds(f) then "true" else "false"
    case t: Term => Printer.print(m.value(t))

  /** The model as SMT-LIB text: a define-fun per declared constant and per
   *  declared function (an ite chain over its graph); the interpreted symbols
   *  of the datatypes stay out.
   */
  private def modelText(m: Model): String =
    val interpreted =
      current.datatypes.flatMap(_.constructors).flatMap(c => c.name :: c.tester :: c.selectors.map(_._1)).toSet
    // The script's symbols, at the sorts the script declared them, their values written as the script
    // would: a bit-vector constant is `(_ BitVec 4)` and `#b1010`, not the `Int` and `10` the lowering
    // reads it as (issue 28). The lowering's own constants stay out, as do the datatypes' symbols.
    def written(v: Term, sort: s2.Sort): String = lowerer.written(v, sort)
    val constants = m.constants.toList.filterNot((n, _) => interpreted(n)).sortBy(_._1).flatMap { (n, v) =>
      lowerer.declaredSort(n).map(sort => s"(define-fun ${Printer.symbol(n)} () ${sort.text} ${written(v, sort)})")
    }
    val functions = m.functions.toList.filterNot((n, _) => interpreted(n)).sortBy(_._1).flatMap { (n, f) =>
      lowerer.declaredSort(n).map { sort =>
        val (argSorts, result) = sort match
          case s2.Sort.Fun(args, r) => (args, r)
          case other => (Nil, other)
        val (params, body) = lowerer.graph(f, argSorts, result)
        s"(define-fun ${Printer.symbol(n)} ($params) ${result.text} $body)"
      }
    }
    (constants ++ functions).mkString("(", " ", ")")

  private def restart(): Unit =
    asserted.clear(); asserted += ArrayBuffer.empty
    written.clear(); written += ArrayBuffer.empty
    declaredAt.clear(); declaredAt += ArrayBuffer.empty
    val produceModels = current.produceModels
    replaced += current.spent
    for ((_, n), i) <- current.statistics.zipWithIndex do replacedCounts(i) += n
    current = Solver(simplify = current.simplify)
    current.produceModels = produceModels
    current.checkModels = checking

  /** Plays lowered commands. */
  def play(commands: List[Command]): List[String] =
    val responses = ArrayBuffer.empty[String]
    // Models cost a walk per sat: taken only once the script asks for them.
    if commands.exists {
        case Command.GetModel | Command.GetValue(_, _) | Command.SetOption(":produce-models", "true") => true
        case _ => false
      }
    then current.produceModels = true
    for command <- commands do
      command match
        case Command.DeclareFun(_, _, _) | Command.DeclareDatatypes(_) =>
          lastCheck = ""
          declarations += command
          if declaredAt.length > 1 && !globalDeclarations then declaredAt.last += command
          declare(command)
        case Command.DeclareMap(_, _, _) => // kept past the pop of its level: the lowering keeps the symbol
          lastCheck = ""
          declarations += command
          declare(command)
        case Command.Assert(formula) =>
          lastCheck = ""
          asserted.last += formula
          current.assert(formula)
        case Command.AssertGlobal(formula) =>
          lastCheck = ""
          asserted.head += formula
          current.assertGlobal(formula)
        case Command.AssertNamed(name, formula) =>
          lastCheck = ""
          asserted.last += formula
          current.assert(formula, name)
        case Command.GetUnsatCore =>
          responses +=
            (if lastCheck == "unsat" then current.unsatCore.mkString("(", " ", ")")
             else "(error \"unsat core is not available\")") // SMT-LIB: after an unsat check only
        case Command.GetAssertions =>
          responses += asserted.flatten.map(Printer.print).mkString("(", " ", ")")
        case Command.GetValue(items, definitions) =>
          responses += withModel { m0 =>
            val m = lowerer.fold(m0, definitions)
            items.map((src, it) => s"($src ${valueText(m, it)})").mkString("(", " ", ")")
          }
        case Command.GetModel => responses += withModel(modelText)
        case Command.Push(n) =>
          lastCheck = ""
          for _ <- 0 until n do
            current.push()
            asserted += ArrayBuffer.empty
            written += ArrayBuffer.empty
            declaredAt += ArrayBuffer.empty
        // More levels than are open: an error, and nothing changes, as z3 answers it (issue 178). The levels
        // are the ones since the last `reset-assertions`, which drops them all.
        case Command.Pop(n) if n > asserted.length - 1 =>
          responses += s"(error \"pop $n: the stack depth is ${asserted.length - 1}\")"
        case Command.Pop(n) =>
          lastCheck = ""
          for _ <- 0 until n do
            current.pop()
            if declaredAt.length > 1 then declaredAt.remove(declaredAt.length - 1).reverseIterator.foreach(undeclare)
          asserted.dropRightInPlace(n min (asserted.length - 1))
          written.dropRightInPlace(n min (written.length - 1))
        case Command.CheckSat => responses ++= answer() :: modelError.toList
        case Command.CheckSatAssuming(assumptions) =>
          current.push()
          assumptions.foreach(current.assert)
          responses ++= answer() :: modelError.toList
          current.pop()
        case Command.ResetAssertions =>
          lastCheck = ""
          restart()
          declarations.foreach(declare)
        case Command.Reset =>
          lastCheck = ""
          restart()
          declarations.clear()
          globalDeclarations = false
        case Command.SetOption(":global-declarations", value) => globalDeclarations = value == "true"
        case Command.SetOption(":rlimit", value) => rlimit = value.toLong
        case Command.SetOption(":timeout", value) => timeout = Some(value.toLong)
        case Command.SetOption(":check-models", value) =>
          checking = value == "true"
          current.checkModels = checking
        case Command.GetInfo(":reason-unknown") => responses += s"((:reason-unknown ${reason.getOrElse("incomplete")}))"
        case _ => ()
    responses.toList

object Session:
  /** Runs a whole script in a session of its own: the responses, each
   *  `check-sat` with `fuel` steps and, when given, `timeoutMs` milliseconds,
   *  none of them past `deadline` (a `System.nanoTime` point: the budget of the
   *  whole script, which a script of many check-sats must not multiply). The
   *  search stops by itself at any of the three: nothing has to interrupt it.
   */
  def run(
      script: s2.Script,
      fuel: Long = Long.MaxValue,
      timeoutMs: Option[Long] = None,
      deadline: Option[Long] = None,
      checkModels: Boolean = false
  ): List[String] =
    Session(fuel = fuel, timeoutMs = timeoutMs, deadline = deadline, checkModels = checkModels).run(script)

  /** The answer of each `check-sat` of a script run in a session of its own:
   *  `Some(true)` for sat, `None` for unknown (the `fuel` of the `check-sat` is
   *  spent, or its time, see `Solver.solve`).
   */
  def answers(
      script: s2.Script,
      fuel: Long = Long.MaxValue,
      timeoutMs: Option[Long] = None,
      deadline: Option[Long] = None,
      checkModels: Boolean = false
  ): List[Option[Boolean]] = decisions(run(script, fuel, timeoutMs, deadline, checkModels))

  /** The check-sat answers among responses. */
  private def decisions(responses: List[String]): List[Option[Boolean]] =
    responses.collect {
      case "sat" => Some(true)
      case "unsat" => Some(false)
      case "unknown" => None
    }
