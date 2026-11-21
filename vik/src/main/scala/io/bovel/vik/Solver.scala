package io.bovel.vik

import scala.collection.immutable.ArraySeq
import scala.collection.mutable.{ArrayBuffer, HashMap, HashSet}
import scala.util.boundary
import scala.util.boundary.break

import io.bovel.cdclt
import io.bovel.cdclt.{Lit, Theory}
import io.bovel.egraph.{App, EClassId, EGraph, NoRules}
import io.bovel.lia

/** An SMT solver for quantifier-free formulas over equality with uninterpreted
 *  functions and linear integer arithmetic: `assert` formulas, `push` and `pop`
 *  levels of assertions, and `solve`. Each `solve` simplifies the assertions of
 *  all levels (see [[Simplifier]], unless `simplify` is false) and encodes them
 *  afresh into a [[cdclt.Solver]] (Tseitin encoding, one CDCL(T) variable per
 *  distinct atom and per compound subformula) with a [[UfTheory]] over an
 *  [[io.bovel.egraph.EGraph]] for the equalities and a [[LiaTheory]] over a
 *  [[lia.Solver]] for the bounds. The theories are combined over the shared
 *  numeric terms — the ones under uninterpreted functions or compared by
 *  equality: every pair of shared terms that can meet gets its equality as an
 *  atom of both theories, and the SAT solver decides the arrangement (Nelson
 *  and Oppen; see `Encoder.shareIntegers`).
 */
final class Solver(val simplify: Boolean = true):
  enum Result:
    case Sat
    case Unsat

    /** No answer, for a [[Reason]] (SMT-LIB's `unknown` and `:reason-unknown`).
     */
    case Unknown(reason: Reason)

  enum Reason:
    /** The fuel of [[solve]] is spent (`resourceout`). */
    case Fuel

    /** The caller's `keepGoing` of [[solve]] said to stop: a deadline, a
     *  cancellation.
     */
    case Stopped

    /** With [[checkModels]]: the search found the assertions satisfiable, and
     *  the model it built does not make one of them true, which `failure`
     *  names. A bug of the solver, in the search or in the model, to report.
     */
    case Model(failure: String)

  private val levels = ArrayBuffer(ArrayBuffer.empty[Formula])

  /** The persistent encoder, built at the first [[solve]] — so that the first
   *  batch is simplified as a whole — and kept across `check-sat`s: terms,
   *  clauses and everything the search learned survive. A formula asserted at a
   *  level above the first is guarded by the level's selector literal, and
   *  [[pop]] retires the selector; [[solve]] assumes the open ones.
   */
  private var encoder: Encoder | Null = null
  private val selectors = ArrayBuffer.empty[Lit]

  /** The constants the first batch's simplification eliminated, and whether the
   *  encoder must be rebuilt (a new assertion mentions one — the elimination
   *  was only sound without such a mention — or a datatype arrived after
   *  encoding began). The rebuild re-encodes [[levels]] and drops what was
   *  learned.
   */
  private var eliminated: Map[String, Term] = Map.empty
  private var dirty = false

  /** The declared function symbols (argument sorts, result sort) and datatypes.
   *  Declarations are optional for uninterpreted functions and integers, and
   *  needed for datatypes: they tell which terms are of a datatype sort.
   */
  private[vik] val declarations = HashMap.empty[String, (List[Sort], Sort)]
  private[vik] val datatypes = ArrayBuffer.empty[Datatype]
  private val auxiliaries = HashSet.empty[String] // the declared constants that only define an operation (see declare)

  /** `auxiliary`: a constant that only defines an operation of the problem (a
   *  bit of the bit-vector lowering). The search decides the bounds on such
   *  constants after every other atom: their values follow from the problem's
   *  own terms, and a search that guesses them first enumerates bit patterns
   *  through the simplex, with conflicts as wide as the bit-vector. Only the
   *  bits: deferring the quotients, the remainders and the results of the
   *  modular operations too loses the searches for a model that need them early
   *  (BinarySearch, in the corpus).
   */
  def declare(name: String, argSorts: List[Sort], sort: Sort, auxiliary: Boolean = false): Unit =
    if encoder != null && encoder.nn.introducedName(name) then
      throw io.bovel.smtlib.Smt2Error(s"$name: a name the solver uses; pick another")
    // A name the live encoder knows at another sort — declared again after the pop of its level (issue
    // 40): the encoder's sort, class and variable for it are the old symbol's, so it is rebuilt.
    if encoder != null && encoded.get(name).exists(_ != (argSorts, sort)) then dirty = true
    declarations(name) = (argSorts, sort)
    if auxiliary then auxiliaries += name else auxiliaries -= name
    if encoder != null then encoded(name) = (argSorts, sort)
    facts -= name
    sort match
      case Sort.IntRange(lower, upper) if argSorts.isEmpty =>
        val constant = Term.Const(name)
        val range = Formula.And(List(Formula.Le(Term.Num(lower), constant), Formula.Le(constant, Term.Num(upper))))
        facts(name) = Fact(range, levels.length - 1, levels.last.length)
        val e = encoder
        if e != null && !dirty then e.assert(range, null)
      case _ => ()
    if Names.isArrayOperation(name) then anyStore = true

  /** What the sort of a declared constant says of it: a constant of a range of
   *  the integers ([[Sort.IntRange]], what a bit-vector sort is to the solver)
   *  lies in the range, `0 ≤ c < 2^n` for `n` bits. A fact of the declaration
   *  and not an assertion: it holds below every level, for as long as the
   *  constant is declared, and no [[pop]] takes it back (issue 145). The terms
   *  that have no declaration of their own get theirs from the encoder
   *  (`Encoder.assertSorts`).
   *
   *  Each fact with the place of its declaration among the assertions, its
   *  level and the number of assertions the level had: an encoder built later
   *  meets the fact there. The search follows the order of the encoding, and
   *  the ranges met after the assertions that use their constants cost files of
   *  the corpus ten times their time.
   */
  private final case class Fact(formula: Formula, level: Int, index: Int)
  private val facts = scala.collection.mutable.LinkedHashMap.empty[String, Fact]

  /** What each declared map of arrays holds at an index (see [[Pointwise]]). */
  private[vik] val maps = HashMap.empty[String, Pointwise]

  /** The finite index sorts of the constant arrays and maps other than `Bool`
   *  and the ranges of the integers: how many values each has, and how to build
   *  the `k`-th (see [[Command.DeclareFinite]]).
   */
  private[vik] val finiteSorts = HashMap.empty[Sort, (BigInt, BigInt => Term)]

  /** Their counts, by their text, which the model's arrays carry. */
  private[vik] val finiteSizes = HashMap.empty[String, BigInt]

  /** The constants a map's template mentions, other than its own parameters and
   *  auxiliaries.
   */
  private def templateConstants(pointwise: Pointwise): Set[String] =
    (pointwise.value :: pointwise.definitions.flatMap(_.terms)).flatMap(Term.constants).toSet --
      pointwise.params.collect { case Term.Const(n) => n } -- pointwise.auxiliaries.map(_._1)

  def declareFinite(sort: Sort, size: BigInt, value: BigInt => Term): Unit =
    if finiteSorts.contains(sort) then dirty = true // a sort of its name declared anew, after a pop
    finiteSorts(sort) = (size, value)
    finiteSizes(sort.text) = size

  /** Declares a map of arrays: the symbol, and the auxiliaries of what it holds
   *  at an index, each a function of the elements there.
   */
  def declare(name: String, sort: Sort, pointwise: Pointwise): Unit =
    // A template that mentions a constant the simplification eliminated is a mention of it, like an
    // assertion's (see mentionsEliminated): the template is not substituted into.
    if encoder != null && !dirty && templateConstants(pointwise).exists(eliminated.contains) then dirty = true
    maps(name) = pointwise
    for (auxiliary, argSorts, result) <- pointwise.auxiliaries do declare(auxiliary, argSorts, result)
    declare(name, Nil, sort)

  /** The declarations the live encoder was given, as given: what a declaration
   *  after a pop is held against.
   */
  private val encoded = HashMap.empty[String, (List[Sort], Sort)]

  /** Forgets a declaration: its level is popped (issue 40). */
  def undeclare(name: String): Unit =
    declarations -= name
    facts -= name
    auxiliaries -= name

  /** Forgets a datatype: its level is popped. The live encoder still holds its
   *  rules and the exhaustiveness of its sort, and would apply them to a sort
   *  or to symbols declared later under the same names (issue 144): it is
   *  rebuilt.
   */
  def undeclare(datatype: Datatype): Unit =
    if encoder != null then dirty = true
    datatypes.filterInPlace(_.name != datatype.name)
    for c <- datatype.constructors do
      declarations -= c.name
      declarations -= c.tester
      for (selector, _) <- c.selectors do declarations -= selector

  /** Whether a `store` has been declared: a flag kept here, since the array
   *  passes ask at every round of the lemma loop and a scan of the
   *  declarations, free under HotSpot, cost the native image a third of the
   *  corpus; a value memoized at the first solve missed the stores declared
   *  after it (issue 13).
   */
  private[vik] var anyStore = false

  /** Declares a datatype: its constructors, selectors and testers become known
   *  function symbols.
   *
   *  The datatype must be well-founded: one of its constructors takes only
   *  fields that have values without it, the datatypes declared before having
   *  some. The solver assumes it, and builds the default values of its models
   *  from such constructors: a datatype without values would leave a model with
   *  nothing to give its terms. The parser refuses a script's datatype that is
   *  not well-founded, as SMT-LIB asks (`Parser.wellFounded`, issue 147); a
   *  datatype declared here directly is not checked.
   */
  def declare(datatype: Datatype): Unit =
    if encoder != null then dirty = true // its rules and exhaustiveness need an encoder that knows it
    datatypes += datatype
    for c <- datatype.constructors do
      declarations(c.name) = (c.selectors.map(_._2), Sort.Named(datatype.name))
      declarations(c.tester) = (List(Sort.Named(datatype.name)), Sort.Bool)
      for (selector, sort) <- c.selectors do declarations(selector) = (List(Sort.Named(datatype.name)), sort)

  def push(): Unit =
    levels += ArrayBuffer.empty
    named += ArrayBuffer.empty
    val e = encoder
    if e != null && !dirty then selectors += e.newSelector()

  def pop(): Unit =
    require(levels.length > 1, "pop without a matching push")
    levels.remove(levels.length - 1)
    named.remove(named.length - 1)
    val e = encoder
    if e != null && !dirty && selectors.length >= levels.length then
      e.retire(selectors.remove(selectors.length - 1))

  /** The named assertions (SMT-LIB `:named`) per level — each one's activation
   *  literal is assumed at every solve while its level is open — and the names
   *  of the last `Unsat`'s core.
   */
  private val named = ArrayBuffer(ArrayBuffer.empty[(String, Formula)])
  private var lastCore: List[String] = Nil

  /** Whether a `Sat` takes its model (see [[model]]): taking one walks the
   *  declarations and the classes, which a caller that never asks should not
   *  pay for — the SMT-LIB player turns this on only when the script asks.
   */
  var produceModels: Boolean = true

  /** Whether a `Sat` is checked before it is answered: the model is built and
   *  every assertion in force, as given to [[assert]] (before the
   *  simplification), must hold in it ([[Model.holds]]). When one does not, the
   *  answer is `Unknown` with [[Reason.Model]], and there is no model. Off by
   *  default: it costs a model and a walk of the assertions per `Sat`.
   */
  var checkModels: Boolean = false

  /** The first assertion in force that the model of the `Sat` just found does
   *  not make true: found false, or not evaluable when the evaluation throws.
   *  The ranges of the declared constants count among them. Or else the first
   *  declared symbol with a value that is none of its sort's
   *  ([[Model.ofSort]]): what a sort says of the terms the solver makes is no
   *  assertion.
   */
  private def modelFailure(): Option[String] = model() match
    case None => Some("no model")
    case Some(m) =>
      val items = levels.iterator.flatten.zipWithIndex.map((f, i) => (s"assertion ${i + 1}", f)) ++
        named.iterator.flatten.map((name, f) => (s"assertion $name", f)) ++
        facts.iterator.map((name, fact) => (s"the range of $name", fact.formula))
      val untrue = items.flatMap { (what, f) =>
        val value =
          try if m.holds(f) then "true" else "false"
          catch case e: Exception => s"not evaluable (${e.getClass.getSimpleName}: ${e.getMessage})"
        Option.when(value != "true") {
          val text = Printer.print(f)
          s"$what ${if text.length > 200 then text.take(200) + "..." else text} is $value"
        }
      }
      val unsorted = declarations.iterator.flatMap { case (name, (argSorts, sort)) =>
        val values =
          if argSorts.isEmpty then m.constants.get(name).iterator.map((_, sort))
          else
            m.functions.get(name).iterator.flatMap(f =>
              (f.default, sort) :: f.rows.flatMap((args, result) => (result, sort) :: args.zip(argSorts))
            )
        values.collectFirst {
          case (value, s) if !m.ofSort(value, s) => s"the value ${Printer.print(value)} of $name is none of ${s.text}"
        }
      }
      untrue.nextOption().orElse(unsorted.nextOption())

  /** Forgets the model of the last `Sat`: for a caller whose own check of it
   *  failed (see [[Session]]).
   */
  private[vik] def dropModel(): Unit =
    val e = encoder
    if e != null then e.lastModel = null

  /** The model of the last [[solve]]'s `Sat`, or `None` after any other answer:
   *  values for the constants, a finite graph per declared function (see
   *  [[Model]]).
   */
  def model(): Option[Model] =
    Option(encoder).flatMap(e => Option(e.lastModel)).map { m =>
      // The constants the simplification defined away get their definitions' values: the
      // definitions mention only constants the model already has.
      m.copy(constants = m.constants ++ eliminated.map((name, d) => name -> m.value(d)))
    }

  /** The named assertions among the causes of the last [[solve]]'s `Unsat`:
   *  re-asserting just these (with the unnamed assertions) stays `Unsat`. Empty
   *  when the unnamed assertions alone are already `Unsat`.
   */
  def unsatCore: List[String] = lastCore

  /** Asserts `(! formula :named name)`: a part of [[unsatCore]]. */
  def assert(formula: Formula, name: String): Unit =
    named.last += ((name, formula))
    if mentionsEliminated(formula) then dirty = true

  def assert(formula: Formula): Unit =
    levels.last += formula
    val e = encoder
    if mentionsEliminated(formula) then dirty = true
    else if e != null && !dirty then
      e.assert(formula, if levels.length == 1 then null else selectors(levels.length - 2))

  // The elimination assumed the constant stayed local; a mention breaks it: start over.
  private def mentionsEliminated(formula: Formula): Boolean = encoder != null && !dirty
    && eliminated.nonEmpty && formula.terms.exists(Term.constants(_).exists(eliminated.contains))

  /** Decides the assertions with at most `fuel` units of work spent (see
   *  [[spent]]), `Unknown` beyond: deterministic, unlike a deadline, which
   *  [[solve(keepGoing)]] allows.
   */
  def solve(fuel: Long = Long.MaxValue): Result =
    val start = spent
    var calls = 0
    solve(() =>
      calls += 1
      (calls & 15) != 1 || spent - start <= fuel // summed at the first step and every 16th: a dozen products
    ) match
      case Result.Unknown(Reason.Stopped) => Result.Unknown(Reason.Fuel)
      case result => result

  /** Decides the assertions while `keepGoing` says so, asked at every step: a
   *  decision or a conflict of the SAT search, a pivot, a row propagation or a
   *  branch of the LIA solver, every 1024th step of the encoding.
   */
  def solve(keepGoing: () => Boolean): Result =
    val counted = () =>
      steps += 1
      keepGoing()
    asked = counted
    bigWordsStart = lia.Rational.bigWords
    overflowsStart = lia.Rational.overflows
    solving = true
    try decide(counted)
    catch
      case Encoder.Stopped =>
        // The encoder stopped part-way through a pass, with pairs noted and not yet encoded, or half the
        // lemmas of a store: not one to search with, now or later. The next solve builds another.
        encoder.nn.addCounts(retired)
        encoder = null
        lastCore = Nil
        Result.Unknown(Reason.Stopped)
    finally
      bigWords += lia.Rational.bigWords - bigWordsStart
      overflows += lia.Rational.overflows - overflowsStart
      solving = false
      asked = () => true // an assertion between two solves is encoded as it arrives, with no one to ask

  /** The work this solver did so far, in units of about 4 ns of the JVM's time
   *  on the machine the costs were measured on, and the same on every machine:
   *  the steps of [[solve(keepGoing)]] and the work between them — Boolean
   *  propagation, the e-graph's merges, explanations and disequalities, the
   *  atoms the UF theory scans, the explanations of the LIA solver, its
   *  arithmetic past `Long` — and the encoding, each weighted by its cost
   *  ([[Solver.kinds]]). The budget of [[solve(fuel)]] and of `:rlimit`.
   */
  def spent: Long =
    val c = counts
    var sum = 0L
    var i = 0
    while i < c.length do
      sum += c(i) * Solver.costs(i)
      i += 1
    sum

  /** How much of each kind of work this solver did so far, unweighted, in the
   *  order of [[Solver.kinds]].
   */
  def statistics: List[(String, Long)] = Solver.kinds.map(_._1).zip(counts)

  private def counts: Array[Long] =
    val c = retired.clone()
    c(0) += steps
    val e = encoder
    if e != null then e.addCounts(c)
    c(12) += bigWords + (if solving then lia.Rational.bigWords - bigWordsStart else 0)
    c(13) += overflows + (if solving then lia.Rational.overflows - overflowsStart else 0)
    c

  private var steps = 0L
  private val retired = new Array[Long](Solver.kinds.length) // the counts of the encoders replaced
  // The arithmetic past `Long`, counted per thread (see `lia.Rational.bigWords`): the solves' share of it.
  private var bigWords = 0L
  private var overflows = 0L
  private var bigWordsStart = 0L
  private var overflowsStart = 0L
  private var solving = false

  /** The `keepGoing` of the [[solve]] under way, for the encoder (see
   *  `Encoder.step`).
   */
  private var asked: () => Boolean = () => true

  private def decide(keepGoing: () => Boolean): Result =
    if encoder == null || dirty then
      if encoder != null then encoder.nn.addCounts(retired)
      val e = Encoder(
        declarations,
        datatypes.toList,
        auxiliaries,
        maps,
        finiteSorts,
        finiteSizes,
        () => anyStore,
        () => asked()
      )
      encoder = e
      encoded.clear()
      encoded ++= declarations
      dirty = false
      selectors.clear()
      val constructors = datatypes.flatMap(_.constructors.map(_.name)).toSet
      // Each level's assertions in order, the facts of the declarations made in the level among them: a
      // fact before the assertions that came after its declaration. A level's place may have gone with a
      // `pop` since; its facts then come with the last level.
      val placed = facts.values.toList.groupBy(_.level min (levels.length - 1))
      val simplified = levels.length == 1 && simplify
      def encode(level: Int, assertions: List[Formula], selector: Lit | Null): Unit =
        var due = placed.getOrElse(level, Nil).sortBy(_.index)
        for (formula, i) <- assertions.zipWithIndex do
          while due.nonEmpty && due.head.index <= i do
            e.assert(due.head.formula, null)
            due = due.tail
          if formula != Formula.True || !simplified then e.assert(formula, selector) // not one simplified away
        for fact <- due do e.assert(fact.formula, null)
      if simplified then
        // One level: the batch is the whole set, so the global simplification is sound to keep.
        val (assertions, gone) =
          // The constants the maps' templates mention are never eliminated: the templates are left as they are.
          val kept = constructors ++ maps.values.flatMap(templateConstants)
          Simplifier.simplifyEach(levels.head.toList, kept, named.head.map(_._2).toList, e.step)
        eliminated = gone
        encode(0, assertions, null)
      else
        eliminated = Map.empty
        for (level, i) <- levels.zipWithIndex do
          val selector = if i == 0 then null
          else
            selectors += e.newSelector(); selectors.last
          encode(i, level.toList, selector)
    val e = encoder.nn
    e.produceModels = produceModels || checkModels
    val activations = named.flatten.toList.map((name, formula) => (name, e.activate(formula)))
    // The passes feed one another — a shared array pair gets a witness, the witness an index, the index
    // new store lemmas and new shared selects — so they run to a fixpoint of the emitted clauses.
    // The loop asks `keepGoing` like a step of the search: the array lemmas of a file can run past any
    // fuel, and a check-sat over its deadline must end, not run on in a thread the caller gave up on.
    // One round can too, and the passes ask from inside (see `Encoder.step`).
    // The Boolean terms are decided in the loop, first: deciding one encodes the terms inside it,
    // a `store` in a Boolean argument among them, which the passes of the same round then see
    // (issue 17). The loop measures the terms decided as well as the clauses, since a round that
    // registers a Boolean and emits nothing else is not done; and the function equalities, since the
    // sharing makes one per pair of arrays without a clause, and its witness is the next round's
    // (issue 133).
    var emitted = -1
    var decided = -1
    var equated = -1
    def settled = emitted == e.clauseCount && decided == e.booleanCount && equated == e.functionEqualityCount
    while !settled && keepGoing() do
      emitted = e.clauseCount
      decided = e.booleanCount
      equated = e.functionEqualityCount
      e.decideBooleans()
      e.assertExtensionality()
      e.applicationLemmas()
      e.arrayLemmas()
      e.assertSorts()
      e.shareIntegers()
    if !settled then
      // Stopped short of the fixpoint: clauses are missing, and a search over the rest could answer
      // sat without them (issue 38).
      lastCore = Nil
      return Result.Unknown(Reason.Stopped)
    val assumed = ArrayBuffer.from(selectors)
    assumed ++= activations.map(_._2)
    e.solve(assumed, keepGoing) match
      // A `sat` found before the datatype terms had their fields of a finite sort: searched again with them.
      case cdclt.Solver.Result.Sat(_) if e.boundFields() => decide(keepGoing)
      // A `sat` that kept two shared arrays apart before they had a witness: searched again with it.
      case cdclt.Solver.Result.Sat(_) if e.witnessApart() => decide(keepGoing)
      case cdclt.Solver.Result.Sat(_) =>
        lastCore = Nil
        if !checkModels then Result.Sat
        else
          modelFailure() match
            case None => Result.Sat
            case Some(failure) =>
              e.lastModel = null
              Result.Unknown(Reason.Model(failure))
      case cdclt.Solver.Result.Unsat =>
        val core = e.core().toSet
        lastCore = activations.collect { case (name, a) if core(a) => name }
        Result.Unsat
      case cdclt.Solver.Result.Unknown =>
        lastCore = Nil // not the core of an earlier solve (issue 32)
        Result.Unknown(Reason.Stopped)

/** Encodes formulas into clauses over CDCL(T) variables, terms into e-classes
 *  of an e-graph and equalities into atoms of the UF theory, `Int` terms into
 *  variables of a LIA solver and `Le` atoms into bounds on them. Datatypes are
 *  rules of the e-graph ([[AdtRules]]): the encoder registers their symbols'
 *  classes. Every term gets what its sort says of it, whoever made the term:
 *  one of its testers holds for a term of a datatype sort, and a term of a
 *  range of the integers lies in the range. After a `sat`, the terms of a
 *  datatype sort get their fields of a finite sort as terms too, and the search
 *  goes on with them, so that it is complete on finite sorts.
 */
object Solver:
  /** The kinds of work the fuel counts, with the cost of each in the units of
   *  [[Solver.spent]], about 4 ns: fitted to the thread CPU time of the corpus
   *  files on the JVM against the counts of each kind (`bench/README.md`). The
   *  steps are those of [[Solver.solve(keepGoing)]]; a decision and a conflict
   *  cost their step and more (the levels the theories open; the analysis,
   *  learning and backjump); the propagations are the literals assigned, the
   *  clause visits those of the watch lists; the encoder steps are
   *  `Encoder.step`'s; the merge, explanation and disequality work is
   *  `EGraph`'s, the atom scans `UfTheory`'s, the reason and row work the LIA
   *  solver's; the big words and overflows are `lia.Rational`'s.
   */
  val kinds: List[(String, Long)] = List(
    "steps" -> 64,
    "decisions" -> 256,
    "conflicts" -> 4096,
    "propagations" -> 32,
    "clause-visits" -> 2,
    "encoder-steps" -> 48,
    "merge-work" -> 4,
    "explain-work" -> 4,
    "diseq-work" -> 1,
    "atom-scans" -> 1,
    "reason-work" -> 2,
    "row-work" -> 8,
    "big-words" -> 16,
    "overflows" -> 192
  )
  private val costs: Array[Long] = kinds.map(_._2).toArray

  /** The cost of a term or formula lowered (see `Session.spent`). */
  val loweredCost = 64L

private object Encoder:
  /** The sort of a term the declarations say nothing of: an undeclared
   *  constant, an application of one.
   */
  val unknown: Sort = Sort.Named("?")

  /** How many values a sort has, as far as the search needs to know (see
   *  [[Encoder.cardinality]]).
   */
  enum Cardinality:
    case One, Finite, Infinite

  /** Whether the terms of `sort` are numbers, variables of the arithmetic
   *  solver: the integers, the reals, and the ranges of the integers, which is
   *  what the bit-vector sorts are here (see [[Encoder.assertSorts]]).
   */
  def numeric(sort: Sort): Boolean = sort match
    case Sort.Int | Sort.Real | Sort.IntRange(_, _) => true
    case _ => false

  /** Thrown by [[Encoder.step]] when the solve's `keepGoing` says to stop. */
  object Stopped extends scala.util.control.ControlThrowable

private final class Encoder(
    declarations: HashMap[String, (List[Sort], Sort)],
    datatypes: List[Datatype],
    auxiliaries: HashSet[String], // the solver's set, read when a constant gets its LIA variable
    maps: HashMap[String, Pointwise], // what each map of arrays holds at an index
    finiteSorts: HashMap[Sort, (BigInt, BigInt => Term)], // the finite index sorts, their counts, their values
    finiteSizes: HashMap[String, BigInt], // their counts, by their text (see Solver.finiteSizes)
    anyStore: () => Boolean, // the solver's flag, read at every array pass (see Solver.anyStore)
    keepGoing: () => Boolean // of the solve under way (see Solver.solve)
):
  private var steps = 0L

  /** A step of the encoding: a formula encoded, a pair of terms or a term and a
   *  store considered by a pass. The passes are quadratic in the terms, and one
   *  round of them, or the first encoding, can outlast any deadline; so every
   *  1024th step asks `keepGoing`, and a no throws [[Encoder.Stopped]], which
   *  [[Solver.solve]] answers `Unknown` to. Not every step: one is far shorter
   *  than a step of the search, whose fuel this spends.
   */
  def step(): Unit =
    steps += 1
    if (steps & 1023) == 0 && !keepGoing() then throw Encoder.Stopped

  private val classes = HashMap.empty[Term, EClassId]
  private val terms = ArrayBuffer.empty[Term] // the terms of `classes`, in the order they arrived: for the passes
  private val unranged = ArrayBuffer.empty[Term] // the terms of an integer range, as they arrive (see assertSorts)
  private val equalities = ArrayBuffer.empty[Formula] // the equality atoms, as they are encoded (see shareIntegers)
  private var anyArrayApplication = false // an application of a store, a constant array or a map
  // The applications among `terms` by their function, and the stores, constant arrays and maps among them,
  // all in arrival order.
  private val applications = HashMap.empty[Term, ArrayBuffer[Term.App]]
  private val storeTerms = ArrayBuffer.empty[Term.App]
  private val constTerms = ArrayBuffer.empty[Term.App]
  private val mapTerms = ArrayBuffer.empty[Term.App]
  private val arrayOperations = ArrayBuffer.empty[Term.App] // the three, as they arrived
  private val noApplications = ArrayBuffer.empty[Term.App]
  private val sorts = HashMap.empty[Term, Sort] // the sorts of terms, memoized: asked for every term, many times
  private val adt = if datatypes.isEmpty then None else Some(AdtRules())

  private val eg = EGraph(adt.getOrElse(NoRules))
  private val trueTerm = eg.newClass() // the class of Boolean-sorted terms that hold
  private val falseTerm = eg.newClass() // and of those that do not (see [[decideBooleans]])

  adt match
    case Some(adt) =>
      adt.truth(trueTerm)
      for d <- datatypes; c <- d.constructors do
        val constructor = classOf(Term.Const(c.name))
        adt.register(constructor, c.selectors.map((s, _) => classOf(Term.Const(s))), classOf(Term.Const(c.tester)))
        if c.selectors.isEmpty then adt.constant(constructor)
    case _ => ()

  /** The constants this encoder introduces (the witnesses of extensionality),
   *  with their sorts.
   */
  private val introduced = HashMap.empty[String, Sort]

  /** The sort of a term, from the declarations: a function sort for a function
   *  symbol, an array being the function of its index; [[Encoder.unknown]] when
   *  they do not say.
   */
  private def sortOf(term: Term): Sort = sorts.getOrElseUpdate(
    term,
    term match
      case Term.Const(name) =>
        declarations.get(name).map(Sort.fun(_, _)).orElse(introduced.get(name)).getOrElse(Encoder.unknown)
      case Term.App(fun, args) => applied(sortOf(fun), args.length)
      case Term.Num(_) => Sort.Int
      case Term.Linear(terms, _) => if terms.exists((_, t) => sortOf(t) == Sort.Real) then Sort.Real else Sort.Int
      case Term.Bool(_) => Sort.Bool
  )

  /** The sort of a term of `sort` applied to `n` arguments. */
  private def applied(sort: Sort, n: Int): Sort = sort.after(n).getOrElse(Encoder.unknown)

  private val datatypesByName = datatypes.map(d => d.name -> d).toMap

  /** The datatype a sort names, if it names one. */
  private def datatypeOf(sort: Sort): Option[Datatype] = sort match
    case Sort.Named(name) => datatypesByName.get(name)
    case _ => None

  /** The fields that [[shareIntegers]] pairs with their constructor's arguments
   *  (the selector rule): the arithmetic ones and the arrays, each as its
   *  selector, its constructor and its position. Found once: the pass runs at
   *  every round of every check.
   */
  private val sharedFields: List[(Term, Term, Int)] =
    for
      d <- datatypes; c <- d.constructors; ((selector, sort), i) <- c.selectors.zipWithIndex
      if Encoder.numeric(sort) || sort.arrow.isDefined
    yield (Term.Const(selector), Term.Const(c.name), i)

  /** How many values a sort has: one, finitely many, or infinitely many. A
   *  range of the integers and `Bool` are finite; a datatype is when every
   *  field of its constructors is, and has one value when it has one
   *  constructor whose fields have one each; an array has one value when its
   *  elements do, and is finite when its index and its elements are. The
   *  integers, the reals and the uninterpreted sorts are infinite, and so is a
   *  datatype met again inside its own values: a recursive one.
   */
  private val cardinalities = HashMap.empty[Sort, Encoder.Cardinality]

  private def cardinality(sort: Sort): Encoder.Cardinality =
    import Encoder.Cardinality.*
    cardinalities.get(sort) match
      case Some(known) => known
      case None =>
        cardinalities(sort) = Infinite // what the sort is found to be if it is met again below
        val found = sort match
          case Sort.Bool => Finite
          case Sort.IntRange(lower, upper) => if lower == upper then One else Finite
          case Sort.Fun(args, result) =>
            cardinality(result) match
              case One => One
              case Finite if args.forall(cardinality(_) != Infinite) => Finite
              case _ => Infinite
          case _ =>
            datatypeOf(sort) match
              case Some(datatype) =>
                val fields = datatype.constructors.flatMap(_.selectors.map((_, s) => cardinality(s)))
                if fields.contains(Infinite) then Infinite
                else if datatype.constructors.length == 1 && fields.forall(_ == One) then One
                else Finite
              case None => Infinite
        cardinalities(sort) = found
        found

  /** The constructor of each datatype's default value in a model: one without
   *  fields if there is one, else the first whose fields all have a default
   *  already, a least fixpoint. A default built from these is ground: the first
   *  constructor of `((rec (next D)) (base (n Bool)))` leads back to `D`, and
   *  the default ended in an abstract element, `(rec (rec @D!2))` (issue 140).
   *  An array field has the default of its elements everywhere.
   *
   *  Every datatype has one: the solver assumes its datatypes are well-founded
   *  (see [[Solver.declare]]), and a well-founded datatype has a constructor
   *  whose fields all have values without it.
   */
  private val groundConstructors: Map[String, Constructor] =
    var known = Map.empty[String, Constructor]
    def ground(sort: Sort): Boolean = sort match
      case Sort.Fun(_, element) => ground(element)
      case _ => datatypeOf(sort).forall(d => known.contains(d.name))
    var changed = true
    while changed do
      val more =
        for
          d <- datatypes if !known.contains(d.name)
          c <- d.constructors.find(_.selectors.isEmpty).orElse(d.constructors.find(_.selectors.forall((_, s) =>
            ground(s)
          )))
        yield d.name -> c
      changed = more.nonEmpty
      known ++= more
    known

  /** The terms known to be `Int`-sorted from their use in arithmetic (a summand
   *  of a combination, a side of `Le`), for undeclared constants.
   */
  private val intTerms = scala.collection.mutable.HashSet.empty[Term]

  private def noteInts(t: Term): Unit = t match
    case Term.Linear(terms, _) => terms.foreach((_, u) => noteInt(u))
    case Term.Num(_) => ()
    case _ => noteInt(t)

  /** Only a term its sort does not already say is one is kept: the set is then
   *  empty on a script that declares its constants, and its growth, which makes
   *  [[shareIntegers]] start over, is rare.
   */
  private var anyNoted = false
  private def noteInt(t: Term): Unit =
    anyNoted = true
    val sort = sortOf(t)
    if !Encoder.numeric(sort) then intTerms += t

  private def isInt(t: Term): Boolean = t match
    case Term.Num(_) | Term.Linear(_, _) => true
    case _ => Encoder.numeric(sortOf(t)) || intTerms(t)

  private def isFun(t: Term): Boolean = sortOf(t).arrow.isDefined

  /** Theory combination: an `Int` term gets an e-class only when it occurs
   *  under an uninterpreted function or a constructor, or is compared by `Eq`;
   *  such shared terms are leaves for the e-graph and variables for the LIA
   *  solver. For every pair of them that can meet — arguments of the same
   *  function at the same position, applications of the same function, the
   *  sides of an equality atom, a selector's applications and its field in
   *  constructor applications: the only equalities the e-graph uses or makes —
   *  this makes their equality atom (the one the e-graph propagates by
   *  congruence) an atom of the LIA theory too, the equality of their
   *  difference to 0: the SAT solver then decides an arrangement of the shared
   *  terms that both theories accept, which is a model of both (Nelson and
   *  Oppen; both theories are stably infinite).
   */
  private val sharedPairs = scala.collection.mutable.HashSet.empty[(Term, Term)]

  /** What [[shareIntegers]] has seen: a session asks check after check of a
   *  problem that grows (two per round of unfolding, on Stainless's), and
   *  meeting every term with every other at each is quadratic in the session.
   *  So the pass makes only the pairs with a term or an equality that arrived
   *  since the last one. It makes them in the order the terms arrived, not the
   *  one a hash table gives them: the atoms, their variables and their rows are
   *  numbered in it, and the search follows the numbers. A term newly known as
   *  an integer changes what the earlier ones share: the pass then starts over
   *  (the pairs already made are not made again).
   */
  private var sharedTerms = 0 // the terms of `terms` seen
  private var sharedEqualities = 0 // the equalities of `equalities` seen
  private var sharedNoted = 0 // the size of `intTerms` then

  def shareIntegers(): Unit = if anyInt || anyArray || anyNoted || anyStore() then
    val pairs = ArrayBuffer.empty[(Term, Term)] // the pairs this call is first to meet
    val arrayPairs = ArrayBuffer.empty[(Term, Term)] // function-sorted pairs: their equality atom, for extensionality
    val selectorPairs = ArrayBuffer.empty[(Term, Term)] // a selector's application and a field: paired last
    def pair(a: Term, b: Term): Unit =
      step()
      if a != b && isInt(a) && isInt(b) && sortOf(a).arrow.isEmpty && sortOf(b).arrow.isEmpty
        && !sharedPairs((b, a)) && sharedPairs.add((a, b))
      then pairs += ((a, b))
      else if a != b && sortOf(a).arrow.isDefined && sortOf(b).arrow.isDefined
        && !sharedPairs((b, a)) && sharedPairs.add((a, b))
      then arrayPairs += ((a, b))
    if sharedNoted != intTerms.size then
      sharedNoted = intTerms.size
      sharedTerms = 0
      sharedEqualities = 0
    val fresh = scala.collection.mutable.HashSet.empty[Term] // the terms that arrived since the last pass
    val freshFuns =
      scala.collection.mutable.LinkedHashSet.empty[Term] // and the functions of the applications among them
    while sharedTerms < terms.length do
      val t = terms(sharedTerms)
      fresh += t
      t match
        case a: Term.App => freshFuns += a.fun
        case _ => ()
      sharedTerms += 1
    // An application with an integer or an array, as its value or among its arguments, can share; the
    // others have nothing to. Two arrays under the same function meet here too, whatever the function
    // gives: equal by extensionality, their applications are equal by congruence (issue 39).
    def shares(a: Term.App): Boolean = isInt(a) || isFun(a) || a.args.exists(x => isInt(x) || isFun(x))
    if fresh.nonEmpty then
      for fun <- freshFuns do
        val group = applications(fun)
        val relevant = group.iterator.filter(shares).toArray
        val arrived = relevant.indices.filter(i => fresh(relevant(i))).toArray // increasing
        var from = 0 // the first of `arrived` after `i`
        for i <- relevant.indices do
          val a = relevant(i)
          while from < arrived.length && arrived(from) <= i do from += 1
          def meet(b: Term.App): Unit =
            pair(a, b)
            for (x, y) <- a.args.zip(b.args) do pair(x, y)
          if fresh(a) then
            var j = i + 1
            while j < relevant.length do
              meet(relevant(j))
              j += 1
          else
            var k = from
            while k < arrived.length do
              meet(relevant(arrived(k)))
              k += 1
      // A selector's applications meet the arguments of its constructor at its position (the selector
      // rule). An arithmetic field, integer or real: a real one shared only through the e-graph left
      // the simplex without its equalities (issue 18). And an array field: the e-graph equates the
      // selector's application with the array, but their reads are shared only once the two are a
      // pair (issue 134).
      for (selector, constructor, i) <- sharedFields if freshFuns(selector) || freshFuns(constructor) do
        val constructions = applications.getOrElse(constructor, noApplications)
        val arrived = constructions.filter(fresh)
        for s <- applications.getOrElse(selector, noApplications); k <- (if fresh(s) then constructions else arrived) do
          if k.args.length > i then selectorPairs += ((s, k.args(i)))
    // Applications of different function terms meet too when the functions themselves can be equated —
    // two arrays, or a store and the array it may equal: group by the function's sort instead of the
    // function.
    // Only functions the search may actually equate: the sides of a function equality (recorded or
    // shared), and store applications. Pairing every same-sorted application would be quadratic on
    // ordinary uninterpreted functions. With no function equality and no application of a store,
    // there is none, and nothing to look for.
    if functionEqualities.nonEmpty || anyArrayApplication then
      val equatableFuns = scala.collection.mutable.HashSet.empty[Term]
      for case Formula.Eq(f, g) <- functionEqualities do
        equatableFuns += f
        equatableFuns += g
      val byFunctionSort = terms.iterator.collect {
        case a: Term.App
            if sortOf(a.fun).arrow.isDefined
              && (equatableFuns(a.fun) ||
                (a.fun match
                  case Term.App(Term.Const(n), _) => Names.isArrayOperation(n)
                  case _ => false)) =>
          a
      }.toList.groupBy(a => (sortOf(a.fun), a.args.length))
      for (_, group) <- byFunctionSort do
        val relevant = group.filter(shares)
        for (a, i) <- relevant.zipWithIndex; b <- relevant.drop(i + 1) if a.fun != b.fun do
          pair(a, b)
          for (x, y) <- a.args.zip(b.args) do pair(x, y)
    // Not the equalities of the application lemmas: paired, they would be the problem's, each with
    // a witness, the map and the arrays read there, and the integers there shared in turn. One the
    // problem states later arrives again (see `lit`).
    while sharedEqualities < equalities.length do
      equalities(sharedEqualities) match
        case eq @ Formula.Eq(a, b) if !lemmaEqualities(eq) => pair(a, b)
        case _ => ()
      sharedEqualities += 1
    for (s, x) <- selectorPairs do pair(s, x)
    for (a, b) <- pairs do
      val e = lit(Formula.Eq(a, b))
      // The atom is the two bounds when true; when false, the disequality is a choice of the SAT solver
      // between the two sides, `a − b ≤ −1` or `a − b ≥ 1`, as a clause over bound atoms — not a
      // disequality the LIA solver decides by branching, without learning, at every value the
      // relaxation lands on (hundreds of them on `wisas`).
      def equalOrApart(x: lia.Var, c: BigInt): Unit =
        liaAtoms(e.variable) = LiaTheory.Atom.Equal(x, c)
        // Below `c` and above it. Over the integers that is `≤ c − 1` and `> c`, which leaves nothing
        // between; over the reals it has to be the strict bound `< c`, or the clause forbids the open
        // band `(c − 1, c)` and forces two shared terms less than one apart to be equal (issue 8).
        val below = if liaSolver.isInteger(x) then bound(x, c - 1, false) else bound(x, c, true)
        val above = bound(x, c, false)
        clauses += Array(e, below, above.neg)
        // Over the reals the two sides are bounds on the same constant, and `< c` implies `≤ c`: said
        // here, the search does not have to reach the theory to find that out.
        if !liaSolver.isInteger(x) then clauses += Array(below.neg, above)
        guidedAtoms += below.variable
        guidedAtoms += above.variable
        anySharedAtom = true
      Term.linear(List((1, a), (-1, b))) match
        case Term.Num(v) => clauses += Array(if v.signum == 0 then e else e.neg) // two numerals
        case Term.Linear(terms, c) => equalOrApart(slack(terms), -c)
        case difference => equalOrApart(intVar(difference), 0)
    // An equality atom per pair of function-sorted shared terms — two arrays under the same function can
    // meet, and the atom's extensionality witness (with the store lemmas at it) decides whether they do:
    // the entailed disjunction of the classic Stump-Barrett-Dill-Levitt example. The witness waits until a
    // `sat` keeps the two apart (see awaitingWitness).
    // An equality an application lemma made already stays the lemma's, without a witness: only the
    // problem stating it makes it one of its own (see `lit`).
    for (a, b) <- arrayPairs do
      val eq = Formula.Eq(a, b)
      if !lits.contains(eq) then
        lits(eq) = encode(eq)
        if functionEqualities.nonEmpty && functionEqualities.last == eq then
          awaitingWitness += eq
          awaitingVars += lits(eq).variable

  /** Applications of the arrays the search may equate with a store: for every
   *  application `a(i)` of an array-sorted term and every store term `s` of the
   *  same sort, the clause `a ≠ s ∨ a(i) = s(i)` — an array equated with a
   *  store is then read at the array's indices, where the read-over-write
   *  lemmas of [[arrayLemmas]] say what the store holds; repeated for the
   *  applications this makes, to a fixpoint (finite: so are the stores and the
   *  indices). The equality `a = s` of a lemma gets no extensionality witness
   *  (see [[assertExtensionality]]): a witness would make an application, the
   *  application a lemma, the lemma an equality, without end.
   */
  private val applicationsDone = scala.collection.mutable.HashSet.empty[(Term.App, Term)]
  private val equatedApplications = ArrayBuffer.empty[(Term, Term)]

  def applicationLemmas(): Unit = if anyStore() then
    val done = applicationsDone // across solves: the encoder persists, a lemma is emitted once
    val equated = equatedApplications
    var more = true
    while more do
      more = false
      val stores = arrayOperations.toList
      val apps = if stores.isEmpty then Nil else terms.iterator.collect { case a: Term.App => a }.toList
      for s <- stores; a <- apps do
        step()
        if applicable(a, s) && done.add((a, s)) then
          more = true
          val applied = Term.App(s, a.args)
          equated += ((a, applied))
          recordFunctionEqualities = false
          clauses += Array(lit(Formula.Eq(a.fun, s)).neg, lit(Formula.Eq(a, applied)))
          recordFunctionEqualities = true
    // An application equated with an integer term is one, and conversely (for the sharing).
    var changed = true
    while changed do
      changed = false
      for (a, b) <- equated if isInt(a) != isInt(b) do
        noteInts(a)
        noteInts(b)
        changed = true

  /** Whether `a` reads an array of the store's sort — the same sort, not an
   *  inner array of it — at one index.
   */
  private def applicable(a: Term.App, s: Term): Boolean =
    a != s && a.fun != s && a.args.length == 1 && !declaredFunction(a.fun) && sortOf(a.fun) == sortOf(s)

  /** Whether a term is a declared function symbol: of an array's sort when it
   *  takes one argument, and no array — nothing equates it with one, and its
   *  argument is no index. An auxiliary of a map's operator is one, applied to
   *  the elements of the arrays: taken for an array, the element would be an
   *  index, the map read there, and its element there another, without end.
   */
  private def declaredFunction(f: Term): Boolean = f match
    case Term.Const(name) => declarations.get(name).exists(_._1.nonEmpty)
    case _ => false

  /** Extensionality: for every equality atom between function-sorted terms, the
   *  lemma `f = g ∨ f(c) ≠ g(c)` with fresh constants `c` (the witnesses of the
   *  difference), repeated while the new equality is between functions (a
   *  curried result). So `unsat` and `sat` follow the usual semantics of
   *  functions on the equalities of the assertions.
   */
  private val extensionalityDone = scala.collection.mutable.HashSet.empty[Formula]

  /** The function equalities of the encoded formulas: the ones that may need a
   *  witness — never the ones the application lemmas make.
   */
  private val functionEqualities = ArrayBuffer.empty[Formula]
  private var recordFunctionEqualities = true

  /** The function equalities [[shareIntegers]] made between two arrays that can
   *  meet, whose witness waits until a search keeps the two apart: the e-graph
   *  merges the arrays the search equates, and a pair it equates needs none.
   *  Given one up front, each pair's witness was an index every array of its
   *  sort was read at, a map among them, whose elements there made new pairs,
   *  and new witnesses, without end. Once the search answers `sat` with two of
   *  them apart, they get their witness, and the search goes on (see
   *  [[witnessApart]]).
   */
  private val awaitingWitness = scala.collection.mutable.LinkedHashSet.empty[Formula]
  private val keptApart = ArrayBuffer.empty[Formula] // the ones the last `sat` kept apart
  private val awaitingVars = HashSet.empty[cdclt.Var] // the variables of their atoms

  /** Whether the last `sat` kept shared arrays apart that had no witness: they
   *  have one now, for the passes and the search to go on with.
   */
  def witnessApart(): Boolean =
    val made = keptApart.nonEmpty
    for eq <- keptApart do
      awaitingWitness -= eq
      awaitingVars -= lits(eq).variable
    keptApart.clear()
    made

  /** The shared arrays the model of a `sat` keeps apart with no witness of a
   *  difference: one pair per two classes of the e-graph, whose other members
   *  differ where those two do, by congruence. Two classes already told apart
   *  by a witness need no other.
   */
  private def wantWitnesses(model: Array[Boolean]): Unit =
    def apart(eq: Formula): Boolean =
      val l = lits(eq)
      model(l.variable) != l.positive
    def classesOf(eq: Formula): (EClassId, EClassId) = eq match
      case Formula.Eq(a, b) =>
        val (x, y) = (eg.find(classOf(a)), eg.find(classOf(b)))
        if x <= y then (x, y) else (y, x)
      case _ => throw IllegalStateException(s"not an equality: $eq")
    val toldApart = scala.collection.mutable.HashSet.empty[(EClassId, EClassId)]
    for eq <- functionEqualities do
      if extensionalityDone(eq) && !awaitingWitness(eq) && lits.contains(eq) && apart(eq) then
        toldApart += classesOf(eq)
    for eq <- awaitingWitness do
      if apart(eq) && toldApart.add(classesOf(eq)) then keptApart += eq

  def functionEqualityCount: Int = functionEqualities.length

  /** A witness index's name, `.witness!N` ([[Names]]): no script symbol is one,
   *  nor any of the lowering's.
   */
  private var witnesses = 0
  private def witnessName(): String =
    witnesses += 1
    Names.witness(witnesses - 1)

  def introducedName(name: String): Boolean = introduced.contains(name)

  def assertExtensionality(): Unit = if anyFunctionEquality then
    val done = extensionalityDone // across solves: one witness pair per equality, ever
    var more = true
    while more do
      more = false
      for case eq @ Formula.Eq(f, g) <- functionEqualities.toList if !done(eq) && !awaitingWitness(eq) do
        done += eq
        if !assertedEqualities(eq) then
          sortOf(f).arrow.orElse(sortOf(g).arrow) match
            case Some((params, _)) =>
              more = true
              // A witness is a constant of the index sort like any other: of a range of the integers, it
              // gets the range with its class, or two arrays over `(_ BitVec 1)` agreeing at both
              // indices could still differ at it (issue 20).
              val witnesses = params.map { sort =>
                val name = witnessName()
                introduced(name) = sort
                Term.Const(name)
              }
              clauses += Array(lit(eq), lit(Formula.Eq(applyAll(f, witnesses), applyAll(g, witnesses))).neg)
            case _ => ()

  /** What a term's sort says of it, asserted once for every term the encoder
   *  knows, whoever made the term: an assertion of the script, a pass of the
   *  encoder, a witness of extensionality. A term of a datatype sort has one of
   *  its testers hold. A term of a range of the integers ([[Sort.IntRange]], a
   *  bit-vector sort of the script) lies in the range, `0 ≤ t < 2^n`.
   *
   *  The sort says it, so no assertion of the script has to, and no level of
   *  the script can take it back: the lowering once asserted the range of the
   *  terms it met, which left out the ones made here (issues 126 and 154) and
   *  went with the level of the assertion (issue 145).
   */
  private val sortsAsserted = scala.collection.mutable.HashSet.empty[Term]
  private var sortsTerms = 0 // the terms of `terms` the pass has looked at
  private var sortsRanged = 0 // and those of `unranged`

  def assertSorts(): Unit =
    val seen = sortsAsserted // across solves: one tester disjunction, one range per term
    if datatypes.nonEmpty then
      // Only the terms that arrived since the last pass, the others are seen, and in the order they
      // arrived: the order of the tester disjunctions numbers the atoms, and the search depends on it.
      val todo = ArrayBuffer.empty[Term]
      while sortsTerms < terms.length do
        val t = terms(sortsTerms)
        if datatypeOf(sortOf(t)).isDefined && !seen(t) then todo += t
        sortsTerms += 1
      while todo.nonEmpty do
        val t = todo.remove(todo.length - 1)
        if seen.add(t) then
          val datatype = datatypeOf(sortOf(t)).get
          assert(
            Formula.Or(datatype.constructors.map(c => Formula.Pred(Term.App(Term.Const(c.tester), List(t))))),
            null
          )
    assertRanges()

  /** The ranges of the terms of an integer range that arrived and have none
   *  yet: of the applications of an assertion as [[meet]] finds them, and of
   *  the terms the passes make at the next [[assertSorts]]. Not of a declared
   *  constant, whose range the solver states at its declaration.
   */
  private def assertRanges(): Unit =
    while sortsRanged < unranged.length do
      val t = unranged(sortsRanged)
      sortsRanged += 1
      if sortsAsserted.add(t) then
        sortOf(t) match
          case Sort.IntRange(lower, upper) =>
            assert(Formula.And(List(Formula.Le(Term.Num(lower), t), Formula.Le(t, Term.Num(upper)))), null)
          case _ => ()

  private val anyFiniteField =
    datatypes.exists(_.constructors.exists(_.selectors.exists((_, s) =>
      cardinality(s) != Encoder.Cardinality.Infinite
    )))

  /** The fields of a finite sort that the model of a `sat` needs as terms and
   *  that the encoder does not have: found by [[wantFields]] while the engines
   *  hold the model, made by [[boundFields]] once they are back at level 0.
   */
  private val wantedFields = ArrayBuffer.empty[(Term, Sort)]

  /** Whether [[boundFields]] has fields to make. */
  def fieldsWanted: Boolean = wantedFields.nonEmpty

  /** Finds the fields the model at hand needs (see [[boundFields]]). A class of
   *  a datatype sort needs those of the constructor whose tester holds of it,
   *  for one of its terms. It needs none when one of its terms is that
   *  constructor's application, whose arguments are the fields, or already has
   *  them all.
   */
  private def wantFields(): Unit =
    wantedFields.clear()
    if anyFiniteField then
      val truth = eg.find(trueTerm)
      val settled = HashSet.empty[EClassId] // the classes that need nothing
      val wanting = scala.collection.mutable.LinkedHashMap.empty[EClassId, List[(Term, Sort)]]
      for t <- terms; datatype <- datatypeOf(sortOf(t)) do
        val root = eg.find(classes(t))
        if !settled(root) then
          val held = datatype.constructors.find(c =>
            classes.get(Term.App(Term.Const(c.tester), List(t))).exists(eg.find(_) == truth)
          )
          for c <- held do
            val built = t match
              case Term.App(Term.Const(name), _) => name == c.name
              case _ => false
            val missing =
              if built then Nil
              else
                for
                  (selector, sort) <- c.selectors
                  if cardinality(sort) != Encoder.Cardinality.Infinite
                  field = Term.App(Term.Const(selector), List(t))
                  // A Boolean field is known once it is one of the Booleans the search decides.
                  if !classes.get(field).exists(cls => sort != Sort.Bool || booleanClasses(cls))
                yield (field, sort)
            if missing.isEmpty then
              settled += root
              wanting -= root
            else if !wanting.contains(root) then wanting(root) = missing
      for fields <- wanting.values do wantedFields ++= fields

  /** Makes the fields of a finite sort that the model of the last `sat` needs
   *  terms of the encoder, and tells whether there were any. As terms, they get
   *  what their sorts say ([[assertSorts]]) and meet one another
   *  ([[shareIntegers]]), so their values are among their sorts': a tester that
   *  holds expands its term into the constructor over the term's fields,
   *  whatever the term's own sort, and nothing else bounds them. Two terms
   *  built by one constructor over a field of sort `Unit` stayed apart, against
   *  the one value of `Unit` (issue 125), and three over a field of one bit
   *  (issue 126).
   *
   *  The fields only take models away, so they are made after a `sat`, which is
   *  then searched again with them, and an `unsat` found without them stands.
   *  And only the ones the model needs: made from the start for every term and
   *  every constructor of its sort, they cost a bounded model checking file of
   *  the corpus fifteen times its steps, with a choice among thirteen blocks
   *  for the top of every tower it names
   *  (`blocksworld__from_0_9_4_to_3_3_7_bmc_5`).
   */
  def boundFields(): Boolean =
    val made = wantedFields.nonEmpty
    for (field, sort) <- wantedFields do if sort == Sort.Bool then boolean(field) else classOf(field)
    wantedFields.clear()
    made

  private val liaSolver = lia.Solver()
  private val intVars = HashMap.empty[Term, lia.Var] // `Int`-sorted constants and applications
  private val slacks = HashMap.empty[List[(BigInt, Term)], lia.Var] // linear combinations of them
  // The LIA variables of the auxiliary constants and of the combinations of those alone, and the atoms
  // bounding them: the ones the search decides last (see Solver.declare).
  private val auxiliaryVars = HashSet.empty[lia.Var]
  private val deferred = ArrayBuffer.empty[cdclt.Var]
  private var deferredCursor = 0

  private val clauses = ArrayBuffer.empty[Array[Lit]]
  private val atoms = ArrayBuffer.empty[(EClassId, EClassId) | Null] // per variable, its UF atom `t = u`
  private val liaAtoms = ArrayBuffer.empty[LiaTheory.Atom | Null] // per variable, its LIA atom, if any
  private val guidedAtoms = HashSet.empty[cdclt.Var] // the sides of the disequality clauses (see LiaTheory.phase)
  private val lits = HashMap.empty[Formula, Lit]
  private val trueLit = freshVar() // a variable asserted true, for `True`
  clauses += Array(trueLit)
  eg.disequate(trueTerm, falseTerm, trueLit.index)

  private def freshVar(): Lit =
    atoms += null
    liaAtoms += null
    Lit(atoms.length - 1)

  /** The Boolean-sorted terms that are arguments of applications or sides of an
   *  equality (see [[decideBooleans]]), and their classes.
   */
  private val booleans = ArrayBuffer.empty[Term]
  private val booleanClasses = scala.collection.mutable.HashSet.empty[EClassId]

  private def boolean(term: Term): Unit =
    if sortOf(term) == Sort.Bool && booleanClasses.add(classOf(term)) then booleans += term

  /** Whether some term is an integer, some application takes or gives an array
   *  (two arrays under the same function are a pair to share, with or without
   *  an integer or a `store` around: issue 133), or some equality is between
   *  functions (arrays): the passes over all the terms of [[shareIntegers]] and
   *  [[assertExtensionality]] are skipped otherwise (many queries are small).
   */
  private var anyInt = false
  private var anyArray = false
  private var anyFunctionEquality = false

  def classOf(term: Term): EClassId = classes.getOrElseUpdate(
    term, {
      sortOf(term) match
        case Sort.Int | Sort.Real => anyInt = true
        case Sort.IntRange(_, _) =>
          anyInt = true
          term match
            case Term.Const(name) if !introduced.contains(name) => () // declared: the solver states its range
            case _ => unranged += term
        case _ => ()
      term match
        case Term.App(Term.App(Term.Const(n), _), _) if Names.isArrayOperation(n) => anyArrayApplication = true
        case _ => ()
      terms += term
      term match
        case a: Term.App =>
          applications.getOrElseUpdate(a.fun, ArrayBuffer.empty) += a
          a match
            case Term.App(Term.Const(name), List(_, _, _)) if Names.isStore(name) =>
              storeTerms += a
              arrayOperations += a
            case Term.App(Term.Const(name), List(_)) if Names.isConstArray(name) =>
              constTerms += a
              arrayOperations += a
            case Term.App(Term.Const(name), _) if Names.isMap(name) =>
              mapTerms += a
              arrayOperations += a
            case _ => ()
        case _ => ()
      classOfNew(term)
    }
  )

  private def classOfNew(term: Term): EClassId =
    term match
      case Term.Const(_) => eg.newClass()
      case Term.App(fun, args) =>
        args.foreach(boolean)
        // Looked at until the first one: once set, the flag stays.
        if !anyArray && (isFun(term) || args.exists(isFun)) then anyArray = true
        eg.add(App(classOf(fun), ArraySeq.from(args.map(classOf))))
      case Term.Num(_) => eg.newClass() // a leaf for the e-graph, a variable for LIA (shared)
      case Term.Linear(terms, _) =>
        // Its terms get their variables of the simplex, and an application among them its class, here: a
        // selector application that occurs only in `(cons (+ 1 (car x)) nil)` had neither, the e-graph
        // never met it, and `x = (cons (+ 1 (car x)) nil)` was sat (issue 136). Nor did the model value it.
        terms.foreach((_, u) => intVar(u))
        eg.newClass()
      case Term.Bool(_) => eg.newClass() // a leaf, tied to its formula by `Pred` (see `encode`)

  /** A Boolean-sorted term that is an argument or a side of an equality is true
   *  or false: its atom `t = true` is decided by the SAT solver, and the UF
   *  theory merges `t` with `true` or with `false` accordingly — so that two
   *  Boolean arguments with the same truth value are equal (congruence), and a
   *  Boolean term's class has a truth value. The atom of a [[Term.Bool]] holds
   *  iff its formula does. A predicate application only used as an atom needs
   *  neither: its disequality with `true` is enough.
   */
  /** The array axioms, as lemmas over the finite product of the `.store!`
   *  applications and the index terms of their array sort (`store` symbols come
   *  from the parser, one per array sort): for `s = store(a, i, v)`, the write
   *  is read back — `select(s, i) = v` — and for every index `j` of the sort,
   *  `i = j ∨ select(s, j) = select(a, j)`. Selection is application, so
   *  congruence and extensionality (the witnesses join the index set) come from
   *  the function machinery; each lemma is emitted once, ever. An array of
   *  arrays is a function of several arguments (its sort flattened), its inner
   *  arrays functions of one: a store at either level gets the lemmas of its
   *  level, and the passes run to a fixpoint (see [[Solver.solve]]).
   */
  /** Applies an array to an index: a store application is a whole array, so it
   *  is applied as one, never flattened into the store symbol's arguments.
   */
  private def applyAll(f: Term, args: List[Term]): Term = args.foldLeft(f)(selectTerm)

  def clauseCount: Int = clauses.length

  def litOf(f: Formula): Option[Lit] = lits.get(f)

  private def selectTerm(array: Term, index: Term): Term = array match
    case Term.App(Term.Const(n), _) if Names.isStore(n) => Term.App(array, List(index))
    case _ => Term.App(array, List(index))

  /** An index of `sort` no store writes at, for the sorts indexing a constant
   *  array: reading there carries the value of a constant array through the
   *  stores over it, so that `((as const A) 0)` with finitely many writes is
   *  not `((as const A) 1)`. There is one while the sort has more values than
   *  the stores' indices; a finite sort they may fill is listed instead (see
   *  [[settling]]): a bit-vector's values the solver knows, another's the
   *  lowering counts and lists ([[Command.DeclareFinite]]).
   */
  private val beyondIndices = scala.collection.mutable.HashMap.empty[Sort, Term]
  private val beyondDone = scala.collection.mutable.HashSet.empty[(Term, Term)]

  /** How many store indices the index beyond the writes of each sort is apart
   *  from, and the bit-vector sorts whose stores were too many for it, now read
   *  at their every value.
   */
  private val beyondApart = scala.collection.mutable.HashMap.empty[Sort, Int]
  private val listedSorts = scala.collection.mutable.HashSet.empty[Sort]

  private def beyond(sort: Sort): Term = beyondIndices.getOrElseUpdate(
    sort, {
      val name = Names.beyond(beyondIndices.size)
      sort match
        case Sort.IntRange(_, _) => () // its range comes with its class (see assertSorts)
        case _ if cardinality(sort) != Encoder.Cardinality.Infinite && !finiteSorts.contains(sort) =>
          throw io.bovel.smtlib.Smt2Error(s"a constant array or a map over the finite sort $sort")
        case _ => ()
      introduced(name) = sort
      Term.Const(name)
    }
  )

  /** The indices that settle a constant array or a map of index sort `sort`
   *  away from the indices read: the index beyond the writes, and every value
   *  of the sort as well once the stores' indices may fill it (see
   *  [[arrayLemmas]]: four writes fill a `(_ BitVec 2)`, and no index is left
   *  beyond them). `Bool`'s two values are listed from the start.
   */
  private def settling(sort: Sort): List[Term] = sort match
    case Sort.Bool => List(Term.boolean(Formula.True), Term.boolean(Formula.False))
    case Sort.IntRange(lower, upper) if listedSorts(sort) => beyond(sort) :: (lower to upper).toList.map(Term.Num(_))
    case _ if listedSorts(sort) => beyond(sort) :: listing(sort)
    case _ => List(beyond(sort))

  /** The values of a finite index sort the lowering counted, built once it is
   *  listed: as many as the writes that filled it, and one more.
   */
  private val listings = scala.collection.mutable.HashMap.empty[Sort, List[Term]]

  private def listing(sort: Sort): List[Term] = listings.getOrElseUpdate(
    sort, {
      val (size, value) = finiteSorts(sort)
      List.tabulate(size.toInt)(k => value(BigInt(k)))
    }
  )

  private val arrayWritesDone = scala.collection.mutable.HashSet.empty[Term]
  private val exhausted = scala.collection.mutable.HashSet.empty[(Sort, Term)]
  private val arrayReadsDone = scala.collection.mutable.HashSet.empty[(Term, Term)]

  /** The literal of the equality of two elements in an array lemma: what a
   *  store, a constant array or a map holds at an index, an array itself for
   *  arrays of arrays. Its equality between arrays gets no witness, as an
   *  application lemma's (see [[lemmaEqualities]]): the lemma only ever needs
   *  it to hold, and a witness would be an index every array of its sort is
   *  read at, whose elements there are equalities of the lemmas in turn,
   *  without end. One the problem states gets its witness (see `lit`).
   */
  private def lemma(formula: Formula): Lit =
    recordFunctionEqualities = false
    try lit(formula)
    finally recordFunctionEqualities = true

  def arrayLemmas(): Unit = if anyStore() then
    val stores = storeTerms.toList
    val indices = scala.collection.mutable.HashMap.empty[Sort, scala.collection.mutable.LinkedHashSet[Term]]
    def index(sort: Sort, j: Term): Unit =
      indices.getOrElseUpdate(sort, scala.collection.mutable.LinkedHashSet.empty) += j
    for a <- terms do
      a match
        case Term.App(f, List(_)) if declaredFunction(f) => ()
        case Term.App(f, List(j)) if sortOf(f).arrow.isDefined => index(sortOf(f), j)
        case _ => ()
    for s <- stores do index(sortOf(s), s.args(1))
    // Two numbers are equal by two bounds; two indices of a range of the integers by an equality atom, as
    // they were while the index sort alone told a bit-vector from an integer.
    def equalAt(sort: Sort, l: Term, r: Term): Formula =
      if Encoder.numeric(sort) then Formula.IntEq(l, r) else Formula.Eq(l, r)
    def equalIndex(sort: Sort, l: Term, r: Term): Formula =
      if sort.isInstanceOf[Sort.IntRange] then Formula.Eq(l, r) else equalAt(sort, l, r)
    // The index beyond the writes (see [[beyond]]) is none of the written ones, while a value is left
    // for it: a bit-vector sort of `2^n` values takes `2^n - 1` indices apart from it, and its arrays
    // are read at every value from then on (see [[settling]]). Fewer indices than values is all it
    // needs, whatever the indices are: two of them may be equal, and the sort then has even more room.
    for s <- stores do
      val indexSort = sortOf(s).arrow.get._1.head
      for w <- beyondIndices.get(indexSort) do
        if beyondDone.add((w, s.args(1))) then
          val room = indexSort match
            case Sort.IntRange(lower, upper) => upper - lower
            case _ => finiteSorts.get(indexSort).fold(BigInt(-1))(_._1 - 1) // -1: an infinite sort
          val apart = beyondApart.getOrElse(indexSort, 0)
          if room >= 0 && apart >= room then listedSorts += indexSort
          else
            beyondApart(indexSort) = apart + 1
            clauses += Array(lit(equalIndex(indexSort, w, s.args(1))).neg)
    // A constant array holds its value at every index of its sort: `const(d)(j) = d`.
    for case c @ Term.App(_, List(d)) <- constTerms.toList do
      val sort = sortOf(c)
      val elementSort = applied(sort, 1)
      settling(sort.arrow.get._1.head).foreach(index(sort, _))
      for j <- indices.getOrElse(sort, Nil).toList do
        step()
        if arrayReadsDone.add((c, j)) then clauses += Array(lemma(equalAt(elementSort, selectTerm(c, j), d)))
    // A map holds, at every index of its sort and of its arrays', what its operator makes of what
    // the arrays hold there: its template at their elements, each auxiliary of the template a
    // function of them, defined there (see [[Pointwise]]). The index beyond the writes is one of
    // them: it settles the map away from the indices read, as for a constant array.
    for case m @ Term.App(Term.Const(name), arrays) <- mapTerms.toList do
      val pointwise = maps.getOrElse(name, throw io.bovel.smtlib.Smt2Error(s"$name: a map with no operator"))
      val sort = sortOf(m)
      val elementSort = applied(sort, 1)
      settling(sort.arrow.get._1.head).foreach(index(sort, _))
      for j <- (sort :: arrays.map(sortOf)).distinct.flatMap(indices.getOrElse(_, Nil)).distinct do
        step()
        if arrayReadsDone.add((m, j)) then
          val (definitions, value) = pointwise.at(arrays.map(selectTerm(_, j)), (c, elements) => Term.App(c, elements))
          for d <- definitions do clauses += Array(lit(d))
          clauses += Array(
            lemma(
              if elementSort == Sort.Bool then Formula.Iff(Formula.Pred(selectTerm(m, j)), Formula.pred(value))
              else equalAt(elementSort, selectTerm(m, j), value)
            )
          )
    // An index read of a listed sort other than the ranges of the integers is one of its values, as the
    // arithmetic says of a range's: the reads at them all then settle what an array holds there.
    for (sort, js) <- indices.toList do
      val indexSort = sort.arrow.get._1.head
      if listedSorts(indexSort) then
        val listed = if finiteSorts.contains(indexSort) then listing(indexSort) else Nil
        for j <- js.toList if listed.nonEmpty do
          if !listed.contains(j) && exhausted.add((indexSort, j)) then
            clauses += listed.map(v => lit(equalIndex(indexSort, j, v))).toArray
    for case s @ Term.App(_, List(a, i, v)) <- stores do
      val sort = sortOf(s)
      val indexSort = sort.arrow.get._1.head
      val elementSort = applied(sort, 1) // an array, for an array of arrays
      if arrayWritesDone.add(s) then clauses += Array(lemma(equalAt(elementSort, selectTerm(s, i), v)))
      for j <- indices.getOrElse(sort, Nil) do
        step()
        if j != i && arrayReadsDone.add((s, j)) then
          clauses += Array(
            lit(equalIndex(indexSort, i, j)),
            lemma(equalAt(elementSort, selectTerm(s, j), selectTerm(a, j)))
          )

  def booleanCount: Int = booleans.length

  private var booleansDecided = 0

  def decideBooleans(): Unit =
    while booleansDecided < booleans.length do
      lit(Formula.Pred(booleans(booleansDecided)))
      booleansDecided += 1

  private def atom(t: EClassId, u: EClassId): Lit =
    atoms += ((t, u))
    liaAtoms += null
    Lit(atoms.length - 1)

  private def bound(x: lia.Var, c: BigInt, strict: Boolean): Lit =
    atoms += null
    liaAtoms += LiaTheory.Atom.Bound(x, c, strict)
    if auxiliaryVars(x) then deferred += atoms.length - 1
    Lit(atoms.length - 1)

  /** `lhs − rhs ≤ 0` (`< 0` when strict), as a bound on the combination
   *  `Σ a × t` (`+ c`) or on a lone term.
   */
  private def comparison(lhs: Term, rhs: Term, strict: Boolean): Lit =
    noteInts(lhs)
    noteInts(rhs)
    Term.linear(List((1, lhs), (-1, rhs))) match
      case Term.Num(v) => if if strict then v.signum < 0 else v.signum <= 0 then trueLit else trueLit.neg
      case Term.Linear(terms, c) => bound(slack(terms), -c, strict)
      case term => bound(intVar(term), 0, strict)

  /** The LIA variable of an atomic `Int` term. An application is a node of the
   *  e-graph as well, so that congruence relates it to other applications (a
   *  shared term, see [[shareIntegers]]).
   */
  private def intVar(term: Term): lia.Var =
    term match
      case Term.App(_, _) => classOf(term)
      case _ => ()
    intVars.getOrElseUpdate(
      term, {
        val x = liaSolver.newVar(integer = sortOf(term) != Sort.Real)
        term match
          case Term.Const(name) if auxiliaries(name) => auxiliaryVars += x
          case _ => ()
        x
      }
    )

  /** The LIA variable standing for a linear combination of `Int` terms. */
  private def slack(terms: List[(BigInt, Term)]): lia.Var =
    slacks.getOrElseUpdate(
      terms, {
        val vars = terms.map((a, t) => (a, intVar(t)))
        val x = liaSolver.newSlack(vars, integer = !terms.exists((_, t) => sortOf(t) == Sort.Real))
        if vars.forall((_, y) => auxiliaryVars(y)) then auxiliaryVars += x
        x
      }
    )

  /** The literal standing for `formula`, defining it by clauses if needed. */
  private def lit(formula: Formula): Lit =
    // An equality first encoded for an application lemma, met again in a formula of the problem,
    // is one of the problem's from then on: its negation needs a witness like any other, and it
    // arrives again for `shareIntegers`, which left it aside as the lemma's.
    if recordFunctionEqualities && lemmaEqualities.nonEmpty && lemmaEqualities.remove(formula) then
      functionEqualities += formula
      equalities += formula
    // One the sharing made, met in a formula of the problem: its witness waits no more.
    if recordFunctionEqualities && awaitingWitness.nonEmpty && awaitingWitness.remove(formula) then
      awaitingVars -= lits(formula).variable
    lits.getOrElseUpdate(formula, encode(formula))

  /** The function equalities encoded for the application lemmas alone, which
   *  get no witness (see [[applicationLemmas]]) until the problem states them.
   */
  private val lemmaEqualities = scala.collection.mutable.HashSet.empty[Formula]

  private def encode(formula: Formula): Lit =
    import Formula.*
    step()
    formula match
      case True => trueLit
      case False => trueLit.neg
      case Not(arg) => lit(arg).neg
      case Eq(lhs, rhs) =>
        if lhs == rhs then trueLit
        else
          boolean(lhs)
          boolean(rhs)
          equalities += formula
          if sortOf(lhs).arrow.isDefined || sortOf(rhs).arrow.isDefined then
            anyFunctionEquality = true
            if recordFunctionEqualities then functionEqualities += formula else lemmaEqualities += formula
          atom(classOf(lhs), classOf(rhs))
      case Pred(term) =>
        // Two-valued from its first literal on: the theory merges a false term with `false` only for
        // terms it knows as Boolean, and a term known only from a later solve keeps the assignment
        // of an earlier one, which is never asserted again (issue 14).
        boolean(term)
        val e = atom(classOf(term), trueTerm)
        term match
          case Term.Bool(inner) => // `t = true` iff the formula holds
            val l = lit(inner)
            clauses += Array(e.neg, l)
            clauses += Array(l.neg, e)
          case _ => ()
        e
      case Le(lhs, rhs) => comparison(lhs, rhs, strict = false)
      case Less(lhs, rhs) => comparison(lhs, rhs, strict = true)
      case Implies(lhs, rhs) => lit(Or(List(Not(lhs), rhs)))
      case And(args) =>
        val v = freshVar()
        val as = args.map(lit)
        for a <- as do clauses += Array(v.neg, a)
        clauses += (v +: as.map(_.neg)).toArray
        v
      case Or(args) =>
        val v = freshVar()
        val as = args.map(lit)
        for a <- as do clauses += Array(v, a.neg)
        clauses += (v.neg +: as).toArray
        v
      case Iff(lhs, rhs) =>
        val v = freshVar()
        val (a, b) = (lit(lhs), lit(rhs))
        clauses += Array(v.neg, a.neg, b)
        clauses += Array(v.neg, a, b.neg)
        clauses += Array(v, a, b)
        clauses += Array(v, a.neg, b.neg)
        v
      case Ite(cond, thn, els) =>
        val v = freshVar()
        val (c, t, e) = (lit(cond), lit(thn), lit(els))
        clauses += Array(v.neg, c.neg, t)
        clauses += Array(v.neg, c, e)
        clauses += Array(v, c.neg, t.neg)
        clauses += Array(v, c, e.neg)
        v

  /** The assertions that are equality atoms: facts, which need no witness of
   *  extensionality.
   */
  private val assertedEqualities = scala.collection.mutable.HashSet.empty[Formula]

  /** Asserts `formula`, guarded by the selector literal `under` when it is not
   *  null: the clause holds only while the selector does — a script level's
   *  assertion (see [[Solver.push]]).
   */
  def assert(formula: Formula, under: Lit | Null): Unit =
    formula match
      // An equality asserted for good needs no witness; one under a level's selector is gone with
      // the level, and its negation then needs one like any other (issue 19).
      case Formula.Eq(_, _) if under == null => assertedEqualities += formula
      case _ => ()
    meet(formula)
    val l = lit(formula)
    clauses += (if under == null then Array(l) else Array(under.nn.neg, l))

  /** Meets the applications of an integer range in a formula, innermost first,
   *  before the formula is encoded: each gets its class, its variable and the
   *  two rows of its range together, ahead of the rows of the formula that use
   *  it. The encoder would find them while encoding the formula all the same,
   *  and range them then; but the search follows the order in which things are
   *  numbered, and this is the order the lowering stated the ranges in, before
   *  the assertion. Met in the middle of it, the ranges took a session of the
   *  corpus from 90 ms to no answer in a minute (`invalid-BinarySearch2__33`).
   */
  private val met = scala.collection.mutable.HashSet.empty[Term]

  private def meet(formula: Formula): Unit = formula match
    case Formula.True | Formula.False => ()
    case Formula.Not(arg) => meet(arg)
    case Formula.And(args) => args.foreach(meet)
    case Formula.Or(args) => args.foreach(meet)
    case Formula.Implies(lhs, rhs) =>
      meet(lhs)
      meet(rhs)
    case Formula.Iff(lhs, rhs) =>
      meet(lhs)
      meet(rhs)
    case Formula.Ite(cond, thn, els) =>
      meet(cond)
      meet(thn)
      meet(els)
    case Formula.Eq(lhs, rhs) =>
      meet(lhs)
      meet(rhs)
    case Formula.Pred(term) => meet(term)
    case Formula.Le(lhs, rhs) =>
      meet(lhs)
      meet(rhs)
    case Formula.Less(lhs, rhs) =>
      meet(lhs)
      meet(rhs)

  private def meet(term: Term): Unit =
    if met.add(term) then // a subterm shared by many terms is walked once
      term match
        case Term.App(fun, args) =>
          meet(fun)
          args.foreach(meet)
          if sortOf(term).isInstanceOf[Sort.IntRange] then
            classOf(term)
            assertRanges()
        case Term.Linear(terms, _) => terms.foreach((_, t) => meet(t))
        case Term.Bool(formula) => meet(formula)
        case Term.Const(_) | Term.Num(_) => ()

  /** A fresh selector literal for a script level. */
  def newSelector(): Lit = freshVar()

  /** The activation literal of a named assertion: the formula holds while the
   *  literal does, and the literal is assumed at every solve, so an `Unsat`
   *  core can name it (see [[core]]).
   */
  private val activations = HashMap.empty[Formula, Lit]

  def activate(formula: Formula): Lit =
    activations.getOrElseUpdate(
      formula, {
        meet(formula)
        val a = freshVar()
        clauses += Array(a.neg, lit(formula))
        a
      }
    )

  /** The failed assumptions of the last `Unsat`, for [[Solver.unsatCore]]. */
  def core(): Array[Lit] = sat.unsatCore

  /** Retires a popped level's selector: false for good, its clauses inert. */
  def retire(selector: Lit): Unit = clauses += Array(selector.neg)

  /** The theories and the SAT solver, alive across [[solve]]s: everything
   *  learned stays. Both theories are always attached — their atom buffers grow
   *  as terms arrive, possibly only after the first solve.
   */
  /** Whether some variable is an atom of both theories (a shared equality):
   *  only then does the combination need to remember impliers.
   */
  private var anySharedAtom = false

  // A decision on the equality of two shared arrays merges them first: the search keeps them apart only
  // where it must, and only those get a witness (see awaitingWitness).
  private val ufTheory = UfTheory(eg, atoms, trueTerm, falseTerm, booleanClasses, v => awaitingVars(v))
  private val theories = List(ufTheory, LiaTheory(liaSolver, liaAtoms, guidedAtoms, bound(_, _, strict = false)))

  /** Adds the work of the encoding and of the engines to `counts`, in the order
   *  of `Solver.kinds`; the steps of the search and the arithmetic are the
   *  solver's to count.
   */
  def addCounts(counts: Array[Long]): Unit =
    counts(1) += sat.numDecisions
    counts(2) += sat.numConflicts
    counts(3) += sat.numPropagations
    counts(4) += sat.numClauseVisits
    counts(5) += steps
    counts(6) += eg.mergeWork
    counts(7) += eg.explainWork
    counts(8) += eg.diseqWork
    counts(9) += ufTheory.atomScans
    counts(10) += liaSolver.reasonWork
    counts(11) += liaSolver.rowWork
  private val sat = cdclt.Solver(
    0,
    Theories(
      theories,
      v => if atoms(v) != null then theories.head else theories.last,
      v => atoms(v) != null && liaAtoms(v) != null, // only a shared equality needs its implier remembered
      () => anySharedAtom
    )
  )
  private var clauseCursor = 0

  /** The model of the last `Sat`, taken while the engines still held the answer
   *  (the unwind below discards it).
   */
  var lastModel: Model | Null = null
  var produceModels: Boolean = true

  def solve(assumptions: ArrayBuffer[Lit], keepGoing: () => Boolean): cdclt.Solver.Result =
    liaSolver.forgetFailedSplits() // a check-sat's splits, not the last one's (see lia.Solver.splitOnDemand)
    liaSolver.keepGoing = keepGoing // the fuel: conflicts of the search, pivots, propagations and branches of LIA
    while sat.vars < atoms.length do sat.newVar() // `atoms` is the source of truth
    while deferredCursor < deferred.length do
      sat.defer(deferred(deferredCursor))
      deferredCursor += 1
    awaitingVars.foreach(sat.prefer) // decided equal before the integers that would tell them apart
    while clauseCursor < clauses.length do
      sat.addClause(clauses(clauseCursor))
      clauseCursor += 1
    lastModel = null
    val result = sat.solve(assumptions.toArray, keepGoing)
    result match
      case cdclt.Solver.Result.Sat(model) =>
        wantFields()
        if !fieldsWanted then wantWitnesses(model)
        // Not the model of a `sat` that is searched again (see boundFields and witnessApart).
        if produceModels && !fieldsWanted && keptApart.isEmpty then lastModel = takeModel()
      case _ => ()
    sat.unwind() // the next assert must find the engines at level 0, not on the trail of this search
    result

  /** Builds the [[Model]] from the live engines: the value of every declared
   *  constant, and the graph of every declared first-order function from the
   *  applications the problem mentions. Uninterpreted sorts get an abstract
   *  element per e-class; a datatype class becomes its constructor term.
   */
  private def takeModel(): Model =
    val elements = HashMap.empty[(Sort, EClassId), Term] // sort and class to element
    val classValues = HashMap.empty[EClassId, BigInt] // the simplex value of an Int class, via any of its terms
    val realClassValues = HashMap.empty[EClassId, lia.Rational]
    for (t, x) <- intVars do
      classes.get(t).foreach { c =>
        if sortOf(t) == Sort.Real then realClassValues(eg.find(c)) = liaSolver.realValue(x)
        else classValues(eg.find(c)) = liaSolver.value(x)
      }
    // A numeral values its class too: a term equated with one by congruence alone (a constructor's
    // field, say) has no variable of its own.
    for case (n @ Term.Num(v), c) <- classes do
      classValues(eg.find(c)) = v
      realClassValues(eg.find(c)) = lia.Rational(v)
    def elementOf(sort: Sort, cls: EClassId): Term =
      val root = eg.find(cls)
      // The name is bare, `@a b!0` for the sort `|a b|`: the printer adds the bars a name needs.
      val bare = sort match
        case Sort.Named(name) => name
        case other => other.text
      elements.getOrElseUpdate((sort, root), Term.Const(s"@$bare!${elements.count(_._1._1 == sort)}"))
    // A number the simplex never saw — a constructor's field invented by a tester's expansion, say — is
    // free of arithmetic but not of the e-graph's disequalities: its class gets a value of its own, past
    // every value known, and not the 0 that `(not (= x (mk 0)))` forbids (issue 26).
    var nextFresh = classValues.values.maxOption.getOrElse(BigInt(0)).max(BigInt(0)) + 1
    def freshInt(root: EClassId): BigInt =
      classValues.getOrElseUpdate(
        root, {
          nextFresh += 1
          nextFresh - 1
        }
      )
    def freshReal(root: EClassId): lia.Rational =
      realClassValues.getOrElseUpdate(root, lia.Rational(freshInt(root)))
    def asRational(value: Term): lia.Rational = value match
      case Term.Num(v) => lia.Rational(v)
      case Term.App(Term.Const("/"), List(Term.Num(p), Term.Num(q))) => lia.Rational(p) / lia.Rational(q)
      case _ => lia.Rational.zero
    val arrayValues = HashMap.empty[EClassId, Term] // an array's value per e-class (see arrayValue)
    val arraysBeingValued = scala.collection.mutable.HashSet.empty[EClassId] // against a cycle of stores or of fields
    // The value of a datatype class with no constructor node: none of its testers holds, so none is
    // asserted of it, and the value is built — a constructor whose tester is not false, its fields
    // from the selectors' classes when the problem has them and fresh values otherwise — one that
    // differs from every other such class's, since the e-graph may keep them apart (issue 26).
    val builtValues = HashMap.empty[EClassId, Term]
    val nodeValues = HashMap.empty[EClassId, Term] // the values of the classes with a constructor
    // The values given to the datatype classes so far, and the values inside them.
    val datatypeValues = HashSet.empty[Term]
    def record(value: Term): Unit =
      if datatypeValues.add(value) then
        value match
          case Term.App(_, args) => args.foreach(record)
          case _ =>
    // The constructor of a class, where it has one, and the classes of its fields.
    def nodeOf(datatype: Datatype, cls: EClassId): Option[(Constructor, List[EClassId])] =
      adt.flatMap(a => Option(a.node(eg, cls))).flatMap(node =>
        datatype.constructors
          .find(c => eg.find(classes(Term.Const(c.name))) == eg.find(node.fun))
          .map((_, node.args.toList))
      )
    val lastFresh = HashMap.empty[Sort, Term] // per datatype, the last value of `freshOf`
    // The class of a tester's or a selector's application to a term of the class `root`, by symbol and
    // class, the first the map of the classes gives: the terms are looked at once, not at every question.
    lazy val unaryApplications =
      val bySymbol = HashMap.empty[String, HashMap[EClassId, EClassId]]
      for case (Term.App(Term.Const(symbol), List(u)), c) <- classes do
        for x <- classes.get(u) do bySymbol.getOrElseUpdate(symbol, HashMap.empty).getOrElseUpdate(eg.find(x), c)
      bySymbol
    def applicationOf(symbol: String, root: EClassId): Option[EClassId] =
      unaryApplications.get(symbol).flatMap(_.get(root))
    def testerOf(root: EClassId, tester: String): Option[Boolean] =
      applicationOf(tester, root).map(c => eg.find(c) == eg.find(trueTerm))
    def selectorOf(root: EClassId, selector: String): Option[EClassId] = applicationOf(selector, root)
    def defaultOf(sort: Sort): Term = datatypeOf(sort) match
      case Some(d) =>
        val c = groundConstructors.getOrElse(
          d.name,
          throw IllegalArgumentException(s"the datatype ${d.name} has no value: it is not well-founded")
        )
        construct(c, c.selectors.map((_, s) => defaultOf(s)))
      case None => valueOfTerm(Term.Const("@default"), sort)
    def construct(c: Constructor, args: List[Term]): Term =
      if args.isEmpty then Term.Const(c.name) else Term.App(Term.Const(c.name), args)
    // A value of the sort that differs from the ones made before, where the sort has values to
    // spare: a new number, or a datatype value around a new value of one of its fields. A sort met
    // again inside its own value takes the last value made for it, so each value is deeper than the
    // one before.
    def freshOf(sort: Sort, seen: Set[Sort]): Option[Term] = sort match
      case Sort.Int => Some(Term.Num(freshInt(eg.newClass())))
      case Sort.Real => Some(Model.rationalTerm(freshReal(eg.newClass())))
      case _ if seen(sort) => Some(lastFresh.getOrElse(sort, defaultOf(sort)))
      case _ =>
        val fields =
          for
            d <- datatypeOf(sort).iterator
            c <- d.constructors.iterator
            ((_, s), i) <- c.selectors.iterator.zipWithIndex
            inner <- freshOf(s, seen + sort)
          yield
            construct(
              c,
              c.selectors.zipWithIndex.map { case ((_, s), j) =>
                if i == j then inner else defaultOf(s)
              }
            )
        val value = fields.nextOption()
        value.foreach(lastFresh(sort) = _)
        value
    def builtValue(datatype: Datatype, root: EClassId, seen: Set[EClassId]): Term =
      builtValues.getOrElseUpdate(
        root, {
          val candidates = datatype.constructors.filter(c => !testerOf(root, c.tester).contains(false))
          val numeric = (s: Sort) => s == Sort.Int || s == Sort.Real
          // A constructor with a number among its fields tells classes apart by that field; an
          // enumeration by taking its constructors in turn.
          val c = candidates.find(_.selectors.exists((_, s) => numeric(s))).getOrElse {
            val nullary = candidates.filter(_.selectors.isEmpty)
            if nullary.nonEmpty then nullary(builtValues.size % nullary.length)
            else candidates.headOption.getOrElse(datatype.constructors.head)
          }
          // The fields from the selectors' classes; a field with none is free, and takes `free` at
          // its position and its default elsewhere.
          def valueWith(c: Constructor, free: Option[(Int, Term)]): Term =
            construct(
              c,
              c.selectors.zipWithIndex.map { case ((selector, s), i) =>
                selectorOf(root, selector) match
                  case Some(field) => valueOfClass(field, s, seen + root)
                  case None if free.exists(_._1 == i) => free.get._2
                  case None if s == Sort.Int => Term.Num(freshInt(eg.newClass()))
                  case None if s == Sort.Real => Model.rationalTerm(freshReal(eg.newClass()))
                  case None => defaultOf(s)
              }
            )
          val value = valueWith(c, None)
          // Another class may have this value already: two fields a tester's expansion invented, both
          // at their default. The e-graph keeps the classes apart, so a function may differ on them,
          // and one value for both gives it two results there. A free field of a sort with values to
          // spare tells them apart (issue 127).
          def freed =
            for
              c <- candidates.iterator
              ((selector, s), i) <- c.selectors.iterator.zipWithIndex
              if selectorOf(root, selector).isEmpty
              fresh <- freshOf(s, Set.empty)
            yield valueWith(c, Some((i, fresh)))
          var distinct = value
          var more = true
          while more && datatypeValues(distinct) do
            freed.nextOption() match
              case Some(other) => distinct = other
              case None => more = false
          record(distinct)
          distinct
        }
      )
    def valueOfClass(cls: EClassId, sort: Sort, seen: Set[EClassId]): Term =
      datatypeOf(sort) match
        case Some(datatype) =>
          val root = eg.find(cls)
          if seen(root) then elementOf(sort, cls) // a cycle, which the rules never let through
          else
            nodeOf(datatype, cls) match
              case None => builtValue(datatype, root, seen)
              case Some((c, args)) =>
                nodeValues.getOrElseUpdate(
                  root, {
                    val value =
                      construct(c, args.zip(c.selectors).map((a, s) => valueOfClass(a, s._2, seen + root)))
                    record(value)
                    value
                  }
                )
        case None =>
          sort match
            case Sort.Int | Sort.IntRange(_, _) => Term.Num(freshInt(eg.find(cls)))
            case Sort.Real => Model.rationalTerm(freshReal(eg.find(cls)))
            case Sort.Bool => Term.boolean(if eg.find(cls) == eg.find(trueTerm) then Formula.True else Formula.False)
            // An array, as a constructor's field: its value as an array, where an abstract element was
            // no array to read or to compare (issue 139). A class reached again while it is valued is
            // inside its own value, through an array of the datatype: only there is it an element.
            case _ if sort.arrow.isDefined && !arraysBeingValued(eg.find(cls)) => arrayValue(cls, sort)
            case _ => elementOf(sort, cls)
    def valueOfTerm(t: Term, sort: Sort): Term =
      (t, sort) match
        case (Term.Num(_), _) => t // a literal argument of an application
        case (Term.Linear(terms, c), _) => // a linear argument or index: computed from its terms (issue 24)
          Model.rationalTerm(terms.foldLeft(lia.Rational(c)) { case (sum, (a, u)) =>
            sum + lia.Rational(a) * asRational(valueOfTerm(u, sortOf(u)))
          })
        case (_, s) if s.arrow.isDefined => // an array: the element of an array of arrays
          if classes.contains(t) then arrayValue(classOf(t), s)
          else Model.constArray(s, valueOfTerm(Term.Const("@default"), applied(s, 1)))
        case (_, Sort.Int | Sort.IntRange(_, _)) =>
          intVars.get(t).map(x => Term.Num(liaSolver.value(x)))
            .orElse(classes.get(t).map(c => Term.Num(freshInt(eg.find(c)))))
            .getOrElse(Term.Num(0))
        case (_, Sort.Real) =>
          intVars.get(t).map(x => Model.rationalTerm(liaSolver.realValue(x)))
            .orElse(classes.get(t).map(c => Model.rationalTerm(freshReal(eg.find(c)))))
            .getOrElse(Term.Num(0))
        case _ =>
          classes.get(t) match
            case Some(cls) => valueOfClass(cls, sort, Set.empty)
            case None =>
              if sort == Sort.Bool then Term.boolean(Formula.False)
              else
                datatypeOf(sort) match
                  case Some(d) => builtValue(d, eg.newClass(), Set.empty) // never reached the e-graph: free
                  case None => elementOf(sort, eg.newClass())
    // A linear term values its class too, from the values of its terms: an argument `(+ a 1)` of a
    // constructor is a leaf of the e-graph without a variable of the simplex, and alone in its class
    // when nothing else reads the field, where a fresh number made `x = (mk (+ a 1))` false (issue 137).
    // The fresh numbers drawn from here on are past these values as well.
    for case (t @ Term.Linear(_, _), c) <- classes do
      val v = asRational(valueOfTerm(t, sortOf(t)))
      if sortOf(t) == Sort.Real then realClassValues.getOrElseUpdate(eg.find(c), v)
      else classValues.getOrElseUpdate(eg.find(c), v.num)
      nextFresh = nextFresh.max(v.floor + 1)
    // An array's value, per e-class: its default and the indices its class was read at — its own
    // selects, the ones of every array equal to it, the write of a store it equals.
    def arrayValue(array: EClassId, sort: Sort): Term =
      val root = eg.find(array)
      arrayValues.getOrElseUpdate(
        root, {
          val indexSort = sort.arrow.get._1.head
          val elementSort = applied(sort, 1) // itself an array, for an array of arrays
          arraysBeingValued += root
          val rows = classes.keys.collect {
            case app @ Term.App(fun, List(j)) if classes.get(fun).exists(c => eg.find(c) == root) =>
              (valueOfTerm(j, indexSort), valueOfTerm(app, elementSort))
          }.toMap
          // A class with a store in it is that store: the base array's value with the write, so that
          // `c = (store a i (select a i))` makes `c` the value of `a`, default and all, and not an
          // array of its own reads over a default of its own; the class's reads then agree with it
          // by the read-over-write lemmas. A class reached again while its base is valued keeps to
          // its reads.
          val written = classes.keys.collectFirst {
            case s @ Term.App(Term.Const(n), List(base, i, v))
                if Names.isStore(n) && classes.get(s).exists(c => eg.find(c) == root)
                  && !arraysBeingValued(eg.find(classOf(base))) =>
              Model.store(arrayValue(classOf(base), sort), valueOfTerm(i, indexSort), valueOfTerm(v, elementSort))
          }
          arraysBeingValued -= root
          // A class with a constant array in it holds that array's value everywhere.
          val constant = constTerms.collectFirst {
            case c @ Term.App(_, List(d)) if eg.find(classes(c)) == root =>
              Model.constArray(sort, valueOfTerm(d, elementSort))
          }
          // A class read at the index beyond the writes holds, away from its rows, what it holds there.
          val settled = beyondIndices.get(indexSort).flatMap(w =>
            if classes.contains(w) then rows.get(valueOfTerm(w, indexSort)) else None
          ).map(Model.constArray(sort, _))
          val start = written.orElse(constant).orElse(settled).getOrElse {
            Model.constArray(sort, valueOfTerm(Term.Const("@default"), elementSort))
          }
          rows.toList.sortBy(_._1.toString).foldLeft(start) { case (acc, (i, v)) => Model.store(acc, i, v) }
        }
      )
    // The datatype classes in an order that keeps their values apart. A class with no constructor
    // takes a value no class has yet, so a class with one is valued as soon as its fields are: before
    // the next built value, which then goes around it. A later one holds a later built value, which
    // is inside none of the values before it.
    val built = ArrayBuffer.empty[(EClassId, Sort)]
    val constructed = ArrayBuffer.empty[(EClassId, Sort, List[EClassId])] // the fields' classes first
    val met = HashSet.empty[EClassId]
    def visit(cls: EClassId, sort: Sort): Unit =
      for datatype <- datatypeOf(sort) if met.add(eg.find(cls)) do
        nodeOf(datatype, cls) match
          case None => built += ((eg.find(cls), sort))
          case Some((c, args)) =>
            for (a, (_, s)) <- args.zip(c.selectors) do visit(a, s)
            constructed +=
              ((
                eg.find(cls),
                sort,
                args.zip(c.selectors).collect {
                  case (a, (_, s)) if datatypeOf(s).isDefined => eg.find(a)
                }
              ))
    for (t, c) <- classes do visit(c, sortOf(t))
    def valueConstructed(): Unit =
      for (root, sort, fields) <- constructed do
        if !nodeValues.contains(root) && fields.forall(f => nodeValues.contains(f) || builtValues.contains(f)) then
          valueOfClass(root, sort, Set.empty)
    valueConstructed()
    for (root, sort) <- built do
      valueOfClass(root, sort, Set.empty)
      valueConstructed()
    val constants = Map.newBuilder[String, Term]
    val functions = Map.newBuilder[String, Model.Function]
    for
      (name, (argSorts, sort)) <- declarations
      if argSorts.isEmpty && sort.arrow.isDefined && !Names.isArrayOperation(name)
    do
      // An array the assertions never read or wrote holds a default everywhere: a value all the same,
      // where `(select arr i)` was printed as itself (issue 48).
      constants += name -> (
        if classes.contains(Term.Const(name)) then arrayValue(classOf(Term.Const(name)), sort)
        else Model.constArray(sort, valueOfTerm(Term.Const("@default"), applied(sort, 1)))
      )
    // A function into arrays: its graph, an array value per application the problem mentions (issue 27).
    for
      (name, (argSorts, sort)) <- declarations
      if argSorts.nonEmpty && sort.arrow.isDefined && !Names.isArrayOperation(name)
    do
      val rows = classes.keys.collect {
        case a @ Term.App(Term.Const(n), args) if n == name && args.length == argSorts.length =>
          (args.zip(argSorts).map(valueOfTerm), arrayValue(classOf(a), sort))
      }.toList
      val default = Model.constArray(sort, valueOfTerm(Term.Const("@default"), applied(sort, 1)))
      functions += name -> Model.Function(argSorts, sort, rows, default)
    for (name, (argSorts, sort)) <- declarations if sort.arrow.isEmpty do
      if argSorts.isEmpty then constants += name -> valueOfTerm(Term.Const(name), sort)
      else
        val rows = classes.keys.collect {
          case a @ Term.App(Term.Const(n), args) if n == name && args.length == argSorts.length =>
            (args.zip(argSorts).map(valueOfTerm), valueOfTerm(a, sort))
        }.toList
        val default = rows.headOption.map(_._2).getOrElse(valueOfTerm(Term.Const("@default"), sort))
        functions += name -> Model.Function(argSorts, sort, rows, default)
    val constSorts = declarations.collect {
      case (name, (Nil, sort)) if Names.isConstArray(name) => name -> applied(sort, 1)
    }.toMap
    Model(constants.result(), functions.result(), datatypes, maps.toMap, finiteSizes.toMap, constSorts)

/** Several theories over disjoint sets of atoms, asserted and checked in turn,
 *  without exchange of equalities between them; `owner(v)` is the theory of the
 *  atom of variable `v`, for explanations.
 */
private final class Theories(
    theories: List[Theory],
    owner: cdclt.Var => Theory,
    shared: cdclt.Var => Boolean,
    anyShared: () => Boolean
) extends Theory:
  /** The theory that implied a literal: the atom of a shared equality belongs
   *  to both, and only the one that implied it can explain it. Only shared
   *  atoms are remembered; every other atom's owner is its implier.
   */
  private val implier = HashMap.empty[cdclt.Var, Theory]

  def assertLit(lit: Lit): Unit = theories.foreach(_.assertLit(lit))
  def propagate(): Theory.Result = combine(_.propagate())
  override def finalCheck(): Theory.Result = combine(_.finalCheck())
  def explain(lit: Lit): ArrayBuffer[Lit] = implier.getOrElse(lit.variable, owner(lit.variable)).explain(lit)
  override def phase(v: cdclt.Var): Option[Boolean] = owner(v).phase(v)
  override def firmPhase(v: cdclt.Var): Option[Boolean] = owner(v).firmPhase(v)
  def push(): Unit = theories.foreach(_.push())
  def pop(): Unit = theories.foreach(_.pop())

  private def combine(check: Theory => Theory.Result): Theory.Result = boundary:
    // A split is passed on at once: its atom exists already, so it must get its variable before any
    // theory is asked again. What the other theories imply comes back when the decision is propagated.
    val results = theories.map(theory =>
      check(theory) match
        case Theory.Result.Ok(lits) => (theory, lits)
        case other => break(other)
    )
    if anyShared() then
      for (theory, lits) <- results; l <- lits if shared(l.variable) do implier(l.variable) = theory
    results.filter(_._2.nonEmpty) match
      case Nil => Theory.ok
      case (_, lits) :: Nil => Theory.Result.Ok(lits) // one theory spoke: its buffer passes through
      case several => Theory.Result.Ok(several.foldLeft(ArrayBuffer.empty[Lit])(_ ++= _._2))
