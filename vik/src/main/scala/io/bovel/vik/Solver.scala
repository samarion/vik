package io.bovel.vik

import scala.collection.immutable.ArraySeq
import scala.collection.mutable.{ArrayBuffer, HashMap, HashSet, LinkedHashMap}
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
 *  [[lia.Solver]] for the bounds. The theories are combined by the model
 *  (model-based theory combination, de Moura and Bjørner 2008): a candidate of
 *  the search is checked against its model, which gives every e-class one value
 *  and every function one result per argument values, and where it does not,
 *  the equality between two shared terms that would make it is added and the
 *  search goes on (see `Encoder.modelDisagreements`). The equalities between
 *  two stores, which the search needs from the start, are the exception (see
 *  `Encoder.pairStores`).
 */
final class Solver(val simplify: Boolean = true, val proofs: Boolean = false):
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

  /** With proofs: the simplifications of the first batch among the encoder's
   *  inputs, and for each, its assertion and the eliminations under it (see
   *  [[Simplifier.traced]]); `None` when one has no proof, which leaves the
   *  search as it is and the proof out.
   */
  private var simplified: Option[Map[Formula, (Formula, List[(Formula, Simplifier.Eliminations)])]] = Some(Map.empty)

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
    if Names.isStore(name) then anyStore = true

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

  /** Formulas the model check requires besides the assertions, which the search
   *  never sees: for a test of what a failed check does, now that no model the
   *  solver makes is known to fail one.
   */
  private[vik] var alsoChecked: List[Formula] = Nil

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
        facts.iterator.map((name, fact) => (s"the range of $name", fact.formula)) ++
        alsoChecked.iterator.map(f => ("a formula checked besides", f))
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

  /** The clausal proof of the last [[solve]]'s `Unsat`, when the solver was
   *  made with `proofs`: over the variables of the SAT search, with the theory
   *  lemmas taken on trust (see [[cdclt.Proof]]).
   */
  def proof: Option[cdclt.Proof] = proved.map(_ => encoder.nn.proof.nn)

  /** Checks the [[proof]] of the last `Unsat` (see `Encoder.checkProof`):
   *  `None` when it holds.
   */
  def checkProof(): Option[String] =
    if proved.nonEmpty && simplified.isEmpty then Some("a simplification without a proof")
    else proved.flatMap((in, as) => encoder.nn.checkProof(in.toSet, as.toSet))

  /** The certificate of the [[proof]] of the last `Unsat`, the S-expression
   *  that `proofs/lean` checks (see [[ProofExport]]), or why it cannot be
   *  written.
   */
  def certificate(surface: Option[ProofExport.Surface] = None): Either[String, String] = (proved, simplified) match
    case (None, _) => Left("no proof")
    case (_, None) => Left("a simplification without a proof")
    case (Some((in, as)), Some(simplifications)) => encoder.nn.certificate(in, simplifications, as, surface)

  /** What the [[proof]] of the last `Unsat` refutes, taken at that solve: the
   *  assertions of the first level, and the variables of the literals assumed
   *  (the selectors of the other levels, the activations of the named
   *  assertions); `None` when the last solve did not answer `Unsat`.
   */
  private var proved: Option[(List[Formula], List[cdclt.Var])] = None

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
    proved = None
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

  /** With proofs, simplifies the first batch as without, when each
   *  simplification comes with its proof ([[Simplifier.implies]]), and encodes
   *  the simplifications; whether it did.
   */
  /** The simplifications of `pairs` (each assertion with its simplification),
   *  each with the conjunctions of the assertion that lost equalities (see
   *  [[Simplifier.traced]]); `None` when one does not follow from its assertion
   *  by [[Simplifier.implies]].
   */
  private def simplifications(
      pairs: List[(Formula, Formula)],
      hints: collection.Map[Formula, Simplifier.Eliminations]
  ): Option[Map[Formula, (Formula, List[(Formula, Simplifier.Eliminations)])]] =
    Option.when(pairs.forall((o, s) => o == s || Simplifier.implies(o, s, hints))) {
      pairs.collect {
        case (o, s) if o != s && s != Formula.True =>
          // the conjunctions of `o` that lost equalities, each subformula visited once
          val under = LinkedHashMap.empty[Formula, Simplifier.Eliminations]
          val seen = HashSet.empty[Formula]
          def walk(f: Formula): Unit = if seen.add(f) then
            f match
              case Formula.And(as) =>
                hints.get(f).foreach(under(f) = _)
                as.foreach(walk)
              case Formula.Or(as) => as.foreach(walk)
              case Formula.Implies(a, b) =>
                walk(a); walk(b)
              case Formula.Ite(c, a, b) =>
                walk(c); walk(a); walk(b)
              case _ => ()
          walk(o)
          s -> (o, under.toList)
      }.toMap
    }

  private def decide(keepGoing: () => Boolean): Result =
    if encoder == null || dirty then
      if encoder != null then encoder.nn.addCounts(retired)
      val e = Encoder(declarations, datatypes.toList, auxiliaries, () => anyStore, () => asked(), proofs)
      encoder = e
      encoded.clear()
      encoded ++= declarations
      dirty = false
      selectors.clear()
      val constructors = datatypes.flatMap(_.constructors.map(_.name)).toSet
      simplified = Some(Map.empty)
      // Each level's assertions in order, the facts of the declarations made in the level among them: a
      // fact before the assertions that came after its declaration. A level's place may have gone with a
      // `pop` since; its facts then come with the last level.
      val placed = facts.values.toList.groupBy(_.level min (levels.length - 1))
      val simplifying = levels.length == 1 && simplify
      def encode(level: Int, assertions: List[Formula], selector: Lit | Null): Unit =
        var due = placed.getOrElse(level, Nil).sortBy(_.index)
        for (formula, i) <- assertions.zipWithIndex do
          while due.nonEmpty && due.head.index <= i do
            e.assert(due.head.formula, null)
            due = due.tail
          if formula != Formula.True || !simplifying then // not one simplified away
            e.assert(formula, selector)
        for fact <- due do e.assert(fact.formula, null)
      if simplifying then
        // One level: the batch is the whole set, so the global simplification is sound to keep.
        val (pairs, gone, hints) =
          Simplifier.traced(levels.head.toList, constructors, named.head.map(_._2).toList, e.step)
        eliminated = gone
        if proofs then simplified = simplifications(pairs, hints)
        encode(0, pairs.map(_._2), null)
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
    // The passes feed one another — a pair of stores gets a witness, the witness an index, the index
    // new store lemmas and new selects — so they run to a fixpoint of the emitted clauses.
    // The loop asks `keepGoing` like a step of the search: the array lemmas of a file can run past any
    // fuel, and a check-sat over its deadline must end, not run on in a thread the caller gave up on.
    // One round can too, and the passes ask from inside (see `Encoder.step`).
    // The Boolean terms are decided in the loop, first: deciding one encodes the terms inside it,
    // a `store` in a Boolean argument among them, which the passes of the same round then see
    // (issue 17). The loop measures the terms decided as well as the clauses, since a round that
    // registers a Boolean and emits nothing else is not done; and the function equalities, since
    // `pairStores` makes one per pair of stores without a clause, and its witness is the next round's
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
      e.pairStores()
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
      // A `sat` whose model needs two arrays or two fields equated or apart that have no atom yet: searched
      // again with it.
      case cdclt.Solver.Result.Sat(_) if e.equateMissing() => decide(keepGoing)
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
        if proofs then proved = Some((e.inputs.toList, assumed.iterator.map(_.variable).toList.distinct.sorted))
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
  /** An array's base and the indices written by the surrounding stores. */
  def storeWrites(array: Term): (Term, List[Term]) =
    @annotation.tailrec
    def collect(term: Term, indices: List[Term]): (Term, List[Term]) = term match
      case Term.App(Term.Const(name), List(base, index, _)) if Names.isStore(name) =>
        collect(base, index :: indices)
      case _ => (term, indices)
    collect(array, Nil)

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

  /** Where a clause of the encoding comes from, for proofs (see
   *  `Encoder.checkProof`):
   *    - `Definition`: a clause of the definition of a variable by its formula
   *      (Tseitin), `True`, or a Boolean term tied to its formula;
   *    - `Assertion`: the clause of an asserted formula, possibly guarded by
   *      the literal of a level or of a named assertion;
   *    - `Retired`: a popped level's selector, false for good;
   *    - `Exhaustive`: one of the testers of a datatype term holds;
   *    - `SharedSplit`: two shared terms are equal, or one is below the other;
   *    - `Numerals`: two numerals are equal or not;
   *    - `Congruence`: arrays equal are equal at an index;
   *    - `ReadOverWrite`: the array axioms of a store;
   *    - `Extensionality`: two functions are equal or differ at fresh
   *      `witnesses`;
   *    - `WitnessRange`: a bit-vector witness index is in its range;
   *    - `SortRange`: a term of a bit-vector sort is in its range;
   *    - `SameBase`: arrays `f` and `g` made by stores from the same base are
   *      equal or differ at one of the `indices` written.
   */
  enum Origin:
    case Definition
    case Assertion(formula: Formula)
    case Retired
    case Exhaustive(term: Term)
    case SharedSplit
    case Numerals
    case Congruence
    case ReadOverWrite
    case Extensionality(witnesses: List[Term])
    case WitnessRange(witness: Term, width: Int)
    case SortRange(term: Term)
    case SameBase(f: Term, g: Term, indices: List[Term])

private final class Encoder(
    declarations: HashMap[String, (List[Sort], Sort)],
    datatypes: List[Datatype],
    auxiliaries: HashSet[String], // the solver's set, read when a constant gets its LIA variable
    anyStore: () => Boolean, // the solver's flag, read at every array pass (see Solver.anyStore)
    keepGoing: () => Boolean, // of the solve under way (see Solver.solve)
    proofs: Boolean
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
  // The applications among `terms` by their function, and the stores among them, both in arrival order.
  private val applications = HashMap.empty[Term, ArrayBuffer[Term.App]]
  private val storeTerms = ArrayBuffer.empty[Term.App]
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
   *  [[registerShared]] start over, is rare.
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

  private def linkArithmeticEquality(e: Lit, a: Term, b: Term, late: Boolean = false): Unit =
    // The atom is the two bounds when true; when false, the disequality is a choice of the SAT solver
    // between the two sides, `a − b ≤ −1` or `a − b ≥ 1`, as a clause over bound atoms — not a
    // disequality the LIA solver decides by branching, without learning, at every value the
    // relaxation lands on (hundreds of them on `wisas`). Linked late, the atom may be decided for
    // good already, and the theory would not hear of it again: its two bounds when true are clauses.
    def equalOrApart(x: lia.Var, c: BigInt): Unit =
      // Below `c` and above it. Over the integers that is `≤ c − 1` and `> c`, which leaves nothing
      // between; over the reals it has to be the strict bound `< c`, or the clause forbids the open
      // band `(c − 1, c)` and forces two shared terms less than one apart to be equal (issue 8).
      val below = if liaSolver.isInteger(x) then bound(x, c - 1, false) else bound(x, c, true)
      val above = bound(x, c, false)
      mean(below, Formula.Less(a, b))
      mean(above, Formula.Le(a, b))
      emit(Array(e, below, above.neg), Encoder.Origin.SharedSplit)
      if !late then liaAtoms(e.variable) = LiaTheory.Atom.Equal(x, c)
      else
        emit(Array(e.neg, above), Encoder.Origin.SharedSplit)
        emit(Array(e.neg, below.neg), Encoder.Origin.SharedSplit)
      // Over the reals the two sides are bounds on the same constant, and `< c` implies `≤ c`: said
      // here, the search does not have to reach the theory to find that out.
      if !liaSolver.isInteger(x) then emit(Array(below.neg, above), Encoder.Origin.SharedSplit)
      guidedAtoms += below.variable
      guidedAtoms += above.variable
      anySharedAtom = true
    Term.linear(List((1, a), (-1, b))) match
      case Term.Num(v) => emit(Array(if v.signum == 0 then e else e.neg), Encoder.Origin.Numerals) // two numerals
      case Term.Linear(terms, c) => equalOrApart(slack(terms), -c)
      case difference => equalOrApart(intVar(difference), 0)

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
      val stores = storeTerms.toList
      val apps = if stores.isEmpty then Nil else terms.iterator.collect { case a: Term.App => a }.toList
      for s <- stores; a <- apps do
        step()
        if applicable(a, s) && done.add((a, s)) then
          more = true
          val applied = Term.App(s, a.args)
          equated += ((a, applied))
          recordFunctionEqualities = false
          emit(Array(lit(Formula.Eq(a.fun, s)).neg, lit(Formula.Eq(a, applied))), Encoder.Origin.Congruence)
          recordFunctionEqualities = true
    // An application equated with an integer term is one, and conversely (for the final check).
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
    a != s && a.fun != s && a.args.length == 1 && sortOf(a.fun) == sortOf(s)

  /** Extensionality: for every equality atom between function-sorted terms, the
   *  lemma `f = g ∨ f(c) ≠ g(c)` with fresh constants `c` (the witnesses of the
   *  difference), repeated while the new equality is between functions (a
   *  curried result). So `unsat` and `sat` follow the usual semantics of
   *  functions on the equalities of the assertions.
   */
  private val extensionalityDone = scala.collection.mutable.HashSet.empty[Formula]

  /** The function equalities used outside application lemmas, in the order they
   *  first need an extensionality witness.
   */
  private val functionEqualities = ArrayBuffer.empty[Formula]
  private var recordFunctionEqualities = true

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
      for case eq @ Formula.Eq(f, g) <- functionEqualities.toList if !done(eq) do
        done += eq
        if !assertedEqualities(eq) then
          sortOf(f).arrow.orElse(sortOf(g).arrow) match
            case Some((params, _)) =>
              more = true
              val (fBase, fWrites) = Encoder.storeWrites(f)
              val (gBase, gWrites) = Encoder.storeWrites(g)
              if fBase == gBase then
                // Arrays built from the same base can differ only at a written index. Using these
                // indices keeps the new reads and sharing from growing with each fresh witness.
                val indices = (fWrites ::: gWrites).distinct
                val differences = indices.map(i => lit(Formula.Eq(selectTerm(f, i), selectTerm(g, i))).neg)
                emit((lit(eq) :: differences).toArray, Encoder.Origin.SameBase(f, g, indices))
              else
                // A witness is a constant of the index sort like any other: of a range of the integers, it
                // gets the range with its class, or two arrays over `(_ BitVec 1)` agreeing at both
                // indices could still differ at it (issue 20).
                val witnesses = params.map { sort =>
                  val name = witnessName()
                  introduced(name) = sort
                  Term.Const(name)
                }
                emit(
                  Array(lit(eq), lit(Formula.Eq(applyAll(f, witnesses), applyAll(g, witnesses))).neg),
                  Encoder.Origin.Extensionality(witnesses)
                )
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
            null,
            Encoder.Origin.Exhaustive(t)
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
            val bounds = List(Formula.Le(Term.Num(lower), t), Formula.Le(t, Term.Num(upper)))
            // For the proof: the range of a witness of an index, or what the sort of the term says.
            val origin = t match
              case Term.Const(name) if Names.isWitness(name) =>
                Encoder.Origin.WitnessRange(t, (upper + 1).bitLength - 1)
              case _ => Encoder.Origin.SortRange(t)
            assert(Formula.And(bounds), null, origin)
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
   *  what their sorts say ([[assertSorts]]) and meet one another in the final
   *  check, so their values are among their sorts': a tester that holds expands
   *  its term into the constructor over the term's fields, whatever the term's
   *  own sort, and nothing else bounds them. Two terms built by one constructor
   *  over a field of sort `Unit` stayed apart, against the one value of `Unit`
   *  (issue 125), and three over a field of one bit (issue 126).
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
  liaSolver.proofs = proofs
  private val intVars = HashMap.empty[Term, lia.Var] // `Int`-sorted constants and applications
  private val slacks = HashMap.empty[List[(BigInt, Term)], lia.Var] // linear combinations of them
  private val termOfVar = HashMap.empty[lia.Var, Term] // with proofs, the term of each of these variables
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

  /** With proofs, where each clause comes from (see [[Encoder.Origin]]), and
   *  what each variable stands for: the formula it was encoded for, `null` for
   *  a selector or an activation literal.
   */
  private val origins = ArrayBuffer.empty[Encoder.Origin]
  private val meanings = ArrayBuffer.empty[Formula | Null]

  private inline def emit(clause: Array[Lit], inline origin: Encoder.Origin): Unit =
    clauses += clause
    if proofs then origins += origin

  private inline def mean(l: Lit, inline formula: Formula): Unit =
    if proofs then
      while meanings.length <= l.variable do meanings += null
      meanings(l.variable) = formula

  private val trueLit = freshVar() // a variable asserted true, for `True`
  mean(trueLit, Formula.True)
  emit(Array(trueLit), Encoder.Origin.Definition)
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
   *  (two arrays under the same function are compared by the final check, with
   *  or without an integer or a `store` around: issue 133), or some equality is
   *  between functions (arrays): the final check's registration and
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
      terms += term
      term match
        case a: Term.App =>
          applications.getOrElseUpdate(a.fun, ArrayBuffer.empty) += a
          a match
            case Term.App(Term.Const(name), List(_, _, _)) if Names.isStore(name) => storeTerms += a
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

  def litOf(f: Formula): Option[Lit] = lits.get(literalKey(f))

  private def selectTerm(array: Term, index: Term): Term = array match
    case Term.App(Term.Const(n), _) if Names.isStore(n) => Term.App(array, List(index))
    case _ => Term.App(array, List(index))

  private val arrayWritesDone = scala.collection.mutable.HashSet.empty[Term]
  private var storesPaired = 0 // the stores of `storeTerms` paired with every store before them
  private val arrayReadsDone = scala.collection.mutable.HashSet.empty[(Term, Term)]

  def arrayLemmas(): Unit = if anyStore() then
    val stores = storeTerms.toList
    val indices = scala.collection.mutable.HashMap.empty[Sort, scala.collection.mutable.LinkedHashSet[Term]]
    def index(sort: Sort, j: Term): Unit =
      indices.getOrElseUpdate(sort, scala.collection.mutable.LinkedHashSet.empty) += j
    for a <- terms do
      a match
        case Term.App(f, List(j)) if sortOf(f).arrow.isDefined => index(sortOf(f), j)
        case _ => ()
    for s <- stores do index(sortOf(s), s.args(1))
    // Two numbers are equal by two bounds; two indices of a range of the integers by an equality atom, as
    // they were while the index sort alone told a bit-vector from an integer.
    def equalAt(sort: Sort, l: Term, r: Term): Formula =
      if Encoder.numeric(sort) then Formula.IntEq(l, r) else Formula.Eq(l, r)
    def equalIndex(sort: Sort, l: Term, r: Term): Formula =
      if sort.isInstanceOf[Sort.IntRange] then Formula.Eq(l, r) else equalAt(sort, l, r)
    for case s @ Term.App(_, List(a, i, v)) <- stores do
      val sort = sortOf(s)
      val indexSort = sort.arrow.get._1.head
      val elementSort = applied(sort, 1) // an array, for an array of arrays
      if arrayWritesDone.add(s) then
        val written = equalAt(elementSort, selectTerm(s, i), v)
        val l = lit(written)
        // The write is a permanent fact, including when the value written is an array.
        if elementSort.arrow.isDefined then assertedEqualities += literalKey(written)
        emit(Array(l), Encoder.Origin.ReadOverWrite)
      for j <- indices.getOrElse(sort, Nil) do
        step()
        if j != i && arrayReadsDone.add((s, j)) then
          emit(
            Array(lit(equalIndex(indexSort, i, j)), lit(equalAt(elementSort, selectTerm(s, j), selectTerm(a, j)))),
            Encoder.Origin.ReadOverWrite
          )

  /** Every two stores of one sort, and the arrays under them: an equality atom
   *  each, whose witness decides the arrangement of the store chains, which the
   *  search needs. Left to the final check with the other arrays,
   *  `wchains002se` went from 0.4 s to no answer in 30 s.
   */
  def pairStores(): Unit =
    val n = storeTerms.length
    for i <- 0 until n; j <- (i + 1).max(storesPaired) until n do
      val (s, t) = (storeTerms(i), storeTerms(j))
      if s.fun == t.fun then
        for (x, y) <- (s :: s.args).zip(t :: t.args) if x != y && sortOf(x).arrow.isDefined do
          step()
          lit(Formula.Eq(x, y))
    storesPaired = n

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

  /** The atom `x ≤ c` of a split of the LIA solver, standing for the bound on
   *  the term or the combination of `x`.
   */
  private def splitBound(x: lia.Var, c: BigInt): Lit =
    val l = bound(x, c, false)
    if proofs then
      for t <- termOfVar.get(x) do mean(l, Formula.Le(t, Term.Num(c)))
    l

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
   *  shared term, see [[registerShared]]).
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
        if proofs then termOfVar(x) = term
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
        if proofs then termOfVar(x) = Term.Linear(terms, 0)
        x
      }
    )

  /** Each equality encoded, by its other orientation: `(= b a)` is `(= a b)` if
   *  that came first. An equality has one atom in either orientation, so its
   *  meanings, the arithmetic one and an array's witness, are given once.
   */
  private val orientations = HashMap.empty[Formula.Eq, Formula.Eq]

  private def literalKey(formula: Formula): Formula = formula match
    case eq: Formula.Eq => orientations.getOrElse(eq, eq) // the proof reads either orientation as the literal's
    case _ => formula

  /** The literal standing for `formula`, defining it by clauses if needed. */
  private def lit(formula: Formula): Lit =
    val key = literalKey(formula)
    // An equality first encoded for an application lemma needs a witness once an assertion or
    // the final check uses it.
    if recordFunctionEqualities && lemmaEqualities.nonEmpty && lemmaEqualities.remove(key) then
      functionEqualities += key
    lits.getOrElseUpdate(key, encode(key))

  /** The function equalities encoded for the application lemmas alone, which
   *  get no witness (see [[applicationLemmas]]) until another use needs one.
   */
  private val lemmaEqualities = scala.collection.mutable.HashSet.empty[Formula]

  private def encode(formula: Formula): Lit =
    import Formula.*
    step()
    formula match
      case True => trueLit
      case False => trueLit.neg
      case Not(arg) => lit(arg).neg
      case eq @ Eq(lhs, rhs) =>
        if lhs == rhs then trueLit
        else
          boolean(lhs)
          boolean(rhs)
          orientations(Eq(rhs, lhs)) = eq
          if sortOf(lhs).arrow.isDefined || sortOf(rhs).arrow.isDefined then
            anyFunctionEquality = true
            if recordFunctionEqualities then functionEqualities += formula else lemmaEqualities += formula
          val e = atom(classOf(lhs), classOf(rhs))
          mean(e, formula)
          // Two numbers, of one sort or not: the equality has its arithmetic meaning from the start.
          if isInt(lhs) && isInt(rhs) then linkArithmeticEquality(e, lhs, rhs)
          else if sortOf(lhs) == Encoder.unknown || sortOf(rhs) == Encoder.unknown then
            untypedEqualities += ((e, lhs, rhs))
          e
      case Pred(term) =>
        // Two-valued from its first literal on: the theory merges a false term with `false` only for
        // terms it knows as Boolean, and a term known only from a later solve keeps the assignment
        // of an earlier one, which is never asserted again (issue 14).
        boolean(term)
        val e = atom(classOf(term), trueTerm)
        mean(e, formula)
        term match
          case Term.Bool(inner) => // `t = true` iff the formula holds
            val l = lit(inner)
            emit(Array(e.neg, l), Encoder.Origin.Definition)
            emit(Array(l.neg, e), Encoder.Origin.Definition)
          case _ => ()
        e
      case Le(lhs, rhs) =>
        val l = comparison(lhs, rhs, strict = false)
        if l.variable != trueLit.variable then mean(l, formula)
        l
      case Less(lhs, rhs) =>
        val l = comparison(lhs, rhs, strict = true)
        if l.variable != trueLit.variable then mean(l, formula)
        l
      case Implies(lhs, rhs) => lit(Or(List(Not(lhs), rhs)))
      // The definitions of fresh variables (Tseitin).
      case And(args) =>
        val v = freshVar()
        mean(v, formula)
        val as = args.map(lit)
        for a <- as do emit(Array(v.neg, a), Encoder.Origin.Definition)
        emit((v +: as.map(_.neg)).toArray, Encoder.Origin.Definition)
        v
      case Or(args) =>
        val v = freshVar()
        mean(v, formula)
        val as = args.map(lit)
        for a <- as do emit(Array(v, a.neg), Encoder.Origin.Definition)
        emit((v.neg +: as).toArray, Encoder.Origin.Definition)
        v
      case Iff(lhs, rhs) =>
        val v = freshVar()
        mean(v, formula)
        val (a, b) = (lit(lhs), lit(rhs))
        emit(Array(v.neg, a.neg, b), Encoder.Origin.Definition)
        emit(Array(v.neg, a, b.neg), Encoder.Origin.Definition)
        emit(Array(v, a, b), Encoder.Origin.Definition)
        emit(Array(v, a.neg, b.neg), Encoder.Origin.Definition)
        v
      case Ite(cond, thn, els) =>
        val v = freshVar()
        mean(v, formula)
        val (c, t, e) = (lit(cond), lit(thn), lit(els))
        emit(Array(v.neg, c.neg, t), Encoder.Origin.Definition)
        emit(Array(v.neg, c, e), Encoder.Origin.Definition)
        emit(Array(v, c.neg, t.neg), Encoder.Origin.Definition)
        emit(Array(v, c, e.neg), Encoder.Origin.Definition)
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
    if proofs && under == null then inputs += formula
    assert(formula, under, Encoder.Origin.Assertion(formula))

  /** With proofs, the formulas asserted for good: the inputs of the proof. */
  val inputs = ArrayBuffer.empty[Formula]

  /** With proofs, the formulas each selector or activation literal guards. */
  private val guards = scala.collection.mutable.LinkedHashMap.empty[cdclt.Var, ArrayBuffer[Formula]]

  private def assert(formula: Formula, under: Lit | Null, origin: Encoder.Origin): Unit =
    meet(formula)
    val l = lit(formula)
    formula match
      // An equality asserted for good needs no witness; one under a level's selector is gone with
      // the level, and its negation then needs one like any other (issue 19).
      case Formula.Eq(_, _) if under == null => assertedEqualities += literalKey(formula)
      case _ => ()
    if proofs && under != null then guards.getOrElseUpdate(under.nn.variable, ArrayBuffer.empty) += formula
    emit(if under == null then Array(l) else Array(under.nn.neg, l), origin)

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
  def newSelector(): Lit =
    val s = freshVar()
    if proofs then assumptions += s.variable
    s

  /** With proofs, the variables of the selectors and activations: the only ones
   *  a solve assumes.
   */
  private val assumptions = scala.collection.mutable.HashSet.empty[cdclt.Var]

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
        if proofs then
          guards(a.variable) = ArrayBuffer(formula)
          assumptions += a.variable
        emit(Array(a.neg, lit(formula)), Encoder.Origin.Assertion(formula))
        a
      }
    )

  /** The failed assumptions of the last `Unsat`, for [[Solver.unsatCore]]. */
  def core(): Array[Lit] = sat.unsatCore

  /** Retires a popped level's selector: false for good, its clauses inert. */
  def retire(selector: Lit): Unit = emit(Array(selector.neg), Encoder.Origin.Retired)

  /** The theories and the SAT solver, alive across [[solve]]s: everything
   *  learned stays. Both theories are always attached — their atom buffers grow
   *  as terms arrive, possibly only after the first solve.
   */
  /** Whether some variable is an atom of both theories (a shared equality):
   *  only then does the combination need to remember impliers.
   */
  private var anySharedAtom = false
  private val preferEqual = HashSet.empty[cdclt.Var]

  private val ufTheory = UfTheory(eg, atoms, trueTerm, falseTerm, booleanClasses)
  private val liaTheory = LiaTheory(liaSolver, liaAtoms, guidedAtoms, splitBound)
  private val theories = List(ufTheory, liaTheory)

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
      () => anySharedAtom,
      preferEqual
    ),
    proofs = proofs
  )
  def proof: cdclt.Proof | Null = sat.proof

  /** The certificate of [[proof]], a refutation of `inputs` with the literals
   *  of `assumed` (see [[checkProof]]), with the script it lowers when given
   *  (see [[ProofExport]]), or why it cannot be written.
   */
  def certificate(
      inputs: List[Formula],
      simplified: collection.Map[Formula, (Formula, List[(Formula, Simplifier.Eliminations)])],
      assumed: List[cdclt.Var],
      surface: Option[ProofExport.Surface]
  ): Either[String, String] =
    ProofExport(
      ProofExport.Input(
        declarations.map { case (n, (as, r)) => (n, (as.map(SortText.of), SortText.of(r))) },
        introduced.map((n, s) => (n, SortText.of(s))),
        t => SortText.of(sortOf(t)),
        classes.iterator.map((t, x) => (x, t)).toMap,
        trueTerm,
        falseTerm,
        atoms,
        liaAtoms,
        meanings,
        trueLit,
        intVars.iterator.map((t, x) => (x, t)).toMap,
        liaSolver.numVars,
        liaSolver.form,
        sat.proof.nn,
        datatypes,
        inputs,
        simplified,
        guards.iterator.map((v, fs) => (v, fs.toList)).toList,
        assumed
      ),
      surface
    )

  /** Checks [[proof]], a refutation of `inputs` (the assertions of the first
   *  level) with the literals of `assumed` (the selectors of the other levels,
   *  the activations of the named assertions): its conclusion is the clause of
   *  the negations of some of these; its derivations check; its input clauses
   *  against where they come from (see [[InputClauses]]); the lemmas of the
   *  theories against their certificates (see [[UfLemmas]] and [[LiaLemmas]]),
   *  the atoms these mention against the formulas their variables stand for.
   *  `None` when it holds, what is wrong otherwise.
   */
  def checkProof(inputs: Set[Formula], assumed: Set[cdclt.Var]): Option[String] =
    val constructors = datatypes.flatMap(_.constructors).map(c =>
      classOf(Term.Const(c.name)) -> c.selectors.map((s, _) => classOf(Term.Const(s)))
    ).toMap
    val testers =
      datatypes.flatMap(_.constructors).map(c => classOf(Term.Const(c.tester)) -> classOf(Term.Const(c.name))).toMap
    val uf = UfLemmas(atoms, trueTerm, falseTerm, trueLit, constructors, testers)
    val arithmetic = LiaLemmas(liaSolver, liaAtoms)
    val clauses = InputClauses(
      meanings,
      trueLit,
      inputs,
      assumptions,
      assumed,
      sort => datatypes.find(d => SortText.of(Sort.Named(d.name)) == sort).map(_.constructors.map(_.tester)),
      t => SortText.of(sortOf(t)),
      declarations.contains
    )
    // The classes of the certificates are those of terms: a leaf is a class the encoder made for a term
    // (constant, number, combination or formula), at the first level, never undone; an application is its
    // function applied to its arguments, recorded with the certificate.
    val p = sat.proof.nn
    val conclusion = p.steps(p.conclusion).clause
    val unassumed = conclusion.find(l => l.positive || !assumed(l.variable))
    unassumed.map(l => s"the conclusion has ${l.show}, not the negation of an assumption").orElse(checkAtoms()).orElse(
      sat.proof.nn.check(
        lemma =>
          lemma.certificate match
            case c: UfTheory.Certified => uf.check(lemma.clause, c)
            case c: lia.Certificate => arithmetic.check(lemma.clause, c)
            case _ => Some("no certificate")
        ,
        input =>
          input.origin match
            case o: Encoder.Origin => clauses.check(input.clause, o)
            case _ => Some("no origin")
      ).orElse(clauses.finish())
    )

  /** Whether every atom of the theories is that of the formula its variable
   *  stands for: an equality atom on the classes of its sides, a bound on the
   *  LIA variable of the difference of its sides.
   */
  private def checkAtoms(): Option[String] =
    val termOf = intVars.iterator.map((t, x) => (x, t)).toMap
    val combinationOf = slacks.iterator.map((ts, x) => (x, ts.toSet)).toMap
    // Whether `lhs − rhs ≤ c` is a bound on `x`: `x` stands for `lhs − rhs` up to a constant.
    def on(lhs: Term, rhs: Term, x: lia.Var, c: BigInt): Boolean = Term.linear(List((1, lhs), (-1, rhs))) match
      case Term.Linear(terms, k) =>
        c == -k &&
        (combinationOf.get(x).contains(terms.toSet) ||
          (terms match
            case List((a, t)) => a == 1 && termOf.get(x).contains(t)
            case _ => false))
      case Term.Num(_) => false
      case t => c == 0 && termOf.get(x).contains(t)
    (0 until math.min(meanings.length, atoms.length)).iterator.flatMap { v =>
      val m = meanings(v)
      val uf = atoms(v)
      val arith = liaAtoms(v)
      def wrong = Some(s"the atom of variable $v is not that of $m")
      val ufOk = uf == null ||
        (m match
          case Formula.Eq(l, r) => classes.get(l).contains(uf._1) && classes.get(r).contains(uf._2)
          case Formula.Pred(t) => classes.get(t).contains(uf._1) && uf._2 == trueTerm
          case _ => false)
      val arithOk = arith == null ||
        ((arith, m) match
          case (LiaTheory.Atom.Bound(x, c, strict), Formula.Le(l, r)) => !strict && on(l, r, x, c)
          case (LiaTheory.Atom.Bound(x, c, strict), Formula.Less(l, r)) =>
            if strict then on(l, r, x, c) else liaSolver.isInteger(x) && on(l, r, x, c + 1)
          case (LiaTheory.Atom.Equal(x, c), Formula.Eq(l, r)) => on(l, r, x, c)
          case _ => false)
      if ufOk && arithOk then None else wrong
    }.nextOption()

  private var clauseCursor = 0

  /** The model of the last `Sat`, taken while the engines still held the answer
   *  (the unwind below discards it).
   */
  var lastModel: Model | Null = null
  var produceModels: Boolean = true

  private val sharedNumbers = ArrayBuffer.empty[Term] // the terms of checked sorts, in arrival order
  private val numericApplications = ArrayBuffer.empty[Term.App] // the applications with such an argument
  // The applications with an array or a datatype argument or result: the final check compares them by
  // the values of those in the candidate model (see modelDisagreements). And the datatype terms, whose
  // classes the e-graph keeps apart the model must give two values.
  private val modelApplications = ArrayBuffer.empty[Term.App]
  private val datatypeTerms = ArrayBuffer.empty[Term]
  private var registeredTerms = 0

  /** The equalities with an undeclared side, a term of the Solver API without a
   *  sort: their arithmetic meaning waits until both sides are known as
   *  integers (see [[intTerms]]), which can be after they were encoded.
   */
  private val untypedEqualities = ArrayBuffer.empty[(Lit, Term, Term)]
  private var registeredNoted = 0 // the size of `intTerms` at the last registration

  private def registerShared(): Unit =
    // A term newly known as an integer: the terms are registered again, with it a number now.
    if intTerms.size != registeredNoted then
      registeredNoted = intTerms.size
      registeredTerms = 0
      sharedNumbers.clear()
      numericApplications.clear()
      modelApplications.clear()
      datatypeTerms.clear()
      untypedEqualities.filterInPlace((e, a, b) =>
        if isInt(a) && isInt(b) then
          linkArithmeticEquality(e, a, b, late = true)
          false
        else true
      )
    while registeredTerms < terms.length do
      step()
      val term = terms(registeredTerms)
      if datatypeOf(sortOf(term)).isDefined then datatypeTerms += term
      if isInt(term) then
        term match
          case Term.Num(_) | Term.Linear(_, _) => () // numerals are values, linear operands already have variables
          case _ => intVar(term)
        sharedNumbers += term
      term match
        case app: Term.App =>
          if app.args.exists(isInt) then numericApplications += app
          if (app :: app.args).exists(t => sortOf(t).arrow.isDefined || datatypeOf(sortOf(t)).isDefined) then
            modelApplications += app
        case _ => ()
      registeredTerms += 1

  /** The simplex's value of a term in its current solution, an integer, or a
   *  real at the δ of `real`: a term with a variable, or a linear term over
   *  such terms. The final check and the model both take their numbers from
   *  here. Every operand of a linear term with a class has its variable (see
   *  [[classOfNew]]).
   */
  private def numericValue(term: Term, real: lia.Var => lia.Rational): lia.Rational = term match
    case Term.Num(value) => lia.Rational(value)
    case Term.Linear(operands, constant) =>
      operands.foldLeft(lia.Rational(constant)) { case (sum, (coefficient, operand)) =>
        sum + lia.Rational(coefficient) * numericValue(operand, real)
      }
    case _ =>
      val x = intVars(term)
      if sortOf(term) == Sort.Real then real(x) else lia.Rational(liaSolver.value(x))

  private final case class ArithmeticSplit(left: Term, right: Term, equalFirst: Boolean)

  /** Every numeric e-class needs one value. Distinct numeric classes can share
   *  a value as long as the observed function tables are still well-defined.
   *  Explicit numeric disequalities already have arithmetic bounds, so this
   *  check only needs to find collisions in the tables. A real is compared at
   *  the δ the model takes it at, so the model agrees with what is checked.
   */
  private def arithmeticDisagreements(): List[ArithmeticSplit] =
    val real = liaSolver.realValues()
    val byClass = HashMap.empty[EClassId, (Term, lia.Rational)]
    val numbers = HashMap.empty[Term, lia.Rational]
    val disagreements = List.newBuilder[ArithmeticSplit]
    for term <- sharedNumbers do
      step()
      val cls = eg.find(classes(term))
      val value = numericValue(term, real)
      numbers(term) = value
      val (firstInClass, classValue) = byClass.getOrElseUpdate(cls, (term, value))
      if classValue != value then disagreements += ArithmeticSplit(firstInClass, term, equalFirst = true)
    val sameClass = disagreements.result()
    if sameClass.nonEmpty then return sameClass

    // Interpret numbers in the simplex, Booleans by their truth values, and
    // the other sorts by their e-classes, as takeModel does.
    type Value = Either[EClassId, lia.Rational]
    val truth = eg.find(trueTerm)
    val falsity = eg.find(falseTerm)
    def valueOf(term: Term): Value =
      numbers.get(term) match
        case Some(value) => Right(value)
        case None =>
          val root = eg.find(classes(term))
          Left(if sortOf(term) == Sort.Bool && root != truth then falsity else root)

    val rows = HashMap.empty[(EClassId, List[Value]), (Term.App, Value)]
    val splits = scala.collection.mutable.LinkedHashSet.empty[(Term, Term)]
    val outputs = scala.collection.mutable.LinkedHashSet.empty[(Term, Term)]
    for app <- numericApplications do
      step()
      // By the head's class, not its syntax: `(select a i)` and `(select b j)` share a row once the e-graph
      // knows `a = b`, and must agree when `i` and `j` take one value.
      val key = (eg.find(classes(app.fun)), app.args.map(valueOf))
      val result = valueOf(app)
      val (first, expected) = rows.getOrElseUpdate(key, (app, result))
      if expected != result then
        // If all arguments had the same e-class, congruence would already
        // identify the results. Nonnumeric arguments have matching classes.
        val (a, b) = first.args.zip(app.args).find { (a, b) =>
          numbers.contains(a) && eg.find(classes(a)) != eg.find(classes(b))
        }.get
        if !splits((b, a)) then splits += ((a, b))
        // If the inputs are later equated, congruence can propagate this result
        // equality into arithmetic during the next search.
        if numbers.contains(app) && !outputs((app, first)) && !lits.contains(literalKey(Formula.Eq(first, app)))
        then outputs += ((first, app))
    // Try separating the inputs first: that repairs the candidate collision
    // without changing the function's current results.
    (splits.iterator ++ outputs.iterator).map((a, b) => ArithmeticSplit(a, b, equalFirst = false)).toList

  /** The equalities the final check found missing in the last candidate, for
   *  the solver to give their atoms before it searches again (see
   *  [[equateMissing]]).
   */
  private var missingEqualities = List.empty[(Term, Term)]

  /** What the final check finds in the candidate model beyond the numbers: the
   *  rows of the functions with an array or a datatype argument or result, and
   *  the datatype classes the e-graph keeps apart. Arrays and datatype values
   *  are compared by the values of their e-classes in the model (not through
   *  the model's graph of a function, which gives `(g a)` and `(g b)` one
   *  result once `a` and `b` are one value), numbers by the simplex's, the rest
   *  by their e-classes.
   *
   *  Two rows with one key and two results need two arguments apart: a numeric
   *  one is split as in [[arithmeticDisagreements]]; two arrays need an
   *  equality atom, with its extensionality witness, made only where a model
   *  needs one (issue 39's shape: `f(a) ≠ f(b)` with `a` and `b` equal as
   *  arrays); two datatype values the fields below. Two datatype classes apart
   *  in the e-graph with one value have equal fields: their fields get their
   *  equality atoms, which the search decides like any other. Preferred equal,
   *  against the classes' disequality, they took `valid-LawTypeArgsElim__99` to
   *  2.6 times the work of the eager pairs. Before these, an eager pass paired
   *  the fields of every two terms of a constructor or a selector: `x ≠ y` with
   *  equal fields, equal in arithmetic only, answered `sat` with a model that
   *  failed its check (`datatype__selectortrigger001`).
   */
  private def modelDisagreements(classValue: Term => Term): (List[ArithmeticSplit], List[(Term, Term)]) =
    val real = liaSolver.realValues()
    val truth = eg.find(trueTerm)
    val falsity = eg.find(falseTerm)
    val modelValues = HashMap.empty[Term, Term]
    def modelValue(term: Term): Term = modelValues.getOrElseUpdate(term, Model.normal(classValue(term)))
    def valueOf(term: Term): Any =
      val sort = sortOf(term)
      if isInt(term) then numericValue(term, real)
      else if sort.arrow.isDefined || datatypeOf(sort).isDefined then modelValue(term)
      else
        val root = eg.find(classes(term))
        if sort == Sort.Bool && root != truth then falsity else root
    val numeric = scala.collection.mutable.LinkedHashSet.empty[(Term, Term)]
    val missing = scala.collection.mutable.LinkedHashSet.empty[(Term, Term)]
    // Two datatype terms of one value: their fields at the constructor of the value.
    def fields(x: Term, y: Term): Unit =
      val constructor = modelValue(x) match
        case Term.App(Term.Const(c), _) => Some(c)
        case Term.Const(c) => Some(c)
        case _ => None
      val selectors =
        for d <- datatypeOf(sortOf(x)).toList; c <- d.constructors if constructor.contains(c.name); s <- c.selectors
        yield s._1
      if selectors.isEmpty then missing += ((x, y)) // one constructor without fields: one value
      for s <- selectors do missing += ((Term.App(Term.Const(s), List(x)), Term.App(Term.Const(s), List(y))))
    val rows = HashMap.empty[(EClassId, List[Any]), (Term.App, Any)]
    for app <- modelApplications do
      step()
      val key = (eg.find(classes(app.fun)), app.args.map(valueOf))
      val result = valueOf(app)
      val (first, expected) = rows.getOrElseUpdate(key, (app, result))
      if expected != result then
        val apart = first.args.zip(app.args).filter((a, b) => eg.find(classes(a)) != eg.find(classes(b)))
        apart.find((a, _) => isInt(a)) match
          case Some((a, b)) => if !numeric((b, a)) then numeric += ((a, b))
          case None =>
            apart.find((a, _) => sortOf(a).arrow.isDefined) match
              case Some((a, b)) => missing += ((a, b))
              case None => for (a, b) <- apart.find((a, _) => datatypeOf(sortOf(a)).isDefined) do fields(a, b)
    // Two datatype classes the e-graph keeps apart, of one value: each class against every class of its
    // value before it, not the first only, which a third class with no disequality to either can be.
    val byValue = HashMap.empty[Term, ArrayBuffer[(Term, EClassId)]]
    val roots = HashSet.empty[EClassId]
    for t <- datatypeTerms do
      step()
      val root = eg.find(classes(t))
      if roots.add(root) then
        val same = byValue.getOrElseUpdate(modelValue(t), ArrayBuffer.empty)
        for (other, r) <- same.find((_, r) => eg.disequality(r, root).isDefined) do fields(other, t)
        same += ((t, root))
    (numeric.toList.map((a, b) => ArithmeticSplit(a, b, equalFirst = false)), missing.toList)

  /** Gives the equalities the last candidate missed their atoms, and tells
   *  whether there were any: the solver then runs its passes, which make the
   *  witnesses of the array equalities and the sorts of the new terms, and
   *  searches again. Like [[boundFields]], between searches, since a witness's
   *  reads need the array lemmas and a field may be a new term.
   */
  def equateMissing(): Boolean =
    val missing = missingEqualities
    missingEqualities = Nil
    for (a, b) <- missing do lit(Formula.Eq(a, b))
    missing.nonEmpty

  def solve(assumptions: ArrayBuffer[Lit], keepGoing: () => Boolean): cdclt.Solver.Result =
    liaSolver.forgetFailedSplits() // a check-sat's splits, not the last one's (see lia.Solver.splitOnDemand)
    liaSolver.keepGoing = keepGoing // the fuel: conflicts of the search, pivots, propagations and branches of LIA
    if anyInt || anyArray || anyNoted then
      registerShared()
      liaTheory.guideBoundsFromModel ||= numericApplications.exists(app => applications(app.fun).size > 1)
    lastModel = null
    val assumed = assumptions.toArray

    @scala.annotation.tailrec
    def search(): cdclt.Solver.Result =
      while sat.vars < atoms.length do sat.newVar() // `atoms` is the source of truth
      while deferredCursor < deferred.length do
        sat.defer(deferred(deferredCursor))
        deferredCursor += 1
      while clauseCursor < clauses.length do
        sat.addClause(clauses(clauseCursor), if proofs then origins(clauseCursor) else null)
        clauseCursor += 1
      var disagreements = List.empty[ArithmeticSplit]
      var stuck = false
      val result =
        try
          val candidate = sat.solve(assumed, keepGoing)
          candidate match
            case cdclt.Solver.Result.Sat(_) =>
              if sharedNumbers.nonEmpty then disagreements = arithmeticDisagreements()
              if disagreements.isEmpty then
                wantFields()
                if !fieldsWanted then
                  if modelApplications.nonEmpty || datatypeTerms.nonEmpty then
                    val (assemble, classValue) = buildModel()
                    val (numeric, more) = modelDisagreements(classValue)
                    disagreements = numeric
                    if numeric.isEmpty then
                      // An equality already with its atom cannot be missing: false, its arithmetic meaning or
                      // its witness keeps the two apart in the model. Found again, it would be searched for ever.
                      missingEqualities = more.filter((a, b) =>
                        !lits.contains(literalKey(Formula.Eq(a, b)))
                          || lemmaEqualities.contains(literalKey(Formula.Eq(a, b)))
                      )
                      if more.nonEmpty && missingEqualities.isEmpty then stuck = true
                      if produceModels && more.isEmpty then lastModel = assemble()
                  else if produceModels then lastModel = takeModel()
            case _ => ()
          candidate
        finally sat.unwind()
      if stuck then cdclt.Solver.Result.Unknown
      else if disagreements.isEmpty then result
      else if !keepGoing() then cdclt.Solver.Result.Unknown
      else
        // Add definitions between searches. Each atom has both meanings before
        // SAT assigns it. The decision phase leaves both polarities open.
        for ArithmeticSplit(a, b, equalFirst) <- disagreements do
          val next = atoms.length
          val eq = lit(Formula.Eq(a, b))
          require(eq.variable == next, s"candidate disagrees on an encoded equality: $a = $b")
          if equalFirst then preferEqual += eq.variable
        search()

    search()

  /** Builds the [[Model]] from the live engines: the value of every declared
   *  constant, and the graph of every declared first-order function from the
   *  applications the problem mentions. Uninterpreted sorts get an abstract
   *  element per e-class; a datatype class becomes its constructor term.
   */
  private def takeModel(): Model = buildModel()._1()

  /** The model, assembled when asked, and the value of a term by its e-class in
   *  it: the value the candidate gives the term, where the model's graph of a
   *  function gives two rows with one key a single result. The final check
   *  needs the values only.
   */
  private def buildModel(): (() => Model, Term => Term) =
    val real = liaSolver.realValues() // one δ for every real of the model, as the final check takes them
    val elements = HashMap.empty[(Sort, EClassId), Term] // sort and class to element
    val elementsOf = HashMap.empty[Sort, Int] // how many a sort has: counted over `elements`, a model was quadratic
    val classValues = HashMap.empty[EClassId, BigInt] // the simplex value of an Int class, via any of its terms
    val realClassValues = HashMap.empty[EClassId, lia.Rational]
    for (t, x) <- intVars do
      classes.get(t).foreach { c =>
        if sortOf(t) == Sort.Real then realClassValues(eg.find(c)) = real(x)
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
      elements.getOrElseUpdate(
        (sort, root), {
          val n = elementsOf.getOrElse(sort, 0)
          elementsOf(sort) = n + 1
          Term.Const(s"@$bare!$n")
        }
      )
    // A simplex value can appear in the model even if its term has no e-class.
    lazy val usedRealIntegers =
      val withoutClass = intVars.iterator.collect {
        case (t, x) if !classes.contains(t) && sortOf(t) == Sort.Real => real(x)
      }
      HashSet.from((realClassValues.valuesIterator ++ withoutClass).filter(_.isInteger).map(_.num))
    // Give free numeric classes distinct values. Start past the known integers and 0 (issue 26),
    // and skip the integers used by assigned real values (issue 179).
    var nextFresh = classValues.values.maxOption.getOrElse(BigInt(0)).max(BigInt(0)) + 1
    def freshInt(root: EClassId): BigInt =
      classValues.getOrElseUpdate(
        root, {
          while usedRealIntegers(nextFresh) do nextFresh += 1
          nextFresh += 1
          nextFresh - 1
        }
      )
    def freshReal(root: EClassId): lia.Rational =
      realClassValues.getOrElseUpdate(root, lia.Rational(freshInt(root)))
    val arrayValues = HashMap.empty[EClassId, Term] // an array's value per e-class (see arrayValue)
    val arraysBeingValued = scala.collection.mutable.HashSet.empty[EClassId] // against a cycle of stores or of fields
    // The arrays that stores connect, by e-class: a store's class and its base's are one group, and a
    // group's arrays take one default. Each array taking a default of its own, two store chains over
    // `A` and `B` that the problem equates were apart at every index no read observes (issue 189). The
    // read-over-write lemmas make the reads of a store and of its base agree at every index the
    // problem mentions, so with one default every store equation of a class holds everywhere.
    val storeGroup = HashMap.empty[EClassId, EClassId]
    def group(c: EClassId): EClassId =
      val parent = storeGroup.getOrElse(c, c)
      if parent == c then c
      else
        val top = group(parent)
        storeGroup(c) = top
        top
    for case s @ Term.App(Term.Const(n), List(base, _, _)) <- terms.iterator if Names.isStore(n) do
      val (a, b) = (group(eg.find(classes(s))), group(eg.find(classOf(base))))
      if a != b then storeGroup(a) = b
    val groupDefaults = HashMap.empty[EClassId, Term]
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
    // spare: a new number, a new element of an uninterpreted sort, an array of a new element, or a
    // datatype value around a new value of one of its fields. A sort met again inside its own value
    // takes the last value made for it, so each value is deeper than the one before. Without the
    // elements, a datatype whose values to spare are around one, `(c0_1 @U!3)`, gave two distinct
    // constants one value (issue 127).
    def freshOf(sort: Sort, seen: Set[Sort]): Option[Term] = sort match
      case Sort.Int => Some(Term.Num(freshInt(eg.newClass())))
      case Sort.Real => Some(Model.rationalTerm(freshReal(eg.newClass())))
      case Sort.Named(_) if datatypeOf(sort).isEmpty && sort != Encoder.unknown => Some(elementOf(sort, eg.newClass()))
      case _ if sort.arrow.isDefined => freshOf(applied(sort, 1), seen).map(Model.constArray(sort, _))
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
        case (Term.Linear(_, _), _) => // a linear argument or index: computed from its terms (issue 24)
          Model.rationalTerm(numericValue(t, real))
        case (_, s) if s.arrow.isDefined => // an array: the element of an array of arrays
          if classes.contains(t) then arrayValue(classOf(t), s)
          else Model.constArray(s, valueOfTerm(Term.Const("@default"), applied(s, 1)))
        case (_, Sort.Int | Sort.IntRange(_, _)) =>
          intVars.get(t).map(x => Term.Num(liaSolver.value(x)))
            .orElse(classes.get(t).map(c => Term.Num(freshInt(eg.find(c)))))
            .getOrElse(Term.Num(0))
        case (_, Sort.Real) =>
          intVars.get(t).map(x => Model.rationalTerm(real(x)))
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
      val v = numericValue(t, real)
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
          val rows = terms.iterator.collect {
            case app @ Term.App(fun, List(j)) if classes.get(fun).exists(c => eg.find(c) == root) =>
              (valueOfTerm(j, indexSort), valueOfTerm(app, elementSort))
          }.toMap
          // A class with a store in it is that store: the base array's value with the write, so that
          // `c = (store a i (select a i))` makes `c` the value of `a`, default and all, and not an
          // array of its own reads over a default of its own; the class's reads then agree with it
          // by the read-over-write lemmas. A class reached again while its base is valued keeps to
          // its reads.
          val written = terms.iterator.collectFirst {
            case s @ Term.App(Term.Const(n), List(base, i, v))
                if Names.isStore(n) && classes.get(s).exists(c => eg.find(c) == root)
                  && !arraysBeingValued(eg.find(classOf(base))) =>
              Model.store(arrayValue(classOf(base), sort), valueOfTerm(i, indexSort), valueOfTerm(v, elementSort))
          }
          arraysBeingValued -= root
          val start = written.getOrElse {
            Model.constArray(
              sort,
              groupDefaults.getOrElseUpdate(group(root), valueOfTerm(Term.Const("@default"), elementSort))
            )
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
    def assemble(): Model =
      val constants = Map.newBuilder[String, Term]
      val functions = Map.newBuilder[String, Model.Function]
      for
        (name, (argSorts, sort)) <- declarations
        if argSorts.isEmpty && sort.arrow.isDefined && !Names.isStore(name)
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
        if argSorts.nonEmpty && sort.arrow.isDefined && !Names.isStore(name)
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
      Model(constants.result(), functions.result(), datatypes)
    (() => assemble(), t => valueOfClass(classOf(t), sortOf(t), Set.empty))

/** Several theories over disjoint sets of atoms, asserted and checked in turn,
 *  without exchange of equalities between them; `owner(v)` is the theory of the
 *  atom of variable `v`, for explanations.
 */
private final class Theories(
    theories: List[Theory],
    owner: cdclt.Var => Theory,
    shared: cdclt.Var => Boolean,
    anyShared: () => Boolean,
    preferEqual: collection.Set[cdclt.Var]
) extends Theory:
  /** The theory that implied a literal: the atom of a shared equality belongs
   *  to both, and only the one that implied it can explain it. Only shared
   *  atoms are remembered; every other atom's owner is its implier.
   */
  private val implier = HashMap.empty[cdclt.Var, Theory]

  def assertLit(lit: Lit): Unit = theories.foreach(_.assertLit(lit))
  def propagate(): Theory.Result = combine(_.propagate())
  override def finalCheck(): Theory.Result = combine(_.finalCheck())
  def explain(lit: Lit): ArrayBuffer[Lit] =
    val theory = implier.getOrElse(lit.variable, owner(lit.variable))
    last = theory
    theory.explain(lit)

  /** The theory of the last conflict or explanation, for its certificate. */
  private var last: Theory = theories.head
  override def certificate(): AnyRef | Null = last.certificate()
  override def phase(v: cdclt.Var): Option[Boolean] =
    if preferEqual(v) then Some(true) else owner(v).phase(v)
  def push(): Unit = theories.foreach(_.push())
  def pop(): Unit = theories.foreach(_.pop())

  private def combine(check: Theory => Theory.Result): Theory.Result = boundary:
    // A split is passed on at once: its atom exists already, so it must get its variable before any
    // theory is asked again. What the other theories imply comes back when the decision is propagated.
    val results = theories.map(theory =>
      check(theory) match
        case Theory.Result.Ok(lits) => (theory, lits)
        case other =>
          last = theory
          break(other)
    )
    if anyShared() then
      for (theory, lits) <- results; l <- lits if shared(l.variable) do implier(l.variable) = theory
    results.filter(_._2.nonEmpty) match
      case Nil => Theory.ok
      case (_, lits) :: Nil => Theory.Result.Ok(lits) // one theory spoke: its buffer passes through
      case several => Theory.Result.Ok(several.foldLeft(ArrayBuffer.empty[Lit])(_ ++= _._2))
