package io.bovel.vik

import scala.collection.immutable.ArraySeq
import scala.collection.mutable.{ArrayBuffer, HashMap, HashSet}
import scala.util.boundary
import scala.util.boundary.break

import io.bovel.cdclt
import io.bovel.cdclt.{Lit, Theory}
import io.bovel.egraph.{App, EClassId, EGraph, NoRules}
import io.bovel.lia
import io.bovel.smtlib.{Datatype, Sorts}

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
  private[vik] val declarations = HashMap.empty[String, (List[String], String)]
  private[vik] val datatypes = ArrayBuffer.empty[Datatype]

  def declare(name: String, argSorts: List[String], sort: String): Unit =
    if encoder != null && encoder.nn.introducedName(name) then
      throw io.bovel.smtlib.Smt2Error(s"$name: a name the solver uses; pick another")
    // A name the live encoder knows at another sort — declared again after the pop of its level (issue
    // 40): the encoder's sort, class and variable for it are the old symbol's, so it is rebuilt.
    if encoder != null && encoded.get(name).exists(_ != (argSorts, sort)) then dirty = true
    declarations(name) = (argSorts, sort)
    if encoder != null then encoded(name) = (argSorts, sort)
    if name.startsWith("store!") || name.startsWith("const!") then anyStore = true

  /** The declarations the live encoder was given, as given: what a declaration
   *  after a pop is held against.
   */
  private val encoded = HashMap.empty[String, (List[String], String)]

  /** Forgets a declaration: its level is popped (issue 40). */
  def undeclare(name: String): Unit = declarations -= name

  def undeclare(datatype: Datatype): Unit =
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
   */
  def declare(datatype: Datatype): Unit =
    if encoder != null then dirty = true // its rules and exhaustiveness need an encoder that knows it
    datatypes += datatype
    for c <- datatype.constructors do
      declarations(c.name) = (c.selectors.map(_._2.text), datatype.name)
      declarations(c.tester) = (List(datatype.name), "Bool")
      for (selector, sort) <- c.selectors do declarations(selector) = (List(datatype.name), sort.text)

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
   */
  private def modelFailure(): Option[String] = model() match
    case None => Some("no model")
    case Some(m) =>
      val items = levels.iterator.flatten.zipWithIndex.map((f, i) => (s"assertion ${i + 1}", f)) ++
        named.iterator.flatten.map((name, f) => (s"assertion $name", f))
      items.flatMap { (what, f) =>
        val value =
          try if m.holds(f) then "true" else "false"
          catch case e: Exception => s"not evaluable (${e.getClass.getSimpleName}: ${e.getMessage})"
        Option.when(value != "true") {
          val text = Printer.print(f)
          s"$what ${if text.length > 200 then text.take(200) + "..." else text} is $value"
        }
      }.nextOption()

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
      val e = Encoder(declarations, datatypes.toList, () => anyStore, () => asked())
      encoder = e
      encoded.clear()
      encoded ++= declarations
      dirty = false
      selectors.clear()
      val constructors = datatypes.flatMap(_.constructors.map(_.name)).toSet
      if levels.length == 1 && simplify then
        // One level: the batch is the whole set, so the global simplification is sound to keep.
        val (simplified, gone) =
          Simplifier.simplify(levels.head.toList, constructors, named.head.map(_._2).toList, e.step)
        eliminated = gone
        for formula <- simplified do e.assert(formula, null)
      else
        eliminated = Map.empty
        for (level, i) <- levels.zipWithIndex do
          val selector = if i == 0 then null
          else
            selectors += e.newSelector(); selectors.last
          for formula <- level do e.assert(formula, selector)
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
    // registers a Boolean and emits nothing else is not done.
    var emitted = -1
    var decided = -1
    while (emitted != e.clauseCount || decided != e.booleanCount) && keepGoing() do
      emitted = e.clauseCount
      decided = e.booleanCount
      e.decideBooleans()
      e.assertExtensionality()
      e.applicationLemmas()
      e.arrayLemmas()
      e.assertExhaustiveness()
      e.shareIntegers()
    if emitted != e.clauseCount || decided != e.booleanCount then
      // Stopped short of the fixpoint: clauses are missing, and a search over the rest could answer
      // sat without them (issue 38).
      lastCore = Nil
      return Result.Unknown(Reason.Stopped)
    val assumed = ArrayBuffer.from(selectors)
    assumed ++= activations.map(_._2)
    e.solve(assumed, keepGoing) match
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
 *  classes and asserts, for every term of a datatype sort, that one of its
 *  testers holds (and, for a term of a finite datatype sort, does the same for
 *  its selector terms, recursively, so that the search is complete on finite
 *  sorts).
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
  val bitVector = """\(_ BitVec (\d+)\)""".r

  /** Thrown by [[Encoder.step]] when the solve's `keepGoing` says to stop. */
  object Stopped extends scala.util.control.ControlThrowable

private final class Encoder(
    declarations: HashMap[String, (List[String], String)],
    datatypes: List[Datatype],
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
  private val sorts = HashMap.empty[Term, String] // the sorts of terms, memoized: asked for every term, many times
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
  private val introduced = HashMap.empty[String, String]

  /** The sort of a term, from the declarations, a function sort for a function
   *  symbol (see [[Sorts]]); `?` when unknown.
   */
  private def sortOf(term: Term): String = sorts.getOrElseUpdate(
    term,
    term match
      case Term.Const(name) =>
        declarations.get(
          name
        ).map((args, sort) => Sorts.function(args, sort)).orElse(introduced.get(name)).getOrElse("?")
      case Term.App(fun, args) => Sorts.applied(sortOf(fun), args.length)
      case Term.Num(_) => "Int"
      case Term.Linear(terms, _) => if terms.exists((_, t) => sortOf(t) == "Real") then "Real" else "Int"
      case Term.Bool(_) => "Bool"
  )

  private val datatypeNames = datatypes.map(_.name).toSet

  /** The datatypes with finitely many values: no constructor field of an
   *  uninterpreted sort or of an infinite (e.g. recursive) datatype, computed
   *  as a least fixpoint.
   */
  private val finite: Set[String] =
    var known = Set("Bool")
    var changed = true
    while changed do
      val more = datatypes.filter(d =>
        !known(d.name) && d.constructors.forall(_.selectors.forall((_, s) => known(s.text)))
      ).map(_.name)
      changed = more.nonEmpty
      known ++= more
    known

  /** The terms known to be `Int`-sorted from their use in arithmetic (a summand
   *  of a combination, a side of `Le`), for undeclared constants.
   */
  private val intTerms = scala.collection.mutable.HashSet.empty[Term]

  private def noteInts(t: Term): Unit = t match
    case Term.Linear(terms, _) => terms.foreach((_, u) => intTerms += u)
    case Term.Num(_) => ()
    case _ => intTerms += t

  private def isInt(t: Term): Boolean = t match
    case Term.Num(_) | Term.Linear(_, _) => true
    case _ => sortOf(t) == "Int" || sortOf(t) == "Real" || intTerms(t)

  private def isFun(t: Term): Boolean = Sorts.arrow(sortOf(t)).isDefined

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

  def shareIntegers(): Unit = if anyInt || intTerms.nonEmpty || anyStore() then
    val pairs = ArrayBuffer.empty[(Term, Term)] // the pairs this call is first to meet
    val arrayPairs = ArrayBuffer.empty[(Term, Term)] // function-sorted pairs: their equality atom, for extensionality
    def pair(a: Term, b: Term): Unit =
      step()
      if a != b && isInt(a) && isInt(b) && Sorts.arrow(sortOf(a)).isEmpty && Sorts.arrow(sortOf(b)).isEmpty
        && !sharedPairs((b, a)) && sharedPairs.add((a, b))
      then pairs += ((a, b))
      else if a != b && Sorts.arrow(sortOf(a)).isDefined && Sorts.arrow(sortOf(b)).isDefined
        && !sharedPairs((b, a)) && sharedPairs.add((a, b))
      then arrayPairs += ((a, b))
    val applications = classes.keys.collect { case a: Term.App => a }.toList.groupBy(_.fun)
    // An application with an integer or an array, as its value or among its arguments, can share; the
    // others have nothing to. Two arrays under the same function meet here too, whatever the function
    // gives: equal by extensionality, their applications are equal by congruence (issue 39).
    def shares(a: Term.App): Boolean = isInt(a) || isFun(a) || a.args.exists(x => isInt(x) || isFun(x))
    for (_, group) <- applications do
      val relevant = group.filter(shares)
      for (a, i) <- relevant.zipWithIndex; b <- relevant.drop(i + 1) do
        pair(a, b)
        for (x, y) <- a.args.zip(b.args) do pair(x, y)
    // Applications of different function terms meet too when the functions themselves can be equated —
    // two arrays, or a store and the array it may equal: group by the function's sort instead of the
    // function.
    // Only functions the search may actually equate: the sides of a function equality (recorded or
    // shared), and store applications. Pairing every same-sorted application would be quadratic on
    // ordinary uninterpreted functions.
    val equatableFuns = scala.collection.mutable.HashSet.empty[Term]
    for case Formula.Eq(f, g) <- functionEqualities do
      equatableFuns += f
      equatableFuns += g
    val byFunctionSort = classes.keys.collect {
      case a: Term.App
          if Sorts.arrow(sortOf(a.fun)).isDefined
            && (equatableFuns(a.fun) ||
              (a.fun match
                case Term.App(Term.Const(n), _) => n.startsWith("store!") || n.startsWith("const!")
                case _ => false)) =>
        a
    }.toList.groupBy(a => (sortOf(a.fun), a.args.length))
    for (_, group) <- byFunctionSort do
      val relevant = group.filter(shares)
      for (a, i) <- relevant.zipWithIndex; b <- relevant.drop(i + 1) if a.fun != b.fun do
        pair(a, b)
        for (x, y) <- a.args.zip(b.args) do pair(x, y)
    // Not the equalities of the application lemmas: paired, they would be the problem's, each with a
    // witness, the map and the arrays read there, and the integers there shared in turn.
    for case eq @ Formula.Eq(a, b) <- lits.keys if !lemmaEqualities(eq) do pair(a, b)
    // A selector's applications meet the arguments of its constructor at its position (the selector rule).
    // An arithmetic field, integer or real: a real one shared only through the e-graph left the
    // simplex without its equalities (issue 18).
    for
      d <- datatypes; c <- d.constructors; ((selector, sort), i) <- c.selectors.zipWithIndex
      if sort.text == "Int" || sort.text == "Real"
    do
      for s <- applications.getOrElse(Term.Const(selector), Nil); k <- applications.getOrElse(Term.Const(c.name), Nil)
      do
        if k.args.length > i then pair(s, k.args(i))
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
    // the entailed disjunction of the classic Stump-Barrett-Dill-Levitt example.
    // An equality an application lemma made already stays the lemma's, without a witness: only the
    // problem stating it makes it one of its own (see `lit`).
    for (a, b) <- arrayPairs do
      val eq = Formula.Eq(a, b)
      lits.getOrElseUpdate(eq, encode(eq))

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
      val stores = classes.keys.collect {
        case s @ Term.App(Term.Const(name), List(_, _, _)) if name.startsWith("store!") => s
        case c @ Term.App(Term.Const(name), List(_)) if name.startsWith("const!") => c
      }.toList
      val apps = if stores.isEmpty then Nil else classes.keys.collect { case a: Term.App => a }.toList
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
    a != s && a.fun != s && a.args.length == 1 && sortOf(a.fun) == sortOf(s)

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

  /** A witness index's name, `ext!N`, past the script's symbols: a script
   *  constant `ext!0` was the witness, and a later declaration of a witness's
   *  name is refused by [[Solver.declare]].
   */
  private var witnesses = 0
  private def witnessName(): String =
    var name = s"ext!$witnesses"
    while declarations.contains(name) do
      witnesses += 1
      name = s"ext!$witnesses"
    witnesses += 1
    name

  def introducedName(name: String): Boolean = introduced.contains(name)

  def assertExtensionality(): Unit = if anyFunctionEquality then
    val done = extensionalityDone // across solves: one witness pair per equality, ever
    var more = true
    while more do
      more = false
      for case eq @ Formula.Eq(f, g) <- functionEqualities.toList if !done(eq) do
        done += eq
        if !assertedEqualities(eq) then
          Sorts.arrow(sortOf(f)).orElse(Sorts.arrow(sortOf(g))) match
            case Some((params, _)) =>
              more = true
              val witnesses = params.map { sort =>
                val name = witnessName()
                sort match
                  case Encoder.bitVector(width) =>
                    // The lowering reads a bit-vector as an integer in its range; so is the witness
                    // index, or two arrays over `(_ BitVec 1)` agreeing at both indices could still
                    // differ at it (issue 20).
                    introduced(name) = "Int"
                    val w = Term.Const(name)
                    clauses += Array(lit(Formula.Le(Term.Num(0), w)))
                    clauses += Array(lit(Formula.Le(w, Term.Num(BigInt(2).pow(width.nn.toInt) - 1))))
                    w
                  case _ =>
                    introduced(name) = sort
                    Term.Const(name)
              }
              clauses += Array(lit(eq), lit(Formula.Eq(applyAll(f, witnesses), applyAll(g, witnesses))).neg)
            case _ => ()

  /** Asserts, for every term of a datatype sort seen so far, that one of its
   *  testers holds; for a term of a finite sort, also for its selector terms,
   *  recursively (see the class documentation).
   */
  private val exhaustivenessSeen = scala.collection.mutable.HashSet.empty[Term]

  def assertExhaustiveness(): Unit =
    if datatypes.nonEmpty then
      val seen = exhaustivenessSeen // across solves: one tester disjunction per term
      val todo = ArrayBuffer.from(classes.keys.filter(t => datatypeNames(sortOf(t))))
      while todo.nonEmpty do
        val t = todo.remove(todo.length - 1)
        if seen.add(t) then
          val datatype = datatypes.find(_.name == sortOf(t)).get
          assert(
            Formula.Or(datatype.constructors.map(c => Formula.Pred(Term.App(Term.Const(c.tester), List(t))))),
            null
          )
          if finite(datatype.name) then
            for c <- datatype.constructors; (selector, sort) <- c.selectors if datatypeNames(sort.text) do
              todo += Term.App(Term.Const(selector), List(t))

  private val liaSolver = lia.Solver()
  private val intVars = HashMap.empty[Term, lia.Var] // `Int`-sorted constants and applications
  private val slacks = HashMap.empty[List[(BigInt, Term)], lia.Var] // linear combinations of them

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
    if sortOf(term) == "Bool" && booleanClasses.add(classOf(term)) then booleans += term

  /** Whether some term is an integer, or some equality is between functions
   *  (arrays): the passes over all the terms of [[shareIntegers]] and
   *  [[assertExtensionality]] are skipped otherwise (many queries are small).
   */
  private var anyInt = false
  private var anyFunctionEquality = false

  def classOf(term: Term): EClassId = classes.getOrElseUpdate(
    term, {
      sortOf(term) match
        case "Int" | "Real" => anyInt = true
        case _ => ()
      classOfNew(term)
    }
  )

  private def classOfNew(term: Term): EClassId =
    term match
      case Term.Const(_) => eg.newClass()
      case Term.App(fun, args) =>
        args.foreach(boolean)
        eg.add(App(classOf(fun), ArraySeq.from(args.map(classOf))))
      case Term.Num(_) | Term.Linear(_, _) => eg.newClass() // a leaf for the e-graph, a variable for LIA (shared)
      case Term.Bool(_) => eg.newClass() // a leaf, tied to its formula by `Pred` (see `encode`)

  /** A Boolean-sorted term that is an argument or a side of an equality is true
   *  or false: its atom `t = true` is decided by the SAT solver, and the UF
   *  theory merges `t` with `true` or with `false` accordingly — so that two
   *  Boolean arguments with the same truth value are equal (congruence), and a
   *  Boolean term's class has a truth value. The atom of a [[Term.Bool]] holds
   *  iff its formula does. A predicate application only used as an atom needs
   *  neither: its disequality with `true` is enough.
   */
  /** The array axioms, as lemmas over the finite product of the `store!`
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
    case Term.App(Term.Const(n), _) if n.startsWith("store!") => Term.App(array, List(index))
    case _ => Term.App(array, List(index))

  /** An index of `sort` no store writes at, for the sorts indexing a constant
   *  array: reading there carries the value of a constant array through the
   *  stores over it, so that `((as const A) 0)` with finitely many writes is
   *  not `((as const A) 1)`. There is one when the sort has more values than a
   *  script has stores; a constant array over another sort is refused.
   */
  private val beyondIndices = scala.collection.mutable.HashMap.empty[String, Term]
  private val beyondDone = scala.collection.mutable.HashSet.empty[(Term, Term)]

  private def beyond(sort: String): Term = beyondIndices.getOrElseUpdate(
    sort, {
      val name = witnessName()
      sort match
        case Encoder.bitVector(width) if width.nn.toInt >= 16 =>
          introduced(name) = "Int"
          val w = Term.Const(name)
          clauses += Array(lit(Formula.Le(Term.Num(0), w)))
          clauses += Array(lit(Formula.Le(w, Term.Num(BigInt(2).pow(width.nn.toInt) - 1))))
          w
        case Encoder.bitVector(_) => throw io.bovel.smtlib.Smt2Error(s"a constant array over the small sort $sort")
        case _ if finite(sort) => throw io.bovel.smtlib.Smt2Error(s"a constant array over the finite sort $sort")
        case _ =>
          introduced(name) = sort
          Term.Const(name)
    }
  )

  private val arrayWritesDone = scala.collection.mutable.HashSet.empty[Term]
  private val arrayReadsDone = scala.collection.mutable.HashSet.empty[(Term, Term)]

  def arrayLemmas(): Unit = if anyStore() then
    val stores = classes.keys.collect {
      case s @ Term.App(Term.Const(name), List(_, _, _)) if name.startsWith("store!") => s
    }.toList
    val indices = scala.collection.mutable.HashMap.empty[String, scala.collection.mutable.LinkedHashSet[Term]]
    def index(sort: String, j: Term): Unit =
      indices.getOrElseUpdate(sort, scala.collection.mutable.LinkedHashSet.empty) += j
    for a <- classes.keys do
      a match
        case Term.App(f, List(j)) if Sorts.arrow(sortOf(f)).isDefined => index(sortOf(f), j)
        case _ => ()
    for s <- stores do index(sortOf(s), s.args(1))
    // The index beyond the writes (see [[beyond]]) is none of the written ones.
    for s <- stores do
      val indexSort = Sorts.arrow(sortOf(s)).get._1.head
      for w <- beyondIndices.get(indexSort) do
        if beyondDone.add((w, s.args(1))) then clauses += Array(lit(equalAt(indexSort, w, s.args(1))).neg)
    // A constant array holds its value at every index of its sort: `const(d)(j) = d`.
    for case c @ Term.App(Term.Const(name), List(d)) <- classes.keys.toList if name.startsWith("const!") do
      val sort = sortOf(c)
      val elementSort = Sorts.applied(sort, 1)
      index(sort, beyond(Sorts.arrow(sort).get._1.head))
      for j <- indices.getOrElse(sort, Nil).toList do
        step()
        if arrayReadsDone.add((c, j)) then clauses += Array(lit(equalAt(elementSort, selectTerm(c, j), d)))
    def equalAt(sort: String, l: Term, r: Term): Formula =
      if sort == "Int" || sort == "Real" then Formula.IntEq(l, r) else Formula.Eq(l, r)
    for case s @ Term.App(_, List(a, i, v)) <- stores do
      val sort = sortOf(s)
      val indexSort = Sorts.arrow(sort).get._1.head
      val elementSort = Sorts.applied(sort, 1) // an array, for an array of arrays
      if arrayWritesDone.add(s) then clauses += Array(lit(equalAt(elementSort, selectTerm(s, i), v)))
      for j <- indices.getOrElse(sort, Nil) do
        step()
        if j != i && arrayReadsDone.add((s, j)) then
          clauses += Array(
            lit(equalAt(indexSort, i, j)),
            lit(equalAt(elementSort, selectTerm(s, j), selectTerm(a, j)))
          )

  def booleanCount: Int = booleans.length

  def decideBooleans(): Unit =
    var i = 0
    while i < booleans.length do
      lit(Formula.Pred(booleans(i)))
      i += 1

  private def atom(t: EClassId, u: EClassId): Lit =
    atoms += ((t, u))
    liaAtoms += null
    Lit(atoms.length - 1)

  private def bound(x: lia.Var, c: BigInt, strict: Boolean): Lit =
    atoms += null
    liaAtoms += LiaTheory.Atom.Bound(x, c, strict)
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
    intVars.getOrElseUpdate(term, liaSolver.newVar(integer = sortOf(term) != "Real"))

  /** The LIA variable standing for a linear combination of `Int` terms. */
  private def slack(terms: List[(BigInt, Term)]): lia.Var =
    slacks.getOrElseUpdate(
      terms,
      liaSolver.newSlack(terms.map((a, t) => (a, intVar(t))), integer = !terms.exists((_, t) => sortOf(t) == "Real"))
    )

  /** The literal standing for `formula`, defining it by clauses if needed. */
  private def lit(formula: Formula): Lit =
    // An equality first encoded for an application lemma, met again in a formula of the problem,
    // is one of the problem's from then on: its negation needs a witness like any other.
    if recordFunctionEqualities && lemmaEqualities.nonEmpty && lemmaEqualities.remove(formula) then
      functionEqualities += formula
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
          if sortOf(lhs).startsWith("(->") || sortOf(rhs).startsWith("(->") then
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
    val l = lit(formula)
    clauses += (if under == null then Array(l) else Array(under.nn.neg, l))

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

  private val ufTheory = UfTheory(eg, atoms, trueTerm, falseTerm, booleanClasses)
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
    while clauseCursor < clauses.length do
      sat.addClause(clauses(clauseCursor))
      clauseCursor += 1
    lastModel = null
    val result = sat.solve(assumptions.toArray, keepGoing)
    result match
      case cdclt.Solver.Result.Sat(_) => if produceModels then lastModel = takeModel()
      case _ => ()
    sat.unwind() // the next assert must find the engines at level 0, not on the trail of this search
    result

  /** Builds the [[Model]] from the live engines: the value of every declared
   *  constant, and the graph of every declared first-order function from the
   *  applications the problem mentions. Uninterpreted sorts get an abstract
   *  element per e-class; a datatype class becomes its constructor term.
   */
  private def takeModel(): Model =
    val elements = HashMap.empty[(String, EClassId), Term] // sort and class to element
    val classValues = HashMap.empty[EClassId, BigInt] // the simplex value of an Int class, via any of its terms
    val realClassValues = HashMap.empty[EClassId, lia.Rational]
    for (t, x) <- intVars do
      classes.get(t).foreach { c =>
        if sortOf(t) == "Real" then realClassValues(eg.find(c)) = liaSolver.realValue(x)
        else classValues(eg.find(c)) = liaSolver.value(x)
      }
    // A numeral values its class too: a term equated with one by congruence alone (a constructor's
    // field, say) has no variable of its own.
    for case (n @ Term.Num(v), c) <- classes do
      classValues(eg.find(c)) = v
      realClassValues(eg.find(c)) = lia.Rational(v)
    def elementOf(sort: String, cls: EClassId): Term =
      val root = eg.find(cls)
      // The name is bare, `@a b!0` for the sort `|a b|`: the printer adds the bars a name needs.
      val bare = sort.stripPrefix("|").stripSuffix("|")
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
    val arraysBeingValued = scala.collection.mutable.HashSet.empty[EClassId] // against a cycle of stores
    // The value of a datatype class with no constructor node: none of its testers holds, so none is
    // asserted of it, and the value is built — a constructor whose tester is not false, its fields
    // from the selectors' classes when the problem has them and fresh values otherwise — one that
    // differs from every other such class's, since the e-graph may keep them apart (issue 26).
    val builtValues = HashMap.empty[EClassId, Term]
    def testerOf(root: EClassId, tester: String): Option[Boolean] =
      classes.collectFirst {
        case (Term.App(Term.Const(t), List(u)), c) if t == tester && classes.get(u).exists(x => eg.find(x) == root) =>
          eg.find(c)
      }.map(c => c == eg.find(trueTerm))
    def selectorOf(root: EClassId, selector: String): Option[EClassId] =
      classes.collectFirst {
        case (Term.App(Term.Const(s), List(u)), c) if s == selector && classes.get(u).exists(x => eg.find(x) == root) =>
          c
      }
    def defaultOf(sort: String, seen: Set[String]): Term = datatypes.find(_.name == sort) match
      case Some(d) if !seen(sort) =>
        val c = d.constructors.find(_.selectors.isEmpty).getOrElse(d.constructors.head)
        val args = c.selectors.map((_, s) => defaultOf(s.text, seen + sort))
        if args.isEmpty then Term.Const(c.name) else Term.App(Term.Const(c.name), args)
      case Some(_) => elementOf(sort, eg.newClass())
      case None => valueOfTerm(Term.Const("@default"), sort)
    def builtValue(datatype: Datatype, root: EClassId, seen: Set[EClassId]): Term =
      builtValues.getOrElseUpdate(
        root, {
          val candidates = datatype.constructors.filter(c => !testerOf(root, c.tester).contains(false))
          val numeric = (s: String) => s == "Int" || s == "Real"
          // A constructor with a number among its fields tells classes apart by that field; an
          // enumeration by taking its constructors in turn.
          val c = candidates.find(_.selectors.exists((_, s) => numeric(s.text))).getOrElse {
            val nullary = candidates.filter(_.selectors.isEmpty)
            if nullary.nonEmpty then nullary(builtValues.size % nullary.length)
            else candidates.headOption.getOrElse(datatype.constructors.head)
          }
          val args = c.selectors.map { (selector, s) =>
            selectorOf(root, selector) match
              case Some(field) => valueOfClass(field, s.text, seen + root)
              case None if s.text == "Int" => Term.Num(freshInt(eg.newClass()))
              case None if s.text == "Real" => Model.rationalTerm(freshReal(eg.newClass()))
              case None => defaultOf(s.text, Set.empty)
          }
          if args.isEmpty then Term.Const(c.name) else Term.App(Term.Const(c.name), args)
        }
      )
    def valueOfClass(cls: EClassId, sort: String, seen: Set[EClassId]): Term =
      datatypes.find(_.name == sort) match
        case Some(datatype) =>
          val node = adt.map(_.node(eg, cls)).orNull
          if seen(eg.find(cls)) then elementOf(sort, cls) // a cycle, which the rules never let through
          else if node == null then builtValue(datatype, eg.find(cls), seen)
          else
            val constructor = datatype.constructors.find(c => eg.find(classes(Term.Const(c.name))) == eg.find(node.fun))
            constructor match
              case Some(c) =>
                val args = node.args.toList.zip(c.selectors).map((a, s) =>
                  valueOfClass(a, s._2.text, seen + eg.find(cls))
                )
                if args.isEmpty then Term.Const(c.name) else Term.App(Term.Const(c.name), args)
              case None => builtValue(datatype, eg.find(cls), seen)
        case None =>
          sort match
            case "Int" => Term.Num(freshInt(eg.find(cls)))
            case "Real" => Model.rationalTerm(freshReal(eg.find(cls)))
            case "Bool" => Term.boolean(if eg.find(cls) == eg.find(trueTerm) then Formula.True else Formula.False)
            case _ => elementOf(sort, cls)
    def valueOfTerm(t: Term, sort: String): Term =
      (t, sort) match
        case (Term.Num(_), _) => t // a literal argument of an application
        case (Term.Linear(terms, c), _) => // a linear argument or index: computed from its terms (issue 24)
          Model.rationalTerm(terms.foldLeft(lia.Rational(c)) { case (sum, (a, u)) =>
            sum + lia.Rational(a) * asRational(valueOfTerm(u, sortOf(u)))
          })
        case (_, s) if Sorts.arrow(s).isDefined => // an array: the element of an array of arrays
          if classes.contains(t) then arrayValue(t, s)
          else Model.constArray(Sorts.array(s), valueOfTerm(Term.Const("@default"), Sorts.applied(s, 1)))
        case (_, "Int") =>
          intVars.get(t).map(x => Term.Num(liaSolver.value(x)))
            .orElse(classes.get(t).map(c => Term.Num(freshInt(eg.find(c)))))
            .getOrElse(Term.Num(0))
        case (_, "Real") =>
          intVars.get(t).map(x => Model.rationalTerm(liaSolver.realValue(x)))
            .orElse(classes.get(t).map(c => Model.rationalTerm(freshReal(eg.find(c)))))
            .getOrElse(Term.Num(0))
        case _ =>
          classes.get(t) match
            case Some(cls) => valueOfClass(cls, sort, Set.empty)
            case None =>
              if sort == "Bool" then Term.boolean(Formula.False)
              else
                datatypes.find(_.name == sort) match
                  case Some(d) => builtValue(d, eg.newClass(), Set.empty) // never reached the e-graph: free
                  case None => elementOf(sort, eg.newClass())
    // An array's value, per e-class: its default and the indices its class was read at — its own
    // selects, the ones of every array equal to it, the write of a store it equals.
    def arrayValue(array: Term, sort: String): Term =
      val root = eg.find(classOf(array))
      arrayValues.getOrElseUpdate(
        root, {
          val indexSort = Sorts.arrow(sort).get._1.head
          val elementSort = Sorts.applied(sort, 1) // itself an array, for an array of arrays
          val rows = classes.keys.collect {
            case app @ Term.App(fun, List(j)) if classes.get(fun).exists(c => eg.find(c) == root) =>
              (valueOfTerm(j, indexSort), valueOfTerm(app, elementSort))
          }.toMap
          // A class with a store in it is that store: the base array's value with the write, so that
          // `c = (store a i (select a i))` makes `c` the value of `a`, default and all, and not an
          // array of its own reads over a default of its own; the class's reads then agree with it
          // by the read-over-write lemmas. A class reached again while its base is valued keeps to
          // its reads.
          arraysBeingValued += root
          val written = classes.keys.collectFirst {
            case s @ Term.App(Term.Const(n), List(base, i, v))
                if n.startsWith("store!") && classes.get(s).exists(c => eg.find(c) == root)
                  && !arraysBeingValued(eg.find(classOf(base))) =>
              Model.store(arrayValue(base, sort), valueOfTerm(i, indexSort), valueOfTerm(v, elementSort))
          }
          arraysBeingValued -= root
          // A class with a constant array in it holds that array's value everywhere.
          val constant = classes.keys.collectFirst {
            case c @ Term.App(Term.Const(n), List(d))
                if n.startsWith("const!") && classes.get(c).exists(k => eg.find(k) == root) =>
              Model.constArray(Sorts.array(sort), valueOfTerm(d, elementSort))
          }
          val start = written.orElse(constant).getOrElse {
            Model.constArray(Sorts.array(sort), valueOfTerm(Term.Const("@default"), elementSort))
          }
          rows.toList.sortBy(_._1.toString).foldLeft(start) { case (acc, (i, v)) => Model.store(acc, i, v) }
        }
      )
    val constants = Map.newBuilder[String, Term]
    val functions = Map.newBuilder[String, Model.Function]
    for
      (name, (argSorts, sort)) <- declarations
      if argSorts.isEmpty && Sorts.arrow(sort).isDefined && !name.startsWith("store!") && !name.startsWith("const!")
    do
      // An array the assertions never read or wrote holds a default everywhere: a value all the same,
      // where `(select arr i)` was printed as itself (issue 48).
      constants += name -> (
        if classes.contains(Term.Const(name)) then arrayValue(Term.Const(name), sort)
        else Model.constArray(Sorts.array(sort), valueOfTerm(Term.Const("@default"), Sorts.applied(sort, 1)))
      )
    // A function into arrays: its graph, an array value per application the problem mentions (issue 27).
    for
      (name, (argSorts, sort)) <- declarations
      if argSorts.nonEmpty && Sorts.arrow(sort).isDefined && !name.startsWith("store!") && !name.startsWith("const!")
    do
      val rows = classes.keys.collect {
        case a @ Term.App(Term.Const(n), args) if n == name && args.length == argSorts.length =>
          (args.zip(argSorts).map(valueOfTerm), arrayValue(a, sort))
      }.toList
      val default = Model.constArray(Sorts.array(sort), valueOfTerm(Term.Const("@default"), Sorts.applied(sort, 1)))
      functions += name -> Model.Function(argSorts, Sorts.array(sort), rows, default)
    for (name, (argSorts, sort)) <- declarations if !sort.startsWith("(->") do
      if argSorts.isEmpty then constants += name -> valueOfTerm(Term.Const(name), sort)
      else
        val rows = classes.keys.collect {
          case a @ Term.App(Term.Const(n), args) if n == name && args.length == argSorts.length =>
            (args.zip(argSorts).map(valueOfTerm), valueOfTerm(a, sort))
        }.toList
        val default = rows.headOption.map(_._2).getOrElse(valueOfTerm(Term.Const("@default"), sort))
        functions += name -> Model.Function(argSorts, sort, rows, default)
    Model(constants.result(), functions.result(), datatypes)

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
