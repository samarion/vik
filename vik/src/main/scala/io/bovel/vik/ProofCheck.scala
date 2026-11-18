package io.bovel.vik

import scala.collection.mutable.ArrayBuffer
import scala.util.boundary
import scala.util.boundary.break

import io.bovel.cdclt
import io.bovel.cdclt.Lit
import io.bovel.egraph.{App, EClassId, EConflict, EqProof}
import io.bovel.lia

/** Checks the lemmas of the UF theory against their certificates (see
 *  [[UfTheory.Certificate]]), reading the terms off the applications the
 *  certificate recorded for its classes, never the e-graph's union-find: each
 *  step of a proof is checked on its own, from the literals of the lemma.
 *
 *  `atoms(v)` is the UF atom `t = u` of variable `v`; `trueLit` is the literal
 *  of `True`, the reason of the disequality `true != false`; `constructors`
 *  maps the class of each constructor symbol to its selectors' classes,
 *  `testers` the class of each tester to its constructor's class.
 */
final class UfLemmas(
    atoms: ArrayBuffer[(EClassId, EClassId) | Null],
    trueClass: EClassId,
    falseClass: EClassId,
    trueLit: Lit,
    constructors: Map[EClassId, Seq[EClassId]],
    testers: Map[EClassId, EClassId]
):
  /** Whether `certificate` shows that `clause` holds: `None` if so, what is
   *  wrong otherwise.
   */
  def check(clause: Array[Lit], certified: UfTheory.Certified): Option[String] = boundary:
    val certificate = certified.certificate
    object eg:
      def app(x: EClassId): App | Null = certified.nodes.getOrElse(x, null)
    def fail(msg: String): Nothing = break(Some(msg))
    // The hypotheses: the negations of the clause's literals.
    val hyps = clause.iterator.map(_.neg.index).toSet
    def same(p: (EClassId, EClassId), q: (EClassId, EClassId)): Boolean = p == q || p == q.swap

    def asserted(a: EClassId, b: EClassId, reason: Int): Unit =
      if !hyps(reason) then fail(s"the reason $reason is not a hypothesis")
      val lit = Lit.fromIndex(reason)
      val atom = if lit.variable < atoms.length then atoms(lit.variable) else null
      if atom == null then fail(s"the reason $reason has no atom")
      if lit.positive then
        if !same((a, b), atom) then fail(s"$a = $b is not the atom of $reason")
      else if !(atom._2 == trueClass && same((a, b), (atom._1, falseClass))) then
        fail(s"$a = $b does not follow from the negation of $reason")

    /** The head of the class `x`'s term when it is a constructor: its class and
     *  its arguments.
     */
    def constructorOf(x: EClassId): Option[(EClassId, Seq[EClassId])] =
      if constructors.get(x).exists(_.isEmpty) then Some((x, Nil))
      else
        val app = eg.app(x)
        if app != null && constructors.contains(app.fun) then Some((app.fun, app.args)) else None

    /** Whether `a = b` follows from the premises by a rule of the datatypes. */
    def rule(a: EClassId, b: EClassId, premises: Seq[(EClassId, EClassId)]): Boolean =
      def oriented(a: EClassId, b: EClassId): Boolean =
        val app = eg.app(a)
        premises match
          case Seq((p, q)) =>
            // A selector of a constructor node: `s_i(t) = x_i` when `t = C(x_1, ..., x_n)`.
            val selector = app != null && app.args.length == 1 && app.args(0) == p &&
              constructorOf(q).exists((c, args) =>
                constructors(c).indexOf(app.fun) match
                  case -1 => false
                  case i => args(i) == b
              )
            // A tester of a constructor node: `is_C(t) = true` when `t = C(...)`.
            val tester = app != null && app.args.length == 1 && app.args(0) == p && b == trueClass &&
              testers.get(app.fun).exists(c => constructorOf(q).exists(_._1 == c))
            // Injectivity: `x_i = y_i` when `C(x_1, ...) = C(y_1, ...)`.
            val injective = (constructorOf(p), constructorOf(q)) match
              case (Some((c, xs)), Some((d, ys))) => c == d && xs.indices.exists(i => xs(i) == a && ys(i) == b)
              case _ => false
            // Expansion: `t = C(s_1(t), ..., s_n(t))` when `is_C(t) = true`.
            val expansion = q == trueClass && {
              val test = eg.app(p)
              test != null && test.args.length == 1 && test.args(0) == a && testers.get(test.fun).exists { c =>
                val selectors = constructors(c)
                if selectors.isEmpty then b == c
                else
                  constructorOf(b).exists((d, fields) =>
                    d == c && fields.indices.forall { i =>
                      val field = eg.app(fields(i))
                      field != null && field.fun == selectors(i) && field.args == Seq(a)
                    }
                  )
              }
            }
            selector || tester || injective || expansion
          case _ => false
      oriented(a, b) || oriented(b, a)

    /** Checks `p` and returns the equality it proves. */
    def proves(p: EqProof): (EClassId, EClassId) = p match
      case EqProof.Refl(a) => (a, a)
      case EqProof.Given(a, b, reason) =>
        asserted(a, b, reason)
        (a, b)
      case EqProof.Symm(q) => proves(q).swap
      case EqProof.Trans(q, r) =>
        val (a, b) = proves(q)
        val (c, d) = proves(r)
        if b != c then fail(s"transitivity through $b and $c")
        (a, d)
      case EqProof.Cong(a, b, fun, args) =>
        val (l, r) = (eg.app(a), eg.app(b))
        if l == null || r == null || l.args.length != args.length || r.args.length != args.length then
          fail(s"congruence of $a and $b, not applications of the same arity")
        if proves(fun) != (l.fun, r.fun) then fail(s"congruence of $a and $b: not their functions")
        for i <- args.indices do
          if proves(args(i)) != (l.args(i), r.args(i)) then fail(s"congruence of $a and $b: not their argument $i")
        (a, b)
      case EqProof.Rule(a, b, premises) =>
        val holding = premises.map(proves)
        if !rule(a, b, holding) then fail(s"$a = $b by no rule from ${holding.mkString(", ")}")
        (a, b)

    /** Checks that `reason`, a hypothesis, makes `a` and `b` distinct. */
    def apart(a: EClassId, b: EClassId, reason: Int): Unit =
      if !hyps(reason) then fail(s"the reason $reason is not a hypothesis")
      val lit = Lit.fromIndex(reason)
      if lit == trueLit then
        if !same((a, b), (trueClass, falseClass)) then fail(s"$a != $b is not true != false")
      else
        val atom = if lit.variable < atoms.length then atoms(lit.variable) else null
        if lit.positive || atom == null || !same((a, b), atom) then fail(s"$a != $b is not the negation of $reason")

    /** Checks that the equalities `holding` contradict the datatypes. */
    def contradiction(holding: Seq[(EClassId, EClassId)]): Unit =
      val clash = holding match
        // Two constructors.
        case Seq((p, q)) =>
          (constructorOf(p), constructorOf(q)) match
            case (Some((c, _)), Some((d, _))) => c != d
            case _ => false
        // A tester true of a term with another constructor.
        case Seq((test, t), (x, n)) if t == trueClass =>
          val app = eg.app(test)
          app != null && app.args == Seq(x) && testers.get(app.fun).exists(c => constructorOf(n).exists(_._1 != c))
        case _ => false
      // A cycle: each argument of a constructor node is the next node, the last's the first.
      val cycle = holding.nonEmpty && holding.indices.forall { i =>
        val (arg, _) = holding(i)
        val (_, node) = holding((i + holding.length - 1) % holding.length)
        constructorOf(node).exists(_._2.contains(arg))
      }
      if !clash && !cycle then fail(s"no contradiction in ${holding.mkString(", ")}")

    certificate match
      case UfTheory.Certificate.Conflict(EConflict.Disequal(p, reason)) =>
        val (a, b) = proves(p)
        apart(a, b, reason)
      case UfTheory.Certificate.Conflict(EConflict.Contradiction(proofs)) =>
        contradiction(proofs.map(proves))
      case UfTheory.Certificate.Equal(p) =>
        val l = clause(0)
        val atom = atoms(l.variable)
        if !l.positive || atom == null || !same(proves(p), atom) then fail("not a proof of the implied atom")
      case UfTheory.Certificate.Apart(left, right, reason) =>
        val l = clause(0)
        val atom = atoms(l.variable)
        val (t, s) = proves(left)
        val (u, s2) = proves(right)
        if l.positive || atom == null || (t, u) != atom then fail("not the sides of the implied atom")
        apart(s, s2, reason)
    None

/** Checks the lemmas of the LIA theory against their certificates (see
 *  `lia.Certificate`): each hypothesis must be the negation of a literal of the
 *  lemma, asserting the bound of that literal's atom (`atoms(v)`, see
 *  [[LiaTheory]]).
 */
final class LiaLemmas(solver: lia.Solver, atoms: ArrayBuffer[LiaTheory.Atom | Null]):
  private val checker = lia.Certificate.Checker(
    solver.form,
    solver.isInteger,
    h =>
      val lit = Lit.fromIndex(h.reason)
      val atom = if lit.variable < atoms.length then atoms(lit.variable) else null
      atom match
        case LiaTheory.Atom.Bound(x, c, strict) =>
          // `x ≤ c` (or `<`), false: `x > c` (or `≥`).
          val expected = (x, c, if lit.positive then strict else !strict, lit.positive)
          if (h.x, h.c, h.strict, h.upper) == expected then None else Some(s"not the bound of $atom")
        case LiaTheory.Atom.Equal(x, c) =>
          if lit.positive && h.x == x && h.c == c && !h.strict then None else Some(s"not a side of $atom")
        case null => Some("no atom")
  )

  /** Whether `certificate` refutes the negations of the literals of `clause`.
   */
  def check(clause: Array[Lit], certificate: lia.Certificate): Option[String] =
    val hyps = clause.iterator.map(_.neg.index).toSet
    checker.check(certificate, hyps)

/** Checks the input clauses of a proof against where they come from (see
 *  `Encoder.Origin`), reading the literals through what their variables stand
 *  for (`meanings`, see [[denotes]]): a clause of a definition is one of the
 *  clauses of its variable's connective, a clause of an assertion has a literal
 *  for one of the script's `inputs` or is guarded by an assumption, and an
 *  axiom of the encoding is an instance of its schema. A clause may have more
 *  literals than its schema asks: those only weaken it. `assumption(v)` says
 *  whether `v` is the literal of a level or of a named assertion; `testers`
 *  gives the testers of a datatype sort, `sortOf` the sort of a term.
 */
final class InputClauses(
    meanings: collection.IndexedSeq[Formula | Null],
    trueLit: Lit,
    inputs: Set[Formula],
    assumption: cdclt.Var => Boolean,
    testers: String => Option[List[String]],
    sortOf: Term => String,
    declared: String => Boolean
):
  import Formula.*

  private def meaning(v: cdclt.Var): Formula | Null = if v < meanings.length then meanings(v) else null

  /** Whether the literal `l` stands for `formula`, as the encoder reads
   *  formulas: through negations, implications and constant comparisons.
   */
  def denotes(l: Lit, formula: Formula): Boolean = formula match
    case Not(g) => denotes(l.neg, g)
    case True => l == trueLit
    case False => l == trueLit.neg
    case Implies(a, b) => denotes(l, Or(List(Not(a), b)))
    case Eq(a, b) if a == b => l == trueLit
    case Le(a, b) => constant(a, b).fold(l.positive && meaning(l.variable) == formula)(v => l == holds(v <= 0))
    case Less(a, b) => constant(a, b).fold(l.positive && meaning(l.variable) == formula)(v => l == holds(v < 0))
    case _ => l.positive && meaning(l.variable) == formula

  private def holds(b: Boolean): Lit = if b then trueLit else trueLit.neg
  private def constant(a: Term, b: Term): Option[BigInt] = Term.linear(List((1, a), (-1, b))) match
    case Term.Num(v) => Some(v)
    case _ => None

  def check(clause: Array[Lit], origin: Encoder.Origin): Option[String] =
    def has(f: Formula): Boolean = clause.exists(denotes(_, f))
    def positives: Iterator[Formula] = clause.iterator.filter(_.positive).flatMap(l => Option(meaning(l.variable)))
    def negatives: Iterator[Formula] = clause.iterator.filter(!_.positive).flatMap(l => Option(meaning(l.variable)))
    // The two sides of an equality, as `Eq` or as the two bounds of `IntEq`.
    def sides(f: Formula): Option[(Term, Term)] = f match
      case Eq(l, r) => Some((l, r))
      case And(List(Le(l, r), Le(r2, l2))) if l == l2 && r == r2 => Some((l, r))
      case _ => None
    def equal(l: Term, r: Term): Boolean = positives.exists(f => sides(f).contains((l, r)))
    def ok(b: Boolean, what: => String): Option[String] = if b then None else Some(what)
    origin match
      case Encoder.Origin.Definition =>
        ok(
          clause.exists { d =>
            meaning(d.variable) match
              case True => d == trueLit
              case And(args) => if d.positive then args.forall(a => has(Not(a))) else args.exists(has)
              case Or(args) => if d.positive then args.exists(a => has(Not(a))) else args.forall(has)
              case Iff(x, y) =>
                if d.positive then (has(x) && has(y)) || (has(Not(x)) && has(Not(y)))
                else (has(Not(x)) && has(y)) || (has(x) && has(Not(y)))
              case Ite(c, t, e) =>
                if d.positive then (has(Not(c)) && has(Not(t))) || (has(c) && has(Not(e)))
                else (has(Not(c)) && has(t)) || (has(c) && has(e))
              case Pred(Term.Bool(inner)) => if d.positive then has(Not(inner)) else has(inner)
              case _ => false
          },
          "not a clause of a definition"
        )
      case Encoder.Origin.Assertion(f) =>
        // Guarded by an assumption: a refutation that uses it concludes the assumption's negation, which
        // the conclusion allows only for the assumptions of the last solve.
        val guarded = clause.exists(l => !l.positive && assumption(l.variable))
        if !inputs(f) && !guarded then Some(s"$f is not an assertion")
        else ok(has(f), s"no literal of $f")
      case Encoder.Origin.Retired =>
        ok(clause.exists(l => !l.positive && assumption(l.variable)), "not the negation of a selector")
      case Encoder.Origin.Exhaustive(t) =>
        testers(sortOf(t)) match
          case Some(names) => ok(has(Or(names.map(n => Pred(Term.App(Term.Const(n), List(t)))))), "not the testers")
          case None => Some(s"$t is not of a datatype")
      case Encoder.Origin.SharedSplit =>
        // `a = b ∨ a < b ∨ ¬(a ≤ b)`, or `¬(a < b) ∨ a ≤ b`.
        ok(
          positives.exists {
            case Eq(a, b) => has(Less(a, b)) && has(Not(Le(a, b)))
            case Le(a, b) => has(Not(Less(a, b)))
            case _ => false
          },
          "not a split of two terms"
        )
      case Encoder.Origin.Numerals =>
        ok(
          clause.exists(l =>
            meaning(l.variable) match
              case Eq(a, b) => constant(a, b).exists(v => (v == 0) == l.positive)
              case _ => false
          ),
          "not a comparison of numerals"
        )
      case Encoder.Origin.Congruence =>
        // `f ≠ s ∨ f(x) = s(x)`.
        ok(
          positives.exists {
            case Eq(Term.App(f, xs), Term.App(g, ys)) => xs == ys && has(Not(Eq(f, g)))
            case _ => false
          },
          "not an instance of congruence"
        )
      case Encoder.Origin.ReadOverWrite =>
        // `store(a, i, v)(i) = v`, or `i = j ∨ store(a, i, v)(j) = a(j)`.
        ok(
          positives.flatMap(sides).exists {
            case (Term.App(s @ Term.App(Term.Const(n), List(a, i, v)), List(j)), w) if n.startsWith("store!") =>
              (j == i && w == v) || (w == Term.App(a, List(j)) && equal(i, j))
            case _ => false
          },
          "not an array axiom"
        )
      case Encoder.Origin.Extensionality(witnesses) =>
        // `f = g ∨ f(w) ≠ g(w)`, for fresh `w`: the witnesses of `f ≠ g`, Skolem constants of that one
        // disequality, so of no other pair.
        def at(f: Term): Term = witnesses.foldLeft(f)((t, w) => Term.App(t, List(w)))
        positives.collectFirst { case eq @ Eq(f, g) if negatives.contains(Eq(at(f), at(g))) => eq } match
          case None => Some("not an instance of extensionality")
          case Some(eq) =>
            witnesses.zipWithIndex.iterator.flatMap { (w, i) =>
              if !fresh(w) then Some(s"the witness $w is not a fresh symbol")
              else
                witnessOf.getOrElseUpdate(w, (eq, i)) match
                  case (`eq`, `i`) => None
                  case other => Some(s"the witness $w of $eq is also that of ${other._1}")
            }.nextOption()
      case Encoder.Origin.WitnessRange(w, width) =>
        // The range of an index of bit-vectors, which the witness of such an index is in.
        if !fresh(w) then Some(s"the witness $w is not a fresh symbol")
        else
          ranges += ((w, width))
          ok(has(Le(Term.Num(0), w)) || has(Le(w, Term.Num(BigInt(2).pow(width) - 1))), "not the range of a witness")

  /** The witnesses of the extensionality instances checked so far: the
   *  disequality and the index of each.
   */
  private val witnessOf = scala.collection.mutable.HashMap.empty[Term, (Formula, Int)]
  private val ranges = ArrayBuffer.empty[(Term, Int)]

  private def fresh(w: Term): Boolean = w match
    case Term.Const(n) => n.startsWith("ext!") && !declared(n)
    case _ => false

  /** Checks what the clauses checked say together: a witness given the range of
   *  a bit-vector index is the witness of such an index (one that is the
   *  witness of nothing in the proof is unconstrained but for the range).
   */
  def finish(): Option[String] =
    ranges.iterator.flatMap { (w, width) =>
      witnessOf.get(w) match
        case Some((Eq(f, _), i)) =>
          io.bovel.smtlib.Sorts.arrow(sortOf(f)).flatMap(_._1.lift(i)) match
            case Some(s) if s == s"(_ BitVec $width)" => None
            case s => Some(s"the witness $w is an index of sort $s, not of $width bits")
        case _ => None
    }.nextOption()
