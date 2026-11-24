package io.bovel.vik

import scala.collection.mutable.{ArrayBuffer, HashMap, HashSet}

import Sexp.{Atom, Lst}

/** Writes a certificate of Vik (`Session.proof`, see `ProofExport`) as a proof
 *  in CPC, the Cooperating Proof Calculus of cvc5, which Ethos checks against
 *  cvc5's signature `Cpc.eo` together with `proofs/cpc/Vik.eo`.
 *
 *  The proof starts with the declarations of the script's sorts and symbols and
 *  one `assume` per assertion of the script, as written. The rest follows the
 *  answer, one CPC derivation per step:
 *
 *    - an input clause from its origin: the assertion itself, or the CNF rule
 *      of the formula a Tseitin variable stands for;
 *    - a lemma of the theory of uninterpreted functions as a scope over the
 *      negations of its literals, inside which the equality proof derives
 *      `false`;
 *    - a derived clause as one `chain_m_resolution` over its hints, the order
 *      and pivots found by replaying the unit propagation.
 *
 *  A Tseitin variable is the formula it stands for, so the proof has no
 *  variables of its own. Terms are shared with `define`, one per node of the
 *  script or of the lowered problem that has children.
 *
 *  This covers Booleans, uninterpreted sorts and functions. Anything else
 *  throws [[Unsupported]].
 */
object Cpc:

  /** Not a certificate this driver reads. */
  type Malformed = Sexp.Malformed
  def Malformed(message: String): Malformed = Sexp.Malformed(message)

  /** A certificate this driver does not translate yet. */
  final class Unsupported(message: String) extends Exception(message)

  /** A literal of the answer: a variable, positive or negated. */
  private final case class Lit(v: Int, pos: Boolean):
    def neg: Lit = Lit(v, !pos)

  /** The CPC proof of `certificate`. A compact proof derives each clause of
   *  conflict analysis by the rule `vik_rup` of `Vik.eo`, from the clauses that
   *  propagate; a plain one (`compact = false`) by the chain of resolutions it
   *  stands for, in CPC's rules only, for checkers that know no `Vik.eo`.
   */
  def apply(certificate: String, compact: Boolean = true): String = Writer(certificate, compact).write()

  private def num(s: Sexp): BigInt = s match
    case Atom(t) => BigInt(t)
    case _ => throw Malformed(s"not a number: ${s.toString.take(100)}")
  private def int(s: Sexp): Int = num(s).toInt
  private def items(s: Sexp): Vector[Sexp] = Sexp.items(s)
  private def ints(s: Sexp): Vector[Int] = items(s).map(int)
  private def bool(s: Sexp): Boolean = s match
    case Atom("true") => true
    case Atom("false") => false
    case _ => throw Malformed(s"not a Boolean: ${s.toString.take(100)}")
  private def lit(s: Sexp): Lit = s match
    case Lst(Vector(v, p)) => Lit(int(v), bool(p))
    case _ => throw Malformed(s"not a literal: ${s.toString.take(100)}")
  private def option(s: Sexp): Option[Sexp] = s match
    case Atom("none") => None
    case Lst(Vector(Atom("some"), x)) => Some(x)
    case _ => throw Malformed(s"not an option: ${s.toString.take(100)}")

  /** The head and arguments of a constructor application. */
  private object Ctor:
    def unapply(s: Sexp): Option[(String, Vector[Sexp])] = s match
      case Atom(name) => Some((name, Vector.empty))
      case Lst(Atom(name) +: args) => Some((name, args))
      case _ => None

  private final class Writer(certificate: String, compact: Boolean):
    private val sections: Map[String, Map[String, Sexp]] = Sexp.sections(certificate).view.mapValues(_.map {
      case Lst(Vector(Atom(f), v)) => f -> v
      case s => throw Malformed(s"not a field: ${s.toString.take(100)}")
    }.toMap).toMap

    private def field(section: String, f: String): Sexp =
      sections.getOrElse(section, throw Malformed(s"no $section")).getOrElse(f, throw Malformed(s"no $f in $section"))

    // The script.
    private val (sSorts, sDecls) = field("script", "sig") match
      case Lst(Vector(sorts, decls)) => (items(sorts), ints(decls))
      case s => throw Malformed(s"not a signature: ${s.toString.take(100)}")
    private val sNodes = items(field("script", "nodes"))
    private val asserts = ints(field("script", "asserts"))
    if items(field("script", "datatypes")).nonEmpty then throw Unsupported("datatypes")

    /** The definitions: symbol, parameters, body nodes and root. */
    private val defs = items(field("script", "defs")).map {
      case Lst(Vector(f, ps, ns, r)) => (int(f), ints(ps), items(ns), int(r))
      case d => throw Malformed(s"not a definition: ${d.toString.take(100)}")
    }

    // The trace.
    private val traceNode = ints(field("trace", "node"))
    private val mints = items(field("trace", "mints"))
    private val inputWhys = items(field("trace", "inputs"))
    private val levelWhys = items(field("trace", "levels")).map(items)

    // The lowered problem.
    private val lNodes = items(field("problem", "nodes"))
    private val inputs = ints(field("problem", "inputs"))
    if items(field("problem", "datatypes")).nonEmpty then throw Unsupported("datatypes")
    if items(field("problem", "stores")).nonEmpty then throw Unsupported("arrays")

    // The answer.
    private val meaning = items(field("answer", "meaning")).map(option(_).map(int))
    private val trueLit = lit(field("answer", "trueLit"))
    private val ufAtoms = items(field("answer", "ufAtoms")).map(option(_).map(p =>
      ints(p) match
        case Vector(a, b) => (a, b)
        case _ => throw Malformed(s"not a pair: $p")
    ))
    private val trueClass = int(field("answer", "trueClass"))
    private val falseClass = int(field("answer", "falseClass"))
    private val steps = items(field("answer", "steps"))
    private val justs = items(field("answer", "justs"))
    private val conclusion = int(field("answer", "conclusion"))

    /** The formulas each level variable guards, and the levels the last check
     *  assumed. The proof takes the assumed levels as true, so their negations
     *  drop from the clauses, and it needs no clause of a retired level.
     */
    private val levels = items(field("answer", "levels")).map {
      case Lst(Vector(v, fs)) => int(v) -> ints(fs)
      case l => throw Malformed(s"not a level: $l")
    }.toMap
    private val assumedLevels = ints(field("answer", "assumed"))
    if items(field("answer", "exts")).nonEmpty then throw Unsupported("extensionality")
    if items(field("answer", "liaAtoms")).exists(_ != Atom("none")) then throw Unsupported("arithmetic")

    private val out = StringBuilder()
    private var fresh = 0
    private def id(prefix: String): String =
      fresh += 1
      s"@$prefix$fresh"

    // ----------------------------------------------------------------------
    // Sorts and symbols

    private def sort(s: Int): String = sSorts.lift(s) match
      case Some(Atom("bool")) => "Bool"
      case Some(Atom("int")) => throw Unsupported("arithmetic")
      case Some(Atom("real")) => throw Unsupported("arithmetic")
      case Some(Atom("user")) => s"S$s"
      case Some(Ctor("bv", _)) => throw Unsupported("bit-vectors")
      case Some(Ctor("array", _)) => throw Unsupported("arrays")
      case Some(Ctor("fn", Vector(args, res))) => (ints(args).map(sort) :+ sort(int(res))).mkString("(-> ", " ", ")")
      case other => throw Malformed(s"no sort $s: $other")

    private def symbol(k: Int): String = s"x$k"

    /** The sorts, the declared symbols, and each definition as a CPC `define`,
     *  which Ethos expands where the script uses it, as the lowering inlines
     *  it.
     */
    private def declarations(): Unit =
      for (s, i) <- sSorts.zipWithIndex if s == Atom("user") do header ++= s"(declare-sort S$i 0)\n"
      val defined = HashMap.from(defs.map(d => d._1 -> d))
      val params = defs.flatMap(_._2).toSet
      // The declarations first, as a definition may use symbols declared after it.
      for (s, k) <- sDecls.zipWithIndex if !params(k) && !defined.contains(k) do
        header ++= s"(declare-const ${symbol(k)} ${sort(s)})\n"
      for (s, k) <- sDecls.zipWithIndex do
        defined.get(k) match
          case None => ()
          case Some((_, ps, ns, r)) =>
            val texts = HashMap.empty[Int, String]
            def body(i: Int): String = texts.getOrElseUpdate(
              i,
              surface(ns.lift(i).getOrElse(throw Malformed(s"no node $i in a definition")), body, t => t)
            )
            val bindings = ps.map(p => s"(${symbol(p)} ${sort(sDecls(p))})").mkString(" ")
            header ++= s"(define ${symbol(k)} ($bindings) ${body(r)} :type ${sort(s)})\n"

    // ----------------------------------------------------------------------
    // Terms: each node with children is a `define` of its own.

    private val sDefined = HashMap.empty[Int, String]
    private val lDefined = HashMap.empty[Int, String]

    /** The term of surface node `i`. */
    private def sTerm(i: Int): String =
      sDefined.getOrElseUpdate(
        i, {
          surface(sNodes.lift(i).getOrElse(throw Malformed(s"no surface node $i")), sTerm, define(s"s$i", _))
        }
      )

    /** The term of a surface node, its children's terms from `sub`, and `share`
     *  naming it when it has children.
     */
    private def surface(node: Sexp, sub: Int => String, share: String => String): String =
      def all(name: String, as: Sexp) = ints(as).map(sub).mkString(s"($name ", " ", ")")
      node match
        case Ctor("const", Vector(n)) => symbol(int(n))
        case Ctor("tt", _) => "true"
        case Ctor("ff", _) => "false"
        case Ctor("bound", Vector(d)) => sub(int(d))
        case Ctor("letIn", Vector(_, body)) => sub(int(body))
        case node =>
          share(node match
            case Ctor("app", Vector(f, args)) => (sub(int(f)) +: ints(args).map(sub)).mkString("(", " ", ")")
            case Ctor("not", Vector(a)) => s"(not ${sub(int(a))})"
            case Ctor("and", Vector(as)) => nary("and", "true", ints(as).map(sub))
            case Ctor("or", Vector(as)) => nary("or", "false", ints(as).map(sub))
            case Ctor("implies", Vector(as)) => all("=>", as)
            case Ctor("iff", Vector(as)) => all("=", as)
            case Ctor("xor", Vector(as)) => all("xor", as)
            case Ctor("eq", Vector(as)) => all("=", as)
            case Ctor("distinct", Vector(as)) => all("distinct", as)
            case Ctor("ite", Vector(c, a, b)) => s"(ite ${sub(int(c))} ${sub(int(a))} ${sub(int(b))})"
            case Ctor(name, _) => throw Unsupported(s"surface $name"))

    /** The term of lowered node `i`. */
    private def lTerm(i: Int): String =
      lDefined.getOrElseUpdate(
        i,
        lNodes.lift(i).getOrElse(throw Malformed(s"no lowered node $i")) match
          case Ctor("const", Vector(n)) =>
            val k = int(n)
            if k < sDecls.length then symbol(k) else minted(k)
          case Ctor("tt", _) => "true"
          case Ctor("ff", _) => "false"
          case Ctor("bterm", Vector(f)) => lTerm(int(f))
          case Ctor("pred", Vector(t)) => lTerm(int(t))
          case node =>
            val text = node match
              case Ctor("app", Vector(f, args)) => (lTerm(int(f)) +: ints(args).map(lTerm)).mkString("(", " ", ")")
              case Ctor("not", Vector(a)) => s"(not ${lTerm(int(a))})"
              case Ctor("and", Vector(as)) => nary("and", "true", ints(as).map(lTerm))
              case Ctor("or", Vector(as)) => nary("or", "false", ints(as).map(lTerm))
              case Ctor("implies", Vector(a, b)) => s"(=> ${lTerm(int(a))} ${lTerm(int(b))})"
              case Ctor("iff", Vector(a, b)) => s"(= ${lTerm(int(a))} ${lTerm(int(b))})"
              case Ctor("eq", Vector(a, b)) => s"(= ${lTerm(int(a))} ${lTerm(int(b))})"
              case Ctor("ite", Vector(c, a, b)) => s"(ite ${lTerm(int(c))} ${lTerm(int(a))} ${lTerm(int(b))})"
              case Ctor(name, _) => throw Unsupported(s"lowered $name")
            define(s"t$i", text)
      )

    /** A symbol the lowering mints. The value of an `ite` is a `define` of the
     *  `ite` of the lowered condition and branches.
     */
    private def minted(k: Int): String = iteOf(k)._1

    private val ites = HashMap.empty[Int, (String, String, String, String)]

    /** The `ite` symbol `k`: its term, condition and branches. */
    private def iteOf(k: Int): (String, String, String, String) = ites.getOrElseUpdate(
      k,
      mints.lift(k - sDecls.length) match
        case Some(Ctor("ite", Vector(i))) =>
          sNodes.lift(int(i)) match
            case Some(Ctor("ite", Vector(c, a, b))) =>
              val Seq(tc, ta, tb) = Seq(c, a, b).map(x => lTerm(traceNode(int(x))))
              (define(s"m$k", s"(ite $tc $ta $tb)"), tc, ta, tb)
            case other => throw Malformed(s"the ite symbol $k is of no ite: $other")
        case Some(Ctor(name, _)) => throw Unsupported(s"minted symbols ($name)")
        case other => throw Malformed(s"no minted symbol $k: $other")
    )

    /** An n-ary connective: its unit with no argument. */
    private def nary(op: String, unit: String, args: Seq[String]): String =
      if args.isEmpty then unit else args.mkString(s"($op ", " ", ")")

    /** The declarations and definitions, which precede the proof so that no
     *  `assume-push` scopes them.
     */
    private val header = StringBuilder()

    /** The name of each term defined, by its text. */
    private val names = HashMap.empty[String, String]

    /** A term, as the name it is defined by if any: the same term is then the
     *  same text, as resolution compares literals.
     */
    private def canon(text: String): String = names.getOrElse(text, text)

    private def define(name: String, text: String): String =
      names.get(text) match
        case Some(n) => n
        case None =>
          names(text) = name
          header ++= s"(define $name () $text)\n"
          name

    // ----------------------------------------------------------------------
    // Literals and clauses

    /** The lowered node a variable stands for. */
    private def meaningOf(v: Int): Int =
      meaning.lift(v).flatten.getOrElse(throw Unsupported(s"variable $v stands for no formula"))

    private def formula(v: Int): String = lTerm(meaningOf(v))

    private def litTerm(l: Lit): String = if l.pos then formula(l.v) else canon(s"(not ${formula(l.v)})")

    private def clauseTerm(c: Seq[Lit]): String = c match
      case Seq() => "false"
      case Seq(l) => litTerm(l)
      case _ => c.map(litTerm).mkString("(or ", " ", ")")

    /** A step. A compact proof leaves out its conclusion, which Ethos computes
     *  from the rule.
     */
    private def step(conclusion: String, rule: String, premises: Seq[String] = Nil, args: Seq[String] = Nil): String =
      val p = id("p")
      out ++= (if compact then s"(step $p :rule $rule" else s"(step $p $conclusion :rule $rule")
      if premises.nonEmpty then out ++= premises.mkString(" :premises (", " ", ")")
      if args.nonEmpty then out ++= args.mkString(" :args (", " ", ")")
      out ++= ")\n"
      p

    /** The `scope` that closes the innermost `assume-push`, as `p`. */
    private def pop(p: String, conclusion: String, premise: String): Unit =
      out ++=
        (if compact then s"(step-pop $p :rule scope :premises ($premise))\n"
         else s"(step-pop $p $conclusion :rule scope :premises ($premise))\n")

    // ----------------------------------------------------------------------
    // Steps

    /** The CPC step of each answer step, and the clause it proves, literal by
     *  literal, as the answer gives it.
     */
    private val proved = ArrayBuffer.empty[(String, Vector[Lit])]

    /** The `assume` of each surface assertion. */
    private val assumed = HashMap.empty[Int, String]

    /** The clause of a step, without the negations of assumed levels. */
    private def stepClause(s: Sexp): Vector[Lit] =
      val c = s match
        case Ctor("input", Vector(c)) => items(c).map(lit)
        case Ctor("lemma", Vector(c)) => items(c).map(lit)
        case Ctor("derived", Vector(c, _)) => items(c).map(lit)
        case _ => throw Malformed(s"not a step: ${s.toString.take(100)}")
      c.filterNot(l => !l.pos && assumedLevels.contains(l.v))

    /** The steps the conclusion depends on. */
    private def cone(): Set[Int] =
      val seen = HashSet.empty[Int]
      val todo = ArrayBuffer(conclusion)
      while todo.nonEmpty do
        val k = todo.remove(todo.length - 1)
        if seen.add(k) then
          steps.lift(k) match
            case Some(Ctor("derived", Vector(_, hints))) => todo ++= ints(hints).filter(_ < k)
            case Some(_) => ()
            case None => throw Malformed(s"no step $k")
      seen.toSet

    def write(): String =
      declarations()
      for (a, i) <- asserts.zipWithIndex do
        val t = sTerm(a)
        val p = s"@a$i"
        out ++= s"(assume $p $t)\n"
        assumed(a) = p
      val needed = cone()
      for ((s, j), k) <- steps.zip(justs).zipWithIndex do
        val c = stepClause(s)
        if !needed(k) then proved += "" -> c
        else
          if c.exists(l => levels.contains(l.v)) then throw Unsupported("clause of a level not assumed")
          val p = (s, j) match
            case (Ctor("input", _), Ctor("input", Vector(origin))) => input(c, origin)
            case (Ctor("lemma", _), Ctor("uf", Vector(proof, cert))) => ufLemma(c, items(proof), cert)
            case (Ctor("lemma", _), Ctor(name, _)) => throw Unsupported(s"$name lemma")
            case (Ctor("derived", Vector(_, hints)), _) => derived(c, ints(hints))
            case _ => throw Malformed(s"step $k does not match its justification")
          // Resolution removes one occurrence of a pivot: factor the clause.
          val set = c.distinctBy(l => (formula(l.v), l.pos))
          if set.length < c.length then proved += step(clauseTerm(set), "factoring", Seq(p)) -> set
          else proved += p -> c
      if proved.lift(conclusion).forall(_._2.nonEmpty) then throw Malformed("the conclusion is not the empty clause")
      header.result() + out.result()

    // ----------------------------------------------------------------------
    // Inputs

    private def input(c: Vector[Lit], origin: Sexp): String = origin match
      case Ctor("assertion", Vector(f)) => assertion(c, int(f))
      case Ctor("definition", _) => definition(c)
      case Ctor(name, _) => throw Unsupported(s"$name input")

    /** The clause of the lowered input `f`, from the surface assertion it
     *  lowers: the same CPC term once Ethos reads the chains of the surface,
     *  then the literal of the clause that stands for it.
     */
    private def assertion(c: Vector[Lit], f: Int): String =
      val why = inputs.indexOf(f) match
        case -1 =>
          assumedLevels.zipWithIndex.collectFirst(Function.unlift { (g, k) =>
            levels.get(g).map(_.indexOf(f)).filter(_ >= 0).flatMap(i => levelWhys.lift(k).flatMap(_.lift(i)))
          })
        case j => inputWhys.lift(j)
      val lowered = holds(why.getOrElse(throw Malformed(s"input $f has no reason")), f)
      c match
        case Vector(l) if denotes(l, f) =>
          bridge(f, l) match
            case None => lowered
            case Some(e) => step(litTerm(l), "eq_resolve", Seq(lowered, e))
        case _ => throw Unsupported("assertion with other literals")

    /** A proof of the lowered input `f`, which holds by `why`. */
    private def holds(why: Sexp, f: Int): String = why match
      case Ctor("assert", Vector(a)) => step(lTerm(f), "vik_lower", Seq(assumed(int(a))), Seq(lTerm(f)))
      case Ctor(name @ ("iteThen" | "iteElse"), Vector(k)) =>
        // `c → k = t` (or `¬c → k = e`): under `c` (or `¬c`), the branch of
        // `ite_eq` that `cnf_ite_pos1` (or `cnf_ite_pos2`) gives.
        val thn = name == "iteThen"
        val (ite, c, a, b) = iteOf(int(k))
        val (hyp, eq) = lNodes(f) match
          case Ctor("implies", Vector(h, e)) => (lTerm(int(h)), lTerm(int(e)))
          case n => throw Malformed(s"not an implication: $n")
        val axiom = s"(ite $c (= $ite $a) (= $ite $b))"
        val p0 = step(axiom, "ite_eq", args = Seq(ite))
        val cnf = step(
          s"(or (not $axiom) ${if thn then s"(not $c)" else c} $eq)",
          if thn then "cnf_ite_pos1" else "cnf_ite_pos2",
          args = Seq(axiom)
        )
        val h = id("h")
        out ++= s"(assume-push $h $hyp)\n"
        val r = step(
          eq,
          "chain_m_resolution",
          Seq(cnf, p0, h),
          Seq(eq, s"(@list false ${if thn then "false" else "true"})", s"(@list $axiom $c)")
        )
        val p = id("p")
        pop(p, s"${lTerm(f)}", r)
        p
      case Ctor("simp", Vector(o0, w, h)) =>
        val o = int(o0)
        val hints = items(h).map {
          case Lst(Vector(c, ps)) =>
            int(c) -> items(ps).map {
              case Lst(Vector(i, Atom(left))) => (int(i), left == "true")
              case x => throw Malformed(s"not a simplification hint: $x")
            }
          case x => throw Malformed(s"not a simplification hint: $x")
        }.toMap
        Simp(hints).weak(Simp.Ctx(Vector.empty), o, f, holds(w, o))
      case Ctor(name, _) => throw Unsupported(s"input of reason $name")
      case other => throw Malformed(s"not a reason: $other")

    /** The proof that a simplified input holds, from the proof of the formula
     *  it simplifies (`weaker` in `Vik/Simp.lean`): through the positive
     *  positions of both, the equalities a conjunction of the original loses
     *  rewrite the rest, by congruence.
     */
    private class Simp(hints: Map[Int, Vector[(Int, Boolean)]]):
      import Simp.Ctx

      private def node(i: Int): Sexp = lNodes.lift(i).getOrElse(throw Malformed(s"no lowered node $i"))

      /** The node with its children left out, and its children. */
      private def shape(i: Int): (Sexp, Vector[Int]) = node(i) match
        case Ctor("app", Vector(f, as)) => (Atom("app"), int(f) +: ints(as))
        case Ctor(k @ ("and" | "or"), Vector(as)) => (Lst(Vector(Atom(k), Atom(ints(as).length.toString))), ints(as))
        case Ctor(k @ ("not" | "bterm" | "pred"), Vector(a)) => (Atom(k), Vector(int(a)))
        case Ctor(k @ ("implies" | "iff" | "eq"), Vector(a, b)) => (Atom(k), Vector(int(a), int(b)))
        case Ctor("ite", Vector(c, a, b)) => (Atom("ite"), Vector(int(c), int(a), int(b)))
        case n => (n, Vector())

      /** Whether `a` and `b` are equal given the equalities of `ctx`. */
      private def eqvOk(ctx: Ctx, a: Int, b: Int, depth: Int = 0): Boolean =
        depth < 10000 && ctx.memo.getOrElseUpdate(
          (a, b),
          a == b || ctx.eqs.exists((x, y, _) => x == a && eqvOk(ctx, y, b, depth + 1)) || {
            val (ka, as) = shape(a)
            val (kb, bs) = shape(b)
            ka == kb && as.nonEmpty && as.length == bs.length && as.zip(bs).forall(eqvOk(ctx, _, _, depth + 1))
          }
        )

      /** A proof of `(= a b)`, which `eqvOk` accepts. */
      private def eqv(ctx: Ctx, a: Int, b: Int): String =
        val (ta, tb) = (lTerm(a), lTerm(b))
        if a == b || ta == tb then step(s"(= $ta $tb)", "refl", args = Seq(ta))
        else
          ctx.eqs.collectFirst { case (x, y, p) if x == a && eqvOk(ctx, y, b) => (y, p) } match
            case Some((y, p)) =>
              if y == b then p else step(s"(= $ta $tb)", "trans", Seq(p, eqv(ctx, y, b)))
            case None =>
              val (k, as) = shape(a)
              val ps = as.zip(shape(b)._2).map(eqv(ctx, _, _))
              val e = s"(= $ta $tb)"
              k match
                case Atom("bterm" | "pred") => ps.head
                case Lst(_) => step(e, "nary_cong", ps, Seq(ta))
                case Atom("app") if as.head == shape(b)._2.head => step(e, "cong", ps.tail, Seq(ta))
                case Atom("app") => step(e, "ho_cong", ps)
                case _ => step(e, "cong", ps, Seq(ta))

      /** Whether `s` holds where `o` and the equalities of `ctx` do. */
      private def ok(ctx: Ctx, o: Int, s: Int, d: Int): Boolean =
        d > 0 &&
          (eqvOk(ctx, o, s) ||
            ((node(o), node(s)) match
              case (Ctor("or", Vector(os)), Ctor("or", Vector(ss))) =>
                ints(os).length == ints(ss).length && ints(os).zip(ints(ss)).forall(ok(ctx, _, _, d - 1))
              case (Ctor("implies", Vector(a, b)), Ctor("implies", Vector(a2, b2))) =>
                eqvOk(ctx, int(a), int(a2)) && ok(ctx, int(b), int(b2), d - 1)
              case (Ctor("and", Vector(os)), sn) =>
                val (inner, kept) = conj(ctx, o, ints(os), None)
                kept match
                  case Vector() => sn match
                      case Ctor("tt", _) => true;
                      case _ => false
                  case Vector((x, _)) => ok(inner, x, s, d - 1)
                  case xs =>
                    sn match
                      case Ctor("and", Vector(ss)) =>
                        xs.length == ints(ss).length && xs.zip(ints(ss)).forall((x, y) => ok(inner, x._1, y, d - 1))
                      case _ => false
              case _ => false))

      /** The context of the conjuncts `os` of conjunction `o`, with the
       *  equalities its hints eliminate, and the conjuncts it keeps with their
       *  positions. With the proof of `o`, the equalities have proofs.
       */
      private def conj(ctx: Ctx, o: Int, os: Vector[Int], proof: Option[String]): (Ctx, Vector[(Int, Int)]) =
        val elim = hints.getOrElse(o, Vector())
        val eqs = elim.flatMap { (i, left) =>
          os.lift(i).flatMap { c =>
            node(c) match
              case Ctor("eq" | "iff", Vector(x0, y0)) =>
                val (x, y) = (int(x0), int(y0))
                val p = proof.fold("") { po =>
                  val e = step(lTerm(c), "and_elim", Seq(po), Seq(i.toString))
                  if left then e else step(s"(= ${lTerm(y)} ${lTerm(x)})", "symm", Seq(e))
                }
                Some(if left then (x, y, p) else (y, x, p))
              case _ => None
          }
        }
        (Ctx(ctx.eqs ++ eqs), os.zipWithIndex.filterNot((_, i) => elim.exists(_._1 == i)))

      /** A proof of `s`, from the proof `p` of `o`. */
      def weak(ctx: Ctx, o: Int, s: Int, p: String): String =
        if !ok(ctx, o, s, lNodes.length + 1) then throw Unsupported("simplification")
        build(ctx, o, s, p, lNodes.length + 1)

      private def build(ctx: Ctx, o: Int, s: Int, p: String, d: Int): String =
        val (to, ts) = (lTerm(o), lTerm(s))
        if to == ts then p
        else if eqvOk(ctx, o, s) then step(ts, "eq_resolve", Seq(p, eqv(ctx, o, s)))
        else
          (node(o), node(s)) match
            case (Ctor("or", Vector(os0)), Ctor("or", Vector(ss0))) =>
              // Each disjunct of `s` from its disjunct of `o`, under it.
              val (os, ss) = (ints(os0), ints(ss0))
              val cases = os.zip(ss).map { (x, y) =>
                val h = id("h")
                out ++= s"(assume-push $h ${lTerm(x)})\n"
                val q = build(ctx, x, y, h, d - 1)
                val r = id("p")
                pop(r, s"(=> ${lTerm(x)} ${lTerm(y)})", q)
                step(s"(or (not ${lTerm(x)}) ${lTerm(y)})", "implies_elim", Seq(r))
              }
              step(
                ts,
                "chain_m_resolution",
                p +: cases,
                Seq(ts, os.map(_ => "true").mkString("(@list ", " ", ")"), os.map(lTerm).mkString("(@list ", " ", ")"))
              )
            case (Ctor("implies", Vector(a0, b0)), Ctor("implies", Vector(a1, b1))) =>
              val (a, b, a2, b2) = (int(a0), int(b0), int(a1), int(b1))
              val h = id("h")
              out ++= s"(assume-push $h ${lTerm(a2)})\n"
              val ha = if lTerm(a) == lTerm(a2) then h else step(lTerm(a), "eq_resolve", Seq(h, eqv(ctx, a2, a)))
              val ab = step(s"(or (not ${lTerm(a)}) ${lTerm(b)})", "implies_elim", Seq(p))
              val hb = step(
                lTerm(b),
                "chain_m_resolution",
                Seq(ab, ha),
                Seq(lTerm(b), "(@list false)", s"(@list ${lTerm(a)})")
              )
              val q = build(ctx, b, b2, hb, d - 1)
              val r = id("p")
              pop(r, s"$ts", q)
              r
            case (Ctor("and", Vector(os)), _) =>
              val (inner, kept) = conj(ctx, o, ints(os), Some(p))
              def part(x: Int, i: Int) = step(lTerm(x), "and_elim", Seq(p), Seq(i.toString))
              kept match
                case Vector() => step("true", "true_elim", Seq(step("(= true true)", "refl", args = Seq("true"))))
                case Vector((x, i)) => build(inner, x, s, part(x, i), d - 1)
                case xs =>
                  val ss = node(s) match
                    case Ctor("and", Vector(ss)) => ints(ss)
                    case n => throw Malformed(s"not a conjunction: $n")
                  step(ts, "and_intro", xs.zip(ss).map { case ((x, i), y) => build(inner, x, y, part(x, i), d - 1) })
            case _ => throw Malformed(s"no simplification of $o to $s")

    private object Simp:
      /** The equalities that hold, each from its left side, with its proof. */
      final case class Ctx(eqs: Vector[(Int, Int, String)]):
        val memo = HashMap.empty[(Int, Int), Boolean]

    /** Whether literal `l` stands for the formula of node `f`, as the encoder
     *  reads formulas: through negations, implications and reflexive equalities
     *  (`denotes` in `Vik/Cert/Inputs.lean`).
     */
    private def denotes(l: Lit, f: Int, fuel: Int = 64): Boolean =
      fuel > 0 && {
        val plain = l.pos && meaning.lift(l.v).flatten.contains(f)
        lNodes(f) match
          case Ctor("not", Vector(g)) => denotes(l.neg, int(g), fuel - 1)
          case Ctor("tt", _) => l == trueLit
          case Ctor("ff", _) => l == trueLit.neg
          case Ctor("implies", Vector(a, b)) =>
            l.pos && meaning.lift(l.v).flatten.exists { m =>
              lNodes(m) match
                case Ctor("or", Vector(Lst(Vector(n, b2)))) => b2 == b && lNodes(int(n)) == Lst(Vector(Atom("not"), a))
                case _ => false
            }
          case Ctor("eq", Vector(a, b)) if a == b => l == trueLit
          case Ctor("eq", Vector(a, b)) => plain || l.pos && reversed(l, a, b)
          case _ => plain
      }

    /** Whether the positive literal `l` means the equality `b = a`: one atom
     *  stands for both orientations of an equality.
     */
    private def reversed(l: Lit, a: Sexp, b: Sexp): Boolean =
      meaning.lift(l.v).flatten.exists(m =>
        lNodes(m) match
          case Ctor("eq", Vector(a2, b2)) => a2 == b && b2 == a
          case _ => false
      )

    /** A proof that the formula of node `f` is the term of the literal `l` that
     *  stands for it, or none when they are the same term.
     */
    private def bridge(f: Int, l: Lit): Option[String] =
      val tf = lTerm(f)
      val tl = litTerm(l)
      lNodes(f) match
        case Ctor("not", Vector(g0)) =>
          val g = int(g0)
          // `(not g)` is `(not l̄)`, l̄ the term of `l.neg`.
          val inner = bridge(g, l.neg).map(b => step(s"(= $tf (not ${litTerm(l.neg)}))", "cong", Seq(b), Seq(tf)))
          if !l.pos then inner
          else
            // `l.neg` is `(not l)`: `(not (not l))` is `l`.
            val dn = step(s"(= (not (not $tl)) $tl)", "bool-double-not-elim", args = Seq(tl))
            Some(inner.fold(dn)(p => step(s"(= $tf $tl)", "trans", Seq(p, dn))))
        case Ctor("ff", _) =>
          val p = step("(= (not true) false)", "evaluate", args = Seq("(not true)"))
          Some(step("(= false (not true))", "symm", Seq(p)))
        case Ctor("implies", Vector(a, b)) =>
          Some(step(s"(= $tf $tl)", "bool-impl-elim", args = Seq(lTerm(int(a)), lTerm(int(b)))))
        case Ctor("eq", Vector(a, b)) if a == b =>
          Some(step(s"(= $tf true)", "eq-refl", args = Seq(lTerm(int(a)))))
        case Ctor("eq", Vector(a, b)) if l.pos && !meaning.lift(l.v).flatten.contains(f) && reversed(l, a, b) =>
          Some(step(s"(= $tf $tl)", "eq-symm", args = Seq(lTerm(int(a)), lTerm(int(b)))))
        case _ => None

    /** The literal `x` of a clause proved by `p`, replaced by `y`, given a
     *  proof `e` of `(= x y)`.
     */
    private def rewriteLit(p: String, clause: Seq[String], x: String, y: String, e: String): (String, Seq[String]) =
      val ce = step(s"(or (not (= $x $y)) (not $x) $y)", "cnf_equiv_pos1", args = Seq(s"(= $x $y)"))
      val out = clause.map(t => if t == x then y else t)
      val concl = clauseOf(out)
      (
        step(concl, "chain_m_resolution", Seq(p, ce, e), Seq(concl, "(@list true false)", s"(@list $x (= $x $y))")),
        out
      )

    private def clauseOf(ts: Seq[String]): String = ts match
      case Seq() => "false"
      case Seq(t) => t
      case _ => ts.mkString("(or ", " ", ")")

    /** A clause of the definition of a Tseitin variable, from its CNF rule. */
    private def definition(c: Vector[Lit]): String =
      if c == Vector(trueLit) && trueLit.pos then
        val r = step("(= true true)", "refl", args = Seq("true"))
        return step("true", "true_elim", Seq(r))
      // The literal of the variable defined: the first whose formula has the
      // shape of the clause.
      val found = c.iterator.flatMap(d => cnf(c, d)).nextOption()
      found.getOrElse(throw Unsupported(s"definition clause ${c.map(litTerm).mkString(" ")}"))

    private def nodeOf(v: Int): Sexp = lNodes(meaningOf(v))

    /** The CNF step for clause `c` from the definition of the variable of
     *  literal `d`, when `c` is one, with each literal of a subformula then
     *  rewritten to the term of the literal of `c` that stands for it.
     */
    private def cnf(c: Vector[Lit], d: Lit): Option[String] =
      val f = formula(d.v)

      /** The literal of `c` that stands for node `n`, positive or negated. */
      def find(n: Int, pos: Boolean): Option[Lit] = c.find(l => denotes(if pos then l else l.neg, n))
      def has(n: Int, pos: Boolean) = find(n, pos).isDefined
      // The rule, its arguments, and the literals of its conclusion: the
      // defined formula's (`None`), or a subformula's, positive or negated.
      type Shape = (String, Seq[String], Seq[(Option[Int], Boolean)])
      val self = (None, d.pos)
      def sub(n: Int, pos: Boolean) = (Some(n), pos)
      val shape: Option[Shape] = nodeOf(d.v) match
        case Ctor("and", Vector(as)) =>
          val xs = ints(as)
          if d.pos && xs.forall(has(_, false)) then Some(("cnf_and_neg", Seq(f), self +: xs.map(sub(_, false))))
          else if !d.pos then
            xs.indexWhere(has(_, true)) match
              case -1 => None
              case i => Some(("cnf_and_pos", Seq(f, i.toString), Seq(self, sub(xs(i), true))))
          else None
        case Ctor("or", Vector(as)) =>
          val xs = ints(as)
          if !d.pos && xs.forall(has(_, true)) then Some(("cnf_or_pos", Seq(f), self +: xs.map(sub(_, true))))
          else if d.pos then
            xs.indexWhere(has(_, false)) match
              case -1 => None
              case i => Some(("cnf_or_neg", Seq(f, i.toString), Seq(self, sub(xs(i), false))))
          else None
        case Ctor("iff", Vector(x0, y0)) =>
          val (x, y) = (int(x0), int(y0))
          if d.pos && has(x, false) && has(y, false) then
            Some(("cnf_equiv_neg2", Seq(f), Seq(self, sub(x, false), sub(y, false))))
          else if d.pos && has(x, true) && has(y, true) then
            Some(("cnf_equiv_neg1", Seq(f), Seq(self, sub(x, true), sub(y, true))))
          else if !d.pos && has(x, false) && has(y, true) then
            Some(("cnf_equiv_pos1", Seq(f), Seq(self, sub(x, false), sub(y, true))))
          else if !d.pos && has(x, true) && has(y, false) then
            Some(("cnf_equiv_pos2", Seq(f), Seq(self, sub(x, true), sub(y, false))))
          else None
        case Ctor("ite", Vector(x0, a0, b0)) =>
          val (x, a, b) = (int(x0), int(a0), int(b0))
          if d.pos && has(x, false) && has(a, false) then
            Some(("cnf_ite_neg1", Seq(f), Seq(self, sub(x, false), sub(a, false))))
          else if d.pos && has(x, true) && has(b, false) then
            Some(("cnf_ite_neg2", Seq(f), Seq(self, sub(x, true), sub(b, false))))
          else if !d.pos && has(x, false) && has(a, true) then
            Some(("cnf_ite_pos1", Seq(f), Seq(self, sub(x, false), sub(a, true))))
          else if !d.pos && has(x, true) && has(b, true) then
            Some(("cnf_ite_pos2", Seq(f), Seq(self, sub(x, true), sub(b, true))))
          else None
        case _ => None
      shape match
        case Some((rule, args, lits)) =>
          def term(n: Option[Int], pos: Boolean) =
            val t = n.fold(f)(lTerm)
            if pos then t else canon(s"(not $t)")
          val terms = lits.map(term)
          var p = step(clauseOf(terms), rule, args = args)
          // A definition over the same formula twice, as `(= a a)`, repeats a
          // literal the clause has once.
          if terms.distinct.length < terms.length then p = step(clauseOf(terms.distinct), "factoring", Seq(p))
          var clause = terms.distinct
          for (n, pos) <- lits.distinct; m <- n do
            val l = find(m, pos).get
            for e <- litBridge(m, pos, l) do
              val r = rewriteLit(p, clause, term(n, pos), litTerm(l), e)
              p = r._1
              clause = r._2
          if clause.distinct.length < clause.length then p = step(clauseOf(clause.distinct), "factoring", Seq(p))
          Some(p)
        case None =>
          nodeOf(d.v) match
            case Ctor("pred", Vector(t0)) =>
              lNodes(int(t0)) match
                case Ctor("bterm", Vector(inner0)) if has(int(inner0), !d.pos) =>
                  // `(or (not F) F)`, the literal of the inner formula then
                  // rewritten to the term of the literal that stands for it.
                  val inner = int(inner0)
                  val p = excludedMiddle(f)
                  val x = if d.pos then s"(not $f)" else f
                  Some(litBridge(inner, !d.pos, find(inner, !d.pos).get).fold(p) { e =>
                    rewriteLit(p, Seq(s"(not $f)", f), x, litTerm(find(inner, !d.pos).get), e)._1
                  })
                case _ => None
            case _ => None

    /** A proof that the literal of node `n`, `pos` or negated, is the term of
     *  the literal `l` that stands for it, or none when they are the same term.
     */
    private def litBridge(n: Int, pos: Boolean, l: Lit): Option[String] =
      if pos then bridge(n, l)
      else
        val tn = lTerm(n)
        val inner =
          bridge(n, l.neg).map(b => step(s"(= (not $tn) (not ${litTerm(l.neg)}))", "cong", Seq(b), Seq(s"(not $tn)")))
        if !l.pos then inner
        else
          val tl = litTerm(l)
          val dn = step(s"(= (not (not $tl)) $tl)", "bool-double-not-elim", args = Seq(tl))
          Some(inner.fold(dn)(p => step(s"(= (not $tn) $tl)", "trans", Seq(p, dn))))

    /** `(or (not F) F)`, from the scope of `F`. */
    private def excludedMiddle(f: String): String =
      val h = id("h")
      out ++= s"(assume-push $h $f)\n"
      val p = id("p")
      pop(p, s"(=> $f $f)", h)
      step(s"(or (not $f) $f)", "implies_elim", Seq(p))

    // ----------------------------------------------------------------------
    // Lemmas of uninterpreted functions

    /** The term of a class: the lowered node it is. */
    private def cls(x: Int): String = lTerm(x)

    private def eq(a: Int, b: Int): String = s"(= ${cls(a)} ${cls(b)})"

    /** The lemma clause `c`, from a scope over the negation of each literal in
     *  which the equality proof derives `false`.
     */
    private def ufLemma(c: Vector[Lit], proof: Vector[Sexp], cert: Sexp): String =
      if compact then return compactUfLemma(c, proof, cert)
      val hyps = c.map(_.neg)
      val hypSteps = hyps.map { h =>
        val p = id("h")
        out ++= s"(assume-push $p ${litTerm(h)})\n"
        h -> p
      }
      def hypStep(r: Lit): String =
        hypSteps.collectFirst { case (`r`, p) => p }.getOrElse(throw Malformed(s"no hypothesis $r"))

      /** The proof of `a = b`, `a` and `b` the classes of an atom, from the
       *  hypothesis that is its variable, positive or negated.
       */
      def fromHyp(a: Int, b: Int, r: Lit): String =
        val (x, y) = ufAtoms.lift(r.v).flatten.getOrElse(throw Malformed(s"variable ${r.v} is no atom"))
        val h = hypStep(r)
        lNodes(meaningOf(r.v)) match
          case Ctor("eq" | "iff", Vector(m1, m2)) if r.pos =>
            val (n1, n2) = (int(m1), int(m2))
            if (a, b) == (n1, n2) then h
            else if (a, b) == (n2, n1) then step(eq(a, b), "symm", Seq(h))
            else throw Unsupported(s"atom ${(x, y)} is not its formula's equality")
          case _ if y == trueClass =>
            // A Boolean term as a formula: `x = true` when it holds, `x = false`
            // when it does not.
            val (rhs, rule) = if r.pos then (trueClass, "true_intro") else (falseClass, "false_intro")
            val p = step(eq(x, rhs), rule, Seq(h))
            if (a, b) == (x, rhs) then p else step(eq(a, b), "symm", Seq(p))
          case other => throw Unsupported(s"atom of $other")

      val done = ArrayBuffer.empty[(Int, Int, String)]
      for s <- proof do
        val proved = s match
          case Ctor("refl", Vector(a0)) =>
            val a = int(a0)
            (a, a, step(eq(a, a), "refl", args = Seq(cls(a))))
          case Ctor("given", Vector(a0, b0, r)) =>
            val (a, b) = (int(a0), int(b0))
            (a, b, fromHyp(a, b, lit(r)))
          case Ctor("symm", Vector(i)) =>
            val (a, b, p) = done(int(i))
            (b, a, step(eq(b, a), "symm", Seq(p)))
          case Ctor("trans", Vector(i, j)) =>
            val (a, _, p) = done(int(i))
            val (_, d, q) = done(int(j))
            (a, d, step(eq(a, d), "trans", Seq(p, q)))
          case Ctor("cong", Vector(a0, b0, f0, args0)) =>
            val (a, b) = (int(a0), int(b0))
            val (fa, fb, pf) = done(int(f0))
            val argProofs = ints(args0).map(done(_)._3)
            val p =
              if fa == fb then step(eq(a, b), "cong", argProofs, Seq(cls(a)))
              else step(eq(a, b), "ho_cong", pf +: argProofs)
            (a, b, p)
          case Ctor(name, _) => throw Unsupported(s"equality step $name")
        done += proved

      /** `false`, from the proof `p` of `a = b` and the hypothesis `r` that
       *  makes `a` and `b` distinct.
       */
      def apart(a: Int, b: Int, p: String, r: Lit): String =
        if r == trueLit then
          // `true = false`.
          val tf = if (a, b) == (trueClass, falseClass) then p else step(eq(trueClass, falseClass), "symm", Seq(p))
          val ft = step(eq(falseClass, trueClass), "symm", Seq(tf))
          step("false", "true_elim", Seq(ft))
        else
          val (x, y) = ufAtoms(r.v).get
          val h = hypStep(r)
          lNodes(meaningOf(r.v)) match
            case Ctor("eq" | "iff", Vector(m1, m2)) =>
              val (n1, n2) = (int(m1), int(m2))
              val q = if (a, b) == (n1, n2) then p else step(eq(n1, n2), "symm", Seq(p))
              step("false", "contra", Seq(q, h))
            case _ if y == trueClass =>
              val q = if (a, b) == (x, trueClass) then p else step(eq(x, trueClass), "symm", Seq(p))
              step("false", "contra", Seq(step(formula(r.v), "true_elim", Seq(q)), h))
            case other => throw Unsupported(s"atom of $other")

      val bottom = cert match
        case Ctor("disequal", Vector(p0, r0)) =>
          val (a, b, p) = done(int(p0))
          apart(a, b, p, lit(r0))
        case Ctor("apart", Vector(left, right, r0)) =>
          // `s = t = u = s2` under the hypothesis `t = u` of the first literal.
          val (t, s, pl) = done(int(left))
          val (u, s2, pr) = done(int(right))
          val tu = fromHyp(t, u, c.head.neg)
          val st = step(eq(s, t), "symm", Seq(pl))
          apart(s, s2, step(eq(s, s2), "trans", Seq(st, tu, pr)), lit(r0))
        case Ctor("equal", Vector(p0)) =>
          // The first literal holds, against the hypothesis of its negation.
          val (a, b, p) = done(int(p0))
          val l = c.head
          val h = hypStep(l.neg)
          lNodes(meaningOf(l.v)) match
            case Ctor("eq" | "iff", Vector(m1, m2)) =>
              val (n1, n2) = (int(m1), int(m2))
              val q = if (a, b) == (n1, n2) then p else step(eq(n1, n2), "symm", Seq(p))
              step("false", "contra", Seq(q, h))
            case _ =>
              val (x, _) = ufAtoms(l.v).get
              val q = if (a, b) == (x, trueClass) then p else step(eq(x, trueClass), "symm", Seq(p))
              step("false", "contra", Seq(step(formula(l.v), "true_elim", Seq(q)), h))
        case Ctor(name, _) => throw Unsupported(s"$name certificate")

      // Discharge the hypotheses, innermost first. Each implication is a
      // `define` over the previous one, so that the scopes stay linear.
      var body = bottom
      var concl = "false"
      for (h, _) <- hypSteps.reverse do
        if !compact then concl = define(id("i").drop(1), s"(=> ${litTerm(h)} $concl)")
        val p = id("p")
        pop(p, s"$concl", body)
        body = p
      if hyps.isEmpty then return bottom
      val hypTerms = hyps.map(litTerm)
      val negAnd = if hyps.length == 1 then s"(not ${hypTerms.head})" else hypTerms.mkString("(not (and ", " ", "))")
      val scoped = step(negAnd, "process_scope", Seq(body), Seq("false"))
      // `(or (not H₁) … (not Hₙ))`, then each `(not (not F))` resolved to `F`.
      val split =
        if hyps.length == 1 then scoped
        else step(hypTerms.map(h => s"(not $h)").mkString("(or ", " ", ")"), "not_and", Seq(scoped))
      val doubles = c.filter(_.pos)
      if doubles.isEmpty then split
      else if compact then
        // `vik_rup` reads `(not (not F))` as `F`.
        step(clauseTerm(c), "vik_rup", Seq(split), Seq(clauseTerm(c)))
      else
        val premises = split +: doubles.map(l => excludedMiddle(formula(l.v)))
        // In the clause, `(not (not F))`: the pivot `(not F)` is negative.
        step(
          clauseTerm(c),
          "chain_m_resolution",
          premises,
          Seq(
            clauseTerm(c),
            doubles.map(_ => "false").mkString("(@list ", " ", ")"),
            doubles.map(l => s"(not ${formula(l.v)})").mkString("(@list ", " ", ")")
          )
        )

    /** The lemma clause `c` by the rule `vik_uf` of `Vik.eo`, whose steps
     *  replay the equality proof under the negations of its literals.
     */
    private def compactUfLemma(c: Vector[Lit], proof: Vector[Sexp], cert: Sexp): String =
      val steps = ArrayBuffer.empty[String]
      def add(s: String): Int =
        steps += s
        steps.length - 1

      /** The equality of each step: its sides, by class, and its index. */
      val done = ArrayBuffer.empty[(Int, Int, Int)]
      def oriented(a: Int, b: Int, e: (Int, Int, Int)): Int =
        if (e._1, e._2) == (a, b) then e._3
        else if (e._2, e._1) == (a, b) then add(s"(vik.symm ${e._3})")
        else throw Malformed(s"step of ${(e._1, e._2)} for ${(a, b)}")

      /** `a = b` from the hypothesis `r`, the negation of a literal of `c`. */
      def fromHyp(a: Int, b: Int, r: Lit): Int =
        val i = c.indexOf(r.neg)
        if i < 0 then throw Malformed(s"no hypothesis $r")
        val (x, y) = ufAtoms.lift(r.v).flatten.getOrElse(throw Malformed(s"variable ${r.v} is no atom"))
        val natural = lNodes(meaningOf(r.v)) match
          case Ctor("eq" | "iff", Vector(m1, m2)) if r.pos => (int(m1), int(m2))
          case _ if y == trueClass => (x, if r.pos then trueClass else falseClass)
          case other => throw Unsupported(s"atom of $other")
        oriented(a, b, (natural._1, natural._2, add(s"(vik.given $i)")))

      for s <- proof do
        done +=
          (s match
            case Ctor("refl", Vector(a0)) =>
              val a = int(a0)
              (a, a, add(s"(vik.refl ${cls(a)})"))
            case Ctor("given", Vector(a0, b0, r)) =>
              val (a, b) = (int(a0), int(b0))
              (a, b, fromHyp(a, b, lit(r)))
            case Ctor("symm", Vector(i)) =>
              val (a, b, k) = done(int(i))
              (b, a, add(s"(vik.symm $k)"))
            case Ctor("trans", Vector(i, j)) =>
              val (a, _, k) = done(int(i))
              val (_, d, m) = done(int(j))
              (a, d, add(s"(vik.trans $k $m)"))
            case Ctor("cong", Vector(a0, b0, f0, args0)) =>
              val (a, b) = (int(a0), int(b0))
              val f = done(int(f0))._3
              (a, b, add(ints(args0).map(done(_)._3).mkString(s"(vik.cong $f (@list ", " ", "))")))
            case Ctor(name, _) => throw Unsupported(s"equality step $name"))

      // The last step contradicts the hypotheses, in either orientation.
      def last(k: Int): Unit = if k != steps.length - 1 then add(s"(vik.symm $k)")
      cert match
        case Ctor("disequal", Vector(p0, _)) => last(done(int(p0))._3)
        case Ctor("equal", Vector(p0)) => last(done(int(p0))._3)
        case Ctor("apart", Vector(left, right, _)) =>
          // `s = t = u = s2` under the hypothesis `t = u` of the first literal.
          val (t, _, l) = done(int(left))
          val (u, _, r) = done(int(right))
          val st = add(s"(vik.symm $l)")
          val tu = fromHyp(t, u, c.head.neg)
          add(s"(vik.trans ${add(s"(vik.trans $st $tu)")} $r)")
        case Ctor(name, _) => throw Unsupported(s"$name certificate")
      val d = clauseTerm(c)
      step(d, "vik_uf", args = Seq(d, steps.mkString("(@list ", " ", ")")))

    // ----------------------------------------------------------------------
    // Derived clauses

    /** The clause `c` by reverse unit propagation over `hints`: with every
     *  literal of `c` false, the hints in turn propagate until one is false.
     *  The resolution chain starts from that conflict and resolves, in reverse,
     *  each propagated literal it contains with the hint that propagated it.
     */
    private def derived(c: Vector[Lit], hints: Seq[Int]): String =
      // The value of each formula, by its node: literals of the same formula
      // are the same in CPC.
      def key(l: Lit): String = formula(l.v)
      val value = HashMap.empty[String, Boolean]
      def holds(l: Lit): Option[Boolean] = value.get(key(l)).map(_ == l.pos)
      for l <- c do value(key(l)) = !l.pos
      val reasons = ArrayBuffer.empty[(Lit, Int)]
      var conflict = -1
      val it = hints.iterator
      while conflict < 0 && it.hasNext do
        val h = it.next()
        val clause = proved(h)._2
        if !clause.exists(holds(_).contains(true)) then
          clause.filter(holds(_).isEmpty).distinctBy(l => (key(l), l.pos)) match
            case Vector() => conflict = h
            case Vector(u) =>
              value(key(u)) = u.pos
              reasons += u -> h
            case _ => ()
      if conflict < 0 then
        throw Malformed(s"hints ${hints.mkString(" ")} do not refute ${c.map(litTerm).mkString(" ")}")
      // Resolve backwards from the conflict.
      val premises = ArrayBuffer(proved(conflict)._1)
      val pols = ArrayBuffer.empty[String]
      val pivots = ArrayBuffer.empty[String]
      val current = HashSet.from(proved(conflict)._2.map(l => (key(l), l.pos)))
      for (u, h) <- reasons.reverseIterator do
        val m = key(u)
        if current.contains((m, !u.pos)) then
          current -= ((m, !u.pos))
          for l <- proved(h)._2 if !(key(l) == m && l.pos == u.pos) do current += ((key(l), l.pos))
          premises += proved(h)._1
          // The pivot as it occurs in the accumulated clause: `¬u`.
          pols += (if u.pos then "false" else "true")
          pivots += m
      val text = clauseTerm(c)
      // A long clause is a `define`: the step gives it twice.
      val concl = if c.length > 8 then define(id("c").drop(1), text) else text
      if compact && premises.length > 1 then
        // The clauses resolution uses, in the order they propagate: the
        // reasons, then the conflict.
        return step(concl, "vik_rup", premises.tail.reverse.toSeq :+ premises.head, Seq(concl))
      if premises.length == 1 then
        // The conflict clause is the clause itself, up to order.
        if clauseTerm(proved(conflict)._2) == text then premises.head
        else step(concl, "reordering", premises.toSeq, Seq(concl))
      else
        step(
          concl,
          "chain_m_resolution",
          premises.toSeq,
          Seq(concl, pols.mkString("(@list ", " ", ")"), pivots.mkString("(@list ", " ", ")"))
        )
