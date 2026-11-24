package io.bovel.vik.proofs

import scala.collection.mutable.{ArrayBuffer, HashMap}

import io.bovel.vik.Sexp
import io.bovel.vik.Sexp.{Atom, Lst}

/** Writes a CPC proof of Vik (`Session.cpcProof`) as a Lean file that
 *  `proofs/lean` checks with `Vik.Cpc.Proof.check` (`Vik/Cpc/Check.lean`): the
 *  script, from the certificate's `script` section, the proof's terms as nodes
 *  after the script's, and its commands, each step with the node it concludes.
 *  Compact proofs give no conclusions, so this computes each as Ethos does,
 *  over terms as Ethos reads them: `(= a b c)` as a conjunction of pairs, `=>`
 *  to the right, `xor` to the left.
 *
 *  An `assume` and a `vik_lower` step relate two terms that differ in form, the
 *  script's assertion (with its `let`s) and its CPC term, or a term and its
 *  lowering: the file gives the equivalences between them, which the checker
 *  checks child by child.
 */
object CpcLean:

  /** Not a proof this driver reads. */
  type Malformed = Sexp.Malformed
  def Malformed(message: String): Malformed = Sexp.Malformed(message)

  /** A proof beyond what the Lean checker covers. */
  final class Unsupported(message: String) extends Exception(message)

  /** Writes `Cnnnnn.lean`, and `native/Cnnnnn.lean`, for each `Cnnnnn.cpc` of a
   *  directory with its certificate `Cnnnnn.cert` (`CpcCorpus` with `CPC_CERTS`
   *  set): `proofs/runMain io.bovel.vik.proofs.CpcLean <dir> <out>`. Prints a
   *  line per proof: its name and `written` or why not.
   */
  def main(args: Array[String]): Unit =
    import java.nio.file.{Files, Path}
    import scala.jdk.CollectionConverters.*
    val dir = Path.of(args(0))
    val out = Files.createDirectories(Path.of(args(1)))
    val native = Files.createDirectories(out.resolve("native"))
    val names = Files.list(dir).iterator.asScala.map(_.getFileName.toString).filter(_.endsWith(".cpc"))
      .map(_.stripSuffix(".cpc")).toList.sorted
    for name <- names do
      val outcome =
        try
          val cert = Files.readString(dir.resolve(s"$name.cert"))
          val cpc = Files.readString(dir.resolve(s"$name.cpc"))
          Files.writeString(out.resolve(s"$name.lean"), CpcLean(cert, cpc, s"Vik.Cpc.Exported.$name"))
          Files.writeString(native.resolve(s"$name.lean"), CpcLean(cert, cpc, s"Vik.Cpc.Exported.$name", true))
          "written"
        catch case e: Exception => s"${e.getClass.getSimpleName}: ${String.valueOf(e.getMessage).take(200)}"
      println(s"$name\t$outcome")

  private val options = "set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n"

  /** The Lean file of the CPC proof `cpc` of `certificate`, in `namespace`,
   *  checked by `native_decide` when `native`, otherwise by the kernel.
   */
  def apply(certificate: String, cpc: String, namespace: String, native: Boolean = false): String =
    val sections = Sexp.sections(certificate)
    val script = sections.getOrElse("script", throw Malformed("no script"))
    val proof = Reader(script).read(cpc)
    val nc = if native then "" else "noncomputable "
    val check = if native then "native_decide" else "decide +kernel"
    val b = StringBuilder()
    b ++= s"import Vik\n\nnamespace $namespace\n\n$options"
    if native then b ++= "set_option vik.sexp.chunk 1000\n"
    b ++= "\n"
    b ++= script.mkString(s"${nc}def script : Vik.Lower.SProblem := sexp% \"(", "\n  ", ")\"\n\n")
    b ++= s"${nc}def proof : Vik.Cpc.Proof := sexp% \"$proof\"\n\n"
    b ++= s"theorem checked : proof.check script = true := by $check\n"
    b ++= """|
       |/-- No model of the script satisfies its assertions. -/
       |theorem no_model {R U : Type} [Lean.Grind.Field R] [LE R] [LT R] [Std.IsLinearOrder R]
       |    [Std.LawfulOrderLT R] [Lean.Grind.OrderedRing R] [Lean.Grind.IsCharP R 0] (M : Vik.Surf.Model R U)
       |    (hM : M.Sound script.sig) (hD : ∀ d ∈ script.defs, d.Holds script.sig M)
       |    (h : ∀ a ∈ script.asserts, Vik.Surf.holds M.toInterp script.nodes a) : False :=
       |  Vik.Cpc.Proof.unsat checked M hM hD h
       |""".stripMargin
    b ++= s"\nend $namespace\n"
    b.toString

  // --------------------------------------------------------------------------
  // Nodes

  /** A node of `Vik.Surf.SNode`, of the shapes CPC proofs use; `Raw` for the
   *  others, which only the script has.
   */
  private enum N:
    case Const(k: Int)
    case App(f: Int, as: Vector[Int])
    case Tt
    case Ff
    case Not(a: Int)

    /** `and`, `or`, `implies`, `iff`, `xor`, `eq` or `distinct`. */
    case Nary(op: String, as: Vector[Int])
    case Ite(c: Int, a: Int, b: Int)
    case LetIn(bs: Vector[Int], body: Int)
    case Bound(d: Int)
    case Raw(text: String)

    def sexp: String = this match
      case Const(k) => s"(const $k)"
      case App(f, as) => s"(app $f (${as.mkString(" ")}))"
      case Tt => "tt"
      case Ff => "ff"
      case Not(a) => s"(not $a)"
      case Nary(op, as) => s"($op (${as.mkString(" ")}))"
      case Ite(c, a, b) => s"(ite $c $a $b)"
      case LetIn(bs, body) => s"(letIn (${bs.mkString(" ")}) $body)"
      case Bound(d) => s"(bound $d)"
      case Raw(t) => t

  private def num(s: Sexp): Int = s match
    case Atom(a) if a.nonEmpty && a.forall(_.isDigit) => a.toInt
    case _ => throw Malformed(s"not a number: ${s.toString.take(100)}")

  private def items(s: Sexp): Vector[Sexp] = Sexp.items(s)

  private def ints(s: Sexp): Vector[Int] = items(s).map(num)

  private val naryOps = Set("and", "or", "implies", "iff", "xor", "eq", "distinct")

  private def node(s: Sexp): N = s match
    case Lst(Vector(Atom("const"), k)) => N.Const(num(k))
    case Lst(Vector(Atom("app"), f, as)) => N.App(num(f), ints(as))
    case Atom("tt") => N.Tt
    case Atom("ff") => N.Ff
    case Lst(Vector(Atom("not"), a)) => N.Not(num(a))
    case Lst(Vector(Atom(op), as)) if naryOps(op) => N.Nary(op, ints(as))
    case Lst(Vector(Atom("ite"), c, a, b)) => N.Ite(num(c), num(a), num(b))
    case Lst(Vector(Atom("letIn"), bs, body)) => N.LetIn(ints(bs), num(body))
    case Lst(Vector(Atom("bound"), d)) => N.Bound(num(d))
    case s => N.Raw(s.toString)

  private final class Reader(script: Vector[Sexp]):
    private def field(f: String): Sexp = script.collectFirst { case Lst(Vector(Atom(`f`), v)) => v }
      .getOrElse(throw Malformed(s"no $f in the script"))

    private val (sigSorts, decls) = field("sig") match
      case Lst(Vector(sorts, ds)) => (items(sorts), ints(ds))
      case s => throw Malformed(s"not a signature: ${s.toString.take(100)}")
    private val asserts = ints(field("asserts"))

    /** The definitions: parameters, body nodes and root, by symbol. */
    private val defs = items(field("defs")).map {
      case Lst(Vector(f, ps, ns, r)) => num(f) -> (ints(ps), items(ns).map(node), num(r))
      case d => throw Malformed(s"not a definition: ${d.toString.take(100)}")
    }.toMap

    private val boolSort = sigSorts.indexOf(Atom("bool"))
    if boolSort < 0 then throw Malformed("no Boolean sort")

    // The table: the script's nodes, then the proof's.
    private val nodes = ArrayBuffer.from(items(field("nodes")).map(node))
    private val sorts = ArrayBuffer.from(ints(field("sortOf")))
    private val scriptSize = nodes.length
    if sorts.length != scriptSize then throw Malformed("the script's sorts and nodes differ in number")
    private val index = HashMap.empty[N, Int]
    for (n, i) <- nodes.zipWithIndex do
      n match
        case _: N.Raw => ()
        case _ => index.getOrElseUpdate(n, i)

    private def isBool(i: Int): Boolean = sigSorts(sorts(i)) == Atom("bool")

    private def sortOf(n: N): Int = n match
      case N.Const(k) => decls.lift(k).getOrElse(throw Malformed(s"no symbol $k"))
      case N.App(f, _) => sigSorts(sorts(f)) match
          case Lst(Vector(Atom("fn"), _, r)) => num(r)
          case s => throw Malformed(s"applies a node of sort $s")
      case N.Ite(_, a, _) => sorts(a)
      case N.LetIn(_, b) => sorts(b)
      case N.Bound(d) => sorts(d)
      case N.Raw(t) => throw Unsupported(s"node $t")
      case _ => boolSort

    private def mk(n: N): Int = index.getOrElseUpdate(
      n, {
        nodes += n
        sorts += sortOf(n)
        nodes.length - 1
      }
    )

    private lazy val tt = mk(N.Tt)
    private lazy val ff = mk(N.Ff)
    private def not(a: Int): Int = mk(N.Not(a))
    private def or(as: Seq[Int]): Int = mk(N.Nary("or", as.toVector))
    private def eq(a: Int, b: Int): Int = mk(N.Nary(if isBool(a) then "iff" else "eq", Vector(a, b)))
    private def implies(a: Int, b: Int): Int = mk(N.Nary("implies", Vector(a, b)))

    private def eqOf(i: Int): Option[(Int, Int)] = nodes(i) match
      case N.Nary("eq" | "iff", Vector(a, b)) => Some((a, b))
      case _ => None

    private def notOf(i: Int): Option[Int] = nodes(i) match
      case N.Not(a) => Some(a)
      case _ => None

    private def clause(i: Int): Vector[Int] = nodes(i) match
      case N.Nary("or", as) => as
      case N.Ff => Vector()
      case _ => Vector(i)

    /** `Ctx.sgn`: a literal as an atom and the value that makes it true. */
    private def sgn(l: Int): (Int, Boolean) = notOf(l) match
      case Some(a) =>
        notOf(a) match
          case Some(b) => sgn(b)
          case None => (a, false)
      case None => (l, true)

    // ------------------------------------------------------------------------
    // Terms, as Ethos reads them

    private val defined = HashMap.empty[String, Int]

    /** The definitions with parameters, which Ethos expands: their parameters
     *  and bodies.
     */
    private val macros = HashMap.empty[String, (Vector[String], Sexp)]

    private def term(s: Sexp, env: Map[String, Int] = Map.empty): Int = s match
      case Atom("true") => tt
      case Atom("false") => ff
      case Atom(a) =>
        env.getOrElse(
          a,
          defined.getOrElse(
            a,
            if a.startsWith("x") && a.drop(1).nonEmpty && a.drop(1).forall(_.isDigit) then
              mk(N.Const(a.drop(1).toInt))
            else throw Malformed(s"unknown symbol $a")
          )
        )
      case Lst(Atom(op) +: args) if args.nonEmpty && !env.contains(op) && macros.contains(op) =>
        val (ps, body) = macros(op)
        if ps.length != args.length then throw Malformed(s"$op applied to ${args.length} arguments")
        term(body, ps.zip(args.map(term(_, env))).toMap)
      case Lst(Atom(op) +: args) if args.nonEmpty =>
        lazy val ts = args.map(term(_, env))
        op match
          case "not" if args.length == 1 => not(ts(0))
          case "and" | "or" | "distinct" => mk(N.Nary(op, ts))
          case "=>" => ts.init.foldRight(ts.last)(implies)
          case "xor" => ts.tail.foldLeft(ts.head)((a, b) => mk(N.Nary("xor", Vector(a, b))))
          case "=" if args.length == 2 => eq(ts(0), ts(1))
          case "=" => mk(N.Nary("and", ts.sliding(2).map(p => eq(p(0), p(1))).toVector))
          case "ite" if args.length == 3 => mk(N.Ite(ts(0), ts(1), ts(2)))
          case _ => mk(N.App(term(Atom(op), env), ts))
      case _ => throw Malformed(s"not a term: ${s.toString.take(100)}")

    // ------------------------------------------------------------------------
    // Equivalences (`Ctx.eqvPairs`)

    private val eqvs = ArrayBuffer.empty[String]
    private val eqvIndex = HashMap.empty[(Int, Int), Int]

    private def pairsOf(as: Vector[Int]): Vector[(Int, Int)] =
      as.indices.flatMap(i => as.drop(i + 1).map(as(i) -> _)).toVector

    private def chainPairs(eqOp: String, as: Vector[Int], es: Vector[Int]): Option[Vector[(Int, Int)]] =
      if as.length != es.length + 1 then None
      else
        val ps = as.sliding(2).toVector.zip(es).map { case (ab, e) =>
          nodes(e) match
            case N.Nary(`eqOp`, Vector(p, q)) => Some(Vector(ab(0) -> p, ab(1) -> q))
            case _ => None
        }
        if ps.forall(_.isDefined) then Some(ps.flatMap(_.get)) else None

    private def implPairs(as: Vector[Int], y: Int): Option[Vector[(Int, Int)]] = (as, nodes(y)) match
      case (Vector(a, b), N.Nary("implies", Vector(p, q))) => Some(Vector(a -> p, b -> q))
      case (a +: rest, N.Nary("implies", Vector(p, z))) if rest.length >= 2 => implPairs(rest, z).map((a -> p) +: _)
      case _ => None

    private def xorPairs(as: Vector[Int], y: Int): Option[Vector[(Int, Int)]] = (as, nodes(y)) match
      case (Vector(b, a), N.Nary("xor", Vector(p, q))) => Some(Vector(a -> p, b -> q))
      case (b +: rest, N.Nary("xor", Vector(z, q))) if rest.length >= 2 => xorPairs(rest, z).map((b -> q) +: _)
      case _ => None

    private def kids(n: N): Option[(String, Vector[Int])] = n match
      case N.App(f, as) => Some(("app", f +: as))
      case N.Not(a) => Some(("not", Vector(a)))
      case N.Nary(op, as) => Some((op, as))
      case N.Ite(c, a, b) => Some(("ite", Vector(c, a, b)))
      case _ => None

    private def samePairs(n: N, m: N): Option[Vector[(Int, Int)]] = (kids(n), kids(m)) match
      case (Some((k, as)), Some((k2, bs))) if k == k2 && as.length == bs.length => Some(as.zip(bs))
      case _ => None

    private def eqvPairs(x: Int, y: Int): Option[Vector[(Int, Int)]] = (nodes(x), nodes(y)) match
      case (N.LetIn(_, b), _) => Some(Vector(b -> y))
      case (N.Bound(d), _) => Some(Vector(d -> y))
      case (N.Nary("and", Vector()), N.Tt) => Some(Vector())
      case (N.Nary("or", Vector()), N.Ff) => Some(Vector())
      case (N.Nary("eq", as), N.Nary("and", es)) if as.length >= 3 => chainPairs("eq", as, es)
      case (N.Nary("iff", as), N.Nary("and", es)) if as.length >= 3 => chainPairs("iff", as, es)
      case (N.Nary("implies", as), _) if as.length >= 3 => implPairs(as, y)
      case (N.Nary("xor", as), _) if as.length >= 3 => xorPairs(as.reverse, y)
      case (N.Nary("xor", Vector(a, b)), N.Not(e)) =>
        nodes(e) match
          case N.Nary("iff", Vector(p, q)) => Some(Vector(a -> p, b -> q))
          case _ => None
      case (N.Nary("distinct", as), N.Nary("and", es)) =>
        val ps = pairsOf(as)
        if ps.length != es.length then None
        else
          val ds = es.map(e => notOf(e).flatMap(eqOf))
          if ds.forall(_.isDefined) then
            Some(ps.zip(ds.map(_.get)).flatMap { case ((a, b), (p, q)) =>
              Vector(a -> p, b -> q)
            })
          else None
      case (n, m) => samePairs(n, m)

    /** `Ctx.defUse`: node `x` as the use of a definition, its symbol and
     *  arguments.
     */
    private def defUse(x: Int): Option[(Int, Vector[Int])] = (nodes(x) match
      case N.Const(k) => Some((k, Vector()))
      case N.App(f, as) =>
        nodes(f) match
          case N.Const(k) => Some((k, as))
          case _ => None
      case _ => None
    ).filter((k, _) => defs.contains(k))

    private def rename(n: N, m: Int => Int): N = n match
      case N.App(f, as) => N.App(m(f), as.map(m))
      case N.Not(a) => N.Not(m(a))
      case N.Nary(op, as) => N.Nary(op, as.map(m))
      case N.Ite(c, a, b) => N.Ite(m(c), m(a), m(b))
      case N.LetIn(bs, b) => N.LetIn(bs.map(m), m(b))
      case N.Bound(d) => N.Bound(m(d))
      case N.Raw(t) => throw Unsupported(s"node $t in a definition")
      case n => n

    /** The instance of the body of definition `k` on the arguments `as`
     *  (`SDef.instOk`): the node of each of the body's nodes.
     */
    private def instance(k: Int, as: Vector[Int]): Vector[Int] =
      val (ps, ns, _) = defs(k)
      val ms = ArrayBuffer.empty[Int]
      for n <- ns do
        ms +=
          (n match
            case N.Const(p) if ps.contains(p) => as(ps.indexOf(p))
            case n => mk(rename(n, ms)))
      ms.toVector

    /** The equivalence of `x` and `y`, `None` when they are one node. */
    private def eqv(x: Int, y: Int): Option[Int] =
      if x == y then None
      else
        Some(eqvIndex.getOrElse(
          (x, y), {
            val (ps, ms) = defUse(x) match
              case Some((k, as)) =>
                val ms = instance(k, as)
                (Vector(ms(defs(k)._3) -> y), ms)
              case None =>
                val ps = eqvPairs(x, y).getOrElse(
                  throw Unsupported(s"no equivalence of ${nodes(x).sexp} and ${nodes(y).sexp}")
                )
                (ps, Vector())
            val hs = ps.flatMap((p, q) => eqv(p, q))
            eqvs += s"($x $y (${hs.mkString(" ")}) (${ms.mkString(" ")}))"
            eqvIndex((x, y)) = eqvs.length - 1
            eqvs.length - 1
          }
        ))

    private def opt(e: Option[Int]): String = e.fold("none")(k => s"(some $k)")

    // ------------------------------------------------------------------------
    // Conclusions

    private def arg(args: Vector[Sexp], i: Int): Sexp = args.lift(i).getOrElse(throw Malformed("missing argument"))

    private def listOf(s: Sexp): Vector[Sexp] = s match
      case Lst(Atom("@list") +: xs) => xs
      case Atom("@list.nil") => Vector()
      case _ => throw Malformed(s"not a list: ${s.toString.take(100)}")

    private def andOf(i: Int): Vector[Int] = nodes(i) match
      case N.Nary("and", as) => as
      case n => throw Malformed(s"not a conjunction: ${n.sexp}")

    private def orOf(i: Int): Vector[Int] = nodes(i) match
      case N.Nary("or", as) => as
      case n => throw Malformed(s"not a disjunction: ${n.sexp}")

    private def iffOf(i: Int): (Int, Int) = nodes(i) match
      case N.Nary("iff", Vector(a, b)) => (a, b)
      case n => throw Malformed(s"not an equivalence: ${n.sexp}")

    private def iteOf(i: Int): (Int, Int, Int) = nodes(i) match
      case N.Ite(c, a, b) => (c, a, b)
      case n => throw Malformed(s"not an ite: ${n.sexp}")

    private def eqOrFail(i: Int): (Int, Int) = eqOf(i).getOrElse(throw Malformed(s"not an equality: ${nodes(i).sexp}"))

    /** The Lean rule of a step and its conclusion. */
    private def rule(name: String, ps: Vector[Int], args: Vector[Sexp]): (String, Int) =
      def a(i: Int) = term(arg(args, i))
      def idx(i: Int) = num(arg(args, i))
      def taut(k: String, d: Int) = (s"(taut $k)", d)
      name match
        case "refl" => taut("refl", eq(a(0), a(0)))
        case "true_elim" =>
          val (f, t) = iffOf(ps(0))
          if t != tt then throw Malformed("true_elim of no (= F true)")
          ("trueElim", f)
        case "cnf_and_pos" =>
          val f = a(0)
          taut("andPos", or(Vector(not(f), andOf(f)(idx(1)))))
        case "cnf_and_neg" =>
          val f = a(0)
          taut("andNeg", or(f +: andOf(f).map(not)))
        case "cnf_or_pos" =>
          val f = a(0)
          taut("orPos", or(not(f) +: orOf(f)))
        case "cnf_or_neg" =>
          val f = a(0)
          taut("orNeg", or(Vector(f, not(orOf(f)(idx(1))))))
        case "cnf_equiv_pos1" | "cnf_equiv_pos2" | "cnf_equiv_neg1" | "cnf_equiv_neg2" =>
          val e = a(0)
          val (x, y) = iffOf(e)
          name match
            case "cnf_equiv_pos1" => taut("equivPos1", or(Vector(not(e), not(x), y)))
            case "cnf_equiv_pos2" => taut("equivPos2", or(Vector(not(e), x, not(y))))
            case "cnf_equiv_neg1" => taut("equivNeg1", or(Vector(e, x, y)))
            case _ => taut("equivNeg2", or(Vector(e, not(x), not(y))))
        case "cnf_ite_pos1" | "cnf_ite_pos2" | "cnf_ite_pos3" | "cnf_ite_neg1" | "cnf_ite_neg2" | "cnf_ite_neg3" =>
          val e = a(0)
          val (c, x, y) = iteOf(e)
          name match
            case "cnf_ite_pos1" => taut("itePos1", or(Vector(not(e), not(c), x)))
            case "cnf_ite_pos2" => taut("itePos2", or(Vector(not(e), c, y)))
            case "cnf_ite_pos3" => taut("itePos3", or(Vector(not(e), x, y)))
            case "cnf_ite_neg1" => taut("iteNeg1", or(Vector(e, not(c), not(x))))
            case "cnf_ite_neg2" => taut("iteNeg2", or(Vector(e, c, not(y))))
            case _ => taut("iteNeg3", or(Vector(e, not(x), not(y))))
        case "ite_eq" =>
          val k = a(0)
          val (c, x, y) = iteOf(k)
          taut("iteEq", mk(N.Ite(c, eq(k, x), eq(k, y))))
        case "evaluate" =>
          val t = a(0)
          def value(i: Int): Boolean = nodes(i) match
            case N.Tt => true
            case N.Ff => false
            case N.Not(x) => !value(x)
            case n => throw Unsupported(s"evaluate of ${n.sexp}")
          taut("evaluate", eq(t, if value(t) then tt else ff))
        case "bool-double-not-elim" =>
          val x = a(0)
          taut("doubleNot", eq(not(not(x)), x))
        case "bool-impl-elim" =>
          val (x, y) = (a(0), a(1))
          taut("implElim", eq(implies(x, y), or(Vector(not(x), y))))
        case "eq-refl" =>
          val x = a(0)
          taut("eqRefl", eq(eq(x, x), tt))
        case "chain_m_resolution" =>
          val pols = listOf(arg(args, 1)).map {
            case Atom("true") => "true"
            case Atom("false") => "false"
            case s => throw Malformed(s"not a polarity: $s")
          }
          val lits = listOf(arg(args, 2)).map(term(_))
          (s"(chain (${pols.mkString(" ")}) (${lits.mkString(" ")}))", a(0))
        case "reordering" => ("weaken", a(0))
        case "factoring" =>
          val ls = clause(ps(0)).distinct
          ("weaken", if ls.length == 1 then ls(0) else if ls.isEmpty then ff else or(ls))
        case "and_elim" => ("andElim", andOf(ps(0))(idx(0)))
        // One premise too makes a one-element `and`, as Ethos reads a premise list.
        case "and_intro" => ("andIntro", mk(N.Nary("and", ps)))
        case "implies_elim" =>
          nodes(ps(0)) match
            case N.Nary("implies", Vector(x, y)) => ("impliesElim", or(Vector(not(x), y)))
            case n => throw Malformed(s"implies_elim of ${n.sexp}")
        case "eq_resolve" =>
          val (f, g) = iffOf(ps(1))
          if f != ps(0) then throw Malformed("eq_resolve of mismatched premises")
          ("eqResolve", g)
        case "symm" =>
          nodes(ps(0)) match
            case N.Not(e) =>
              val (x, y) = eqOrFail(e)
              ("symm", not(eq(y, x)))
            case _ =>
              val (x, y) = eqOrFail(ps(0))
              ("symm", eq(y, x))
        case "trans" =>
          val es = ps.map(eqOrFail)
          ("trans", eq(es.head._1, es.last._2))
        case "cong" =>
          val t = a(0)
          val rhs = ps.map(p => eqOrFail(p)._2)
          val u = nodes(t) match
            case N.App(f, as) if as.length == rhs.length => mk(N.App(f, rhs))
            case N.Not(_) if rhs.length == 1 => not(rhs(0))
            case N.Nary(op, as) if as.length == rhs.length => mk(N.Nary(op, rhs))
            case N.Ite(_, _, _) if rhs.length == 3 => mk(N.Ite(rhs(0), rhs(1), rhs(2)))
            case n => throw Unsupported(s"cong over ${n.sexp} with ${rhs.length} premises")
          ("cong", eq(t, u))
        case "vik_rup" => ("rup", a(0))
        case "vik_lower" =>
          val d = a(0)
          (s"(lower ${opt(eqv(ps(0), d))})", d)
        case "vik_uf" =>
          val d = a(0)
          (s"(uf (${ufSteps(d, listOf(arg(args, 1))).mkString(" ")}))", d)
        case _ => throw Unsupported(s"rule $name")

    /** The steps of a `vik_uf` lemma `d`, as `Ctx.ufSteps` reads them. */
    private def ufSteps(d: Int, steps: Vector[Sexp]): Vector[String] =
      val hyps = clause(d).map { l =>
        val (a, p) = sgn(l); (a, !p)
      }
      val done = ArrayBuffer.empty[(Int, Int)]
      def hypEq(h: (Int, Boolean)): (Int, Int) =
        if h._2 then eqOf(h._1).getOrElse((h._1, tt))
        else if isBool(h._1) then (h._1, ff)
        else throw Malformed("a hypothesis of no equality")
      steps.map { s =>
        val (text, e) = s match
          case Lst(Vector(Atom("vik.refl"), t)) =>
            val x = term(t)
            (s"(refl $x)", (x, x))
          case Lst(Vector(Atom("vik.given"), i)) => (s"(given ${num(i)})", hypEq(hyps(num(i))))
          case Lst(Vector(Atom("vik.symm"), j)) =>
            val (a, b) = done(num(j))
            (s"(symm ${num(j)})", (b, a))
          case Lst(Vector(Atom("vik.trans"), j, k)) =>
            val (a, b) = done(num(j))
            val (b2, c) = done(num(k))
            if b != b2 then throw Malformed("vik.trans of equalities that do not chain")
            (s"(trans ${num(j)} ${num(k)})", (a, c))
          case Lst(Vector(Atom("vik.cong"), j, js)) =>
            val (f, g) = done(num(j))
            val ks = listOf(js).map(num)
            val l = mk(N.App(f, ks.map(done(_)._1)))
            val r = mk(N.App(g, ks.map(done(_)._2)))
            (s"(cong ${num(j)} (${ks.mkString(" ")}) $l $r)", (l, r))
          case _ => throw Malformed(s"not a vik_uf step: ${s.toString.take(100)}")
        done += e
        text
      }

    // ------------------------------------------------------------------------
    // Commands

    def read(cpc: String): String =
      val cmds = ArrayBuffer.empty[String]
      val ids = HashMap.empty[String, Int]
      val facts = ArrayBuffer.empty[Int]
      var stack = List.empty[(Int, Int)]
      def add(id: String, d: Int): Unit =
        ids(id) = facts.length
        facts += d
      def prem(p: Sexp): Int = p match
        case Atom(id) => ids.getOrElse(id, throw Malformed(s"no premise $id"))
        case _ => throw Malformed(s"not a premise: $p")

      /** The `:premises` and `:args` of a step. */
      def attrs(xs: Vector[Sexp]): (String, Vector[Int], Vector[Sexp]) =
        var rule = ""
        var ps = Vector.empty[Int]
        var as = Vector.empty[Sexp]
        xs.grouped(2).foreach {
          case Vector(Atom(":rule"), Atom(r)) => rule = r
          case Vector(Atom(":premises"), Lst(xs)) => ps = xs.map(prem)
          case Vector(Atom(":args"), Lst(xs)) => as = xs
          case other => throw Malformed(s"not an attribute: ${other.mkString(" ").take(100)}")
        }
        (rule, ps, as)
      // A step's conclusion term, when given, comes before its attributes.
      def stepParts(xs: Vector[Sexp]): (Option[Sexp], Vector[Sexp]) = xs match
        case (a @ Atom(k)) +: rest if k.startsWith(":") => (None, xs)
        case t +: rest => (Some(t), rest)
        case _ => (None, xs)
      for c <- items(Sexp.parse(s"($cpc)")) do
        c match
          case Lst(Vector(Atom("declare-sort"), _, _)) => ()
          case Lst(Vector(Atom("declare-const"), _, _)) => ()
          case Lst(Atom("define") +: Atom(name) +: Lst(Vector()) +: t +: _) => defined(name) = term(t)
          case Lst(Atom("define") +: Atom(name) +: Lst(ps) +: t +: _) =>
            macros(name) = (
              ps.map {
                case Lst(Vector(Atom(p), _)) => p
                case p => throw Malformed(s"not a parameter: $p")
              },
              t
            )
          case Lst(Vector(Atom("assume"), Atom(id), t)) =>
            val d = term(t)
            val i = id.stripPrefix("@a").toIntOption.getOrElse(throw Malformed(s"not an assertion: $id"))
            val a = asserts.lift(i).getOrElse(throw Malformed(s"no assertion $i"))
            cmds += s"(step ((assume $a ${opt(eqv(a, d))}) () $d))"
            add(id, d)
          case Lst(Vector(Atom("assume-push"), Atom(id), t)) =>
            val f = term(t)
            stack = (f, facts.length) :: stack
            cmds += s"(push $f)"
            add(id, f)
          case Lst(Atom("step-pop") +: Atom(id) +: rest) =>
            val (_, attrs1) = stepParts(rest)
            val (r, ps, _) = attrs(attrs1)
            if r != "scope" || ps.length != 1 then throw Unsupported(s"step-pop of $r")
            val (f, m) = stack.headOption.getOrElse(throw Malformed("step-pop with no scope"))
            stack = stack.tail
            val d = implies(f, facts(ps(0)))
            cmds += s"(pop ${ps(0)} $d)"
            facts.dropRightInPlace(facts.length - m)
            add(id, d)
          case Lst(Atom("step") +: Atom(id) +: rest) =>
            val (stated, as) = stepParts(rest)
            val (r, ps, args) = attrs(as)
            val (leanRule, d) = rule(r, ps.map(facts), args)
            for t <- stated do
              if term(t) != d then throw Malformed(s"$id concludes ${nodes(term(t)).sexp}, not ${nodes(d).sexp}")
            cmds += s"(step ($leanRule (${ps.mkString(" ")}) $d))"
            add(id, d)
          case other => throw Unsupported(s"command ${other.toString.take(100)}")
      if stack.nonEmpty then throw Malformed("a scope left open")
      val (t, f) = (tt, ff)
      val extra = nodes.drop(scriptSize)
      val b = StringBuilder()
      b ++= "((extra ("
      b ++= extra.map(_.sexp).mkString(" ")
      b ++= s"))\n  (sorts (${sorts.drop(scriptSize).mkString(" ")}))\n  (eqvs ("
      b ++= eqvs.mkString(" ")
      b ++= s"))\n  (tt $t) (ff $f)\n  (cmds (\n    "
      b ++= cmds.mkString("\n    ")
      b ++= ")))"
      b.toString
