package io.bovel.vik.proofs

import scala.collection.mutable.ArrayBuffer

import io.bovel.vik.Sexp
import io.bovel.vik.Sexp.{Atom, Lst}

/** Writes a certificate of Vik (`Session.proof`, see `ProofExport`) as a Lean
 *  file that `proofs/lean` checks: its sections as definitions read by `sexp%`,
 *  and the theorems that the lowered problem accepts the answer and, with the
 *  script, that no model of the script satisfies its assertions.
 *
 *  The kernel checks the derived steps, their justifications, the nodes of the
 *  script and the inputs of the lowering in slices, each a theorem of its own:
 *  it keeps the values it computes within a declaration, which on a large proof
 *  take more memory and stack than one check can have. The slices come from the
 *  certificate alone. [[LeanModules]] splits the file into modules checked in
 *  parallel, [[LeanNative]] makes it a file for `native_decide`.
 */
object Lean:

  /** Not a certificate this driver reads. */
  type Malformed = Sexp.Malformed
  def Malformed(message: String): Malformed = Sexp.Malformed(message)

  private val stepSlice = 250
  private val nodeSlice = 500
  private val inputSlice = 100

  /** The steps of the certificates of a slice of justifications: the kernel
   *  keeps about 5 MB per step until the end of a slice, so this bounds the
   *  memory of one.
   */
  private val justBudget = 400

  /** The literals a slice of derived steps visits, those of the steps and of
   *  their hints: the kernel takes about 4 ms and 0.5 MB for each.
   */
  private val rupBudget = 5000

  /** Large proofs, their terms and the kernel's checks, run past the
   *  elaborator's default limits.
   */
  private val options = "set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n"

  /** The Lean file of `certificate`, its definitions and theorems in the
   *  namespace `namespace`.
   */
  def apply(certificate: String, namespace: String): String =
    val sections = Sexp.sections(certificate)
    def section(name: String): Vector[Sexp] = sections.getOrElse(name, throw Malformed(s"no $name"))
    def field(name: String, f: String): Vector[Sexp] = section(name).collectFirst {
      case Lst(Vector(Atom(`f`), Lst(xs))) => xs
    }.getOrElse(throw Malformed(s"no list $f in $name"))
    val b = StringBuilder()
    b ++= s"import Vik\n\nnamespace $namespace\n\nopen Vik.Low Vik.Surf Vik.Clausal\n\n$options\n"
    b ++= definition("problem", "Problem", section("problem"))
    b ++= "\n"
    b ++= definition("answer", "Answer", section("answer"))
    b ++= "\n"
    b ++= accepted(field("answer", "steps"), field("answer", "justs"))
    if sections.contains("script") then
      b ++= "\n"
      b ++= definition("script", "Vik.Lower.SProblem", section("script"))
      b ++= "\n"
      b ++= definition("trace", "Vik.Lower.Trace", section("trace"))
      b ++= "\n"
      b ++= checked(field("script", "nodes").length, field("trace", "inputs").length)
    b ++= s"\nend $namespace\n"
    b.toString

  private def definition(name: String, tpe: String, fields: Vector[Sexp]): String =
    fields.mkString(s"noncomputable def $name : $tpe := sexp% \"(", "\n  ", ")\"\n")

  /** `[0, total)` in slices of `size`: their starts and lengths. */
  private def slices(total: Int, size: Int): List[(Int, Int)] = (0 until total by size).map(a =>
    (a, size min (total - a))
  ).toList

  /** Consecutive slices of items of the costs `costs`, each of at most
   *  `budget`, unless one item alone costs more, and of at most `size` items.
   */
  private def weightedSlices(costs: IndexedSeq[Int], budget: Int, size: Int): List[(Int, Int)] =
    val out = ArrayBuffer.empty[(Int, Int)]
    var a = 0
    while a < costs.length do
      var n = 1
      var w = costs(a)
      while a + n < costs.length && n < size && w + costs(a + n) <= budget do
        w += costs(a + n)
        n += 1
      out += ((a, n))
      a += n
    out.toList

  private def items(s: Sexp): Vector[Sexp] = Sexp.items(s)

  /** The cost of each derived step, the literals it and its hints visit. */
  private def rupCosts(steps: Vector[Sexp]): IndexedSeq[Int] =
    val clauses = steps.map(s => items(items(s)(1)).length)
    steps.map {
      case Lst(Vector(Atom("derived"), clause, hints)) =>
        items(clause).length + items(hints).map {
          case Atom(h) => clauses(h.toInt)
          case h => throw Malformed(s"not a hint: $h")
        }.sum
      case _ => 0
    }

  /** The cost of each justification, the steps of its certificate. */
  private def justCosts(justs: Vector[Sexp]): IndexedSeq[Int] = justs.map {
    case Lst(Vector(Atom("lia"), Lst(steps))) => steps.length
    case Atom("derived") => 0
    case _ => 1
  }

  private def accepted(steps: Vector[Sexp], justs: Vector[Sexp]): String =
    val ss = weightedSlices(rupCosts(steps), rupBudget, stepSlice)
    val js = weightedSlices(justCosts(justs), justBudget, stepSlice)
    val b = StringBuilder()
    b ++= "theorem acceptedBase : problem.acceptsBase answer = true := by decide +kernel\n"
    for (a, n) <- js do
      b ++= s"theorem acceptedJusts$a : problem.justsSlice answer $a $n = true := by decide +kernel\n"
    for (a, n) <- ss do
      b ++= s"theorem acceptedSteps$a : answer.rupSlice $a $n = true := by decide +kernel\n"
    val justChain = js.foldRight("(Problem.justsFrom_end problem answer (by decide +kernel))")((an, rest) =>
      s"(Problem.justsFrom_slice problem answer acceptedJusts${an._1}\n    $rest)"
    )
    val rupChain = ss.foldRight("(Answer.rupFrom_end answer (by decide +kernel))")((an, rest) =>
      s"(Answer.rupFrom_slice answer acceptedSteps${an._1}\n    $rest)"
    )
    b ++= "\ntheorem accepted : problem.accepts answer = true :=\n"
    b ++= s"  Problem.accepts_of_slices problem answer acceptedBase\n    $justChain\n    $rupChain\n"
    b.toString

  private def checked(nodes: Int, inputs: Int): String =
    val ns = slices(nodes, nodeSlice)
    val is = slices(inputs, inputSlice)
    val b = StringBuilder()
    b ++= "theorem checkedBase : trace.checkBase script problem answer = true := by decide +kernel\n"
    for (a, n) <- ns do
      b ++= s"theorem checkedNodes$a : trace.nodesSlice script problem $a $n = true := by decide +kernel\n"
    for (a, n) <- is do
      b ++= s"theorem checkedInputs$a : trace.inputsSlice script problem $a $n = true := by decide +kernel\n"
    val nodeChain =
      ns.foldRight("(Vik.Lower.Trace.nodesFrom_end script problem trace (by decide +kernel))")((an, rest) =>
        s"(Vik.Lower.Trace.nodesFrom_slice script problem trace checkedNodes${an._1}\n    $rest)"
      )
    val inputChain =
      is.foldRight("(Vik.Lower.Trace.inputsFrom_end script problem trace (by decide +kernel))")((an, rest) =>
        s"(Vik.Lower.Trace.inputsFrom_slice script problem trace checkedInputs${an._1}\n    $rest)"
      )
    b ++= "\ntheorem checked : trace.check script problem answer = true :=\n"
    b ++= s"  Vik.Lower.Trace.check_of_slices script problem trace checkedBase\n    $nodeChain\n    $inputChain\n"
    b ++= """|
       |/-- No model of the script satisfies its assertions. -/
       |theorem no_model {R U : Type} [Lean.Grind.Field R] [LE R] [LT R] [Std.IsLinearOrder R]
       |    [Std.LawfulOrderLT R] [Lean.Grind.OrderedRing R] [Lean.Grind.IsCharP R 0] (M : Vik.Surf.Model R U)
       |    (size : Val R U → Nat) (hL : script.Laws M size) (hfl : ∀ r : R, ∃ k : Int, Vik.Real.IsFloor r k)
       |    (h : ∀ a ∈ script.asserts, Vik.Surf.holds M.toInterp script.nodes a) : False :=
       |  Vik.Lower.Trace.unsat checked accepted M size hL hfl h
       |""".stripMargin
    b.toString
