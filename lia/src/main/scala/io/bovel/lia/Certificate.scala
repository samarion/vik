package io.bovel.lia

import scala.collection.mutable.{ArrayBuffer, HashMap}

/** Why some bounds of a [[Solver]] are inconsistent, as a cutting-planes
 *  derivation of `0 ≤ c` with `c < 0`: each node proves an inequality
 *  `Σ a·u ≤ c` over the solver's unknowns (the variables of [[Solver.newVar]];
 *  a slack stands for its expression), `c` possibly with an infinitesimal part
 *  (see [[Delta]]).
 *
 *    - `Hyp`: a bound asserted for `reason`, `x ≤ c` (`upper`) or `x ≥ c`,
 *      strict or not, on the expression `x` stands for. A negative reason is
 *      the hypothesis of an enclosing `Split`;
 *    - `Comb`: a combination of inequalities with non-negative factors;
 *    - `Round`: an inequality over integer unknowns, its right side rounded
 *      down to a value its left side takes (a multiple of the gcd of the
 *      coefficients);
 *    - `Split`: the expression `x` (integer valued) is at most `floor` or at
 *      least `ceil`, nothing lying in between, and both cases are refuted;
 *      `reason` is the reason of their hypotheses. With a disequality `x ≠ at`
 *      asserted for `except`, the value `at` may lie in between: the split of a
 *      disequality, its sides strict when `x` may be real (`x < at` or
 *      `x > at`, with `floor` and `ceil` both `at`).
 *
 *  Nodes are shared: a derived bound is the premise of many others.
 */
enum Certificate:
  case Hyp(reason: Int, x: Var, c: BigInt, strict: Boolean, upper: Boolean)
  case Comb(factors: Array[Rational], parts: Array[Certificate])
  case Round(of: Certificate)
  case Split(
      reason: Int,
      x: Var,
      floor: BigInt,
      ceil: BigInt,
      low: Certificate,
      high: Certificate,
      except: Int = -1,
      at: BigInt = 0,
      strict: Boolean = false
  )

object Certificate:
  /** `Σ coefs(u)·u ≤ rhs`. */
  final case class Inequality(coefs: Map[Var, Rational], rhs: Delta):
    override def toString: String =
      val lhs = if coefs.isEmpty then "0" else coefs.toList.sortBy(_._1).map((u, a) => s"${a}·u$u").mkString(" + ")
      s"$lhs ≤ $rhs"

  /** Checks certificates against the unknowns of a solver: `form(x)` is the
   *  expression `x` stands for over the unknowns, `isInteger(u)` whether the
   *  unknown is integer, `hyp(h)` whether the bound of a hypothesis with a
   *  non-negative reason is the one asserted for that reason (`None` if so),
   *  `distinct(reason, x, c)` whether `x ≠ c` is the disequality asserted for
   *  `reason`. What a node proves is kept for the next certificates, which
   *  share it.
   */
  final class Checker(
      form: Var => Map[Var, Rational],
      isInteger: Var => Boolean,
      hyp: Hyp => Option[String],
      distinct: (Int, Var, BigInt) => Option[String] = (_, _, _) => Some("no disequalities")
  ):
    /** What a node proves, the hypotheses of the enclosing splits it rests on,
     *  and the reasons of the others.
     */
    private final case class Proved(inequality: Inequality, open: Set[Hyp], reasons: Set[Int])

    private val memo = java.util.IdentityHashMap[Certificate, Proved]()
    private val forms = HashMap.empty[Var, Map[Var, Rational]]
    private def formOf(x: Var): Map[Var, Rational] = forms.getOrElseUpdate(x, form(x))

    /** Checks that `certificate` derives a contradiction from the hypotheses of
     *  the reasons `assumed` allows: `None` if so, what is wrong otherwise.
     */
    def check(certificate: Certificate, assumed: Int => Boolean): Option[String] =
      def fail(msg: String): Nothing = throw CheckFailed(msg)
      def side(h: Hyp): Inequality =
        val f = formOf(h.x)
        val d = Delta(Rational(h.c), if h.strict then Rational(if h.upper then -1 else 1) else Rational.zero)
        if h.upper then Inequality(f, d) else Inequality(f.view.mapValues(-_).toMap, -d)
      def children(c: Certificate): Iterator[Certificate] = c match
        case Comb(_, parts) => parts.iterator
        case Round(of) => Iterator(of)
        case s: Split => Iterator(s.low, s.high)
        case _ => Iterator.empty
      // Depth first, without the call stack: derivations run deep.
      def prove(c: Certificate): Proved =
        val known = memo.get(c)
        if known != null then known
        else
          val todo = ArrayBuffer(c)
          while todo.nonEmpty do
            val top = todo.last
            if memo.containsKey(top) then todo.remove(todo.length - 1)
            else
              val waiting = children(top).filter(!memo.containsKey(_)).toList
              if waiting.isEmpty then
                compute(top)
                todo.remove(todo.length - 1)
              else todo ++= waiting
          memo.get(c).nn
      // `c`, whose children are proved.
      def compute(c: Certificate): Proved =
        val p = c match
          case h: Hyp =>
            if h.reason >= 0 then
              hyp(h).foreach(e => fail(s"the hypothesis ${h.reason}: $e"))
              Proved(side(h), Set.empty, Set(h.reason))
            else Proved(side(h), Set(h), Set.empty)
          case Comb(factors, parts) =>
            if factors.length != parts.length then fail("a combination with as many factors as parts")
            val sum = HashMap.empty[Var, Rational]
            var rhs = Delta.zero
            var open = Set.empty[Hyp]
            var reasons = Set.empty[Int]
            for i <- parts.indices do
              val f = factors(i)
              if f.signum < 0 then fail(s"a negative factor $f")
              val q = prove(parts(i))
              open ++= q.open
              reasons ++= q.reasons
              for (u, a) <- q.inequality.coefs do
                val s = sum.getOrElse(u, Rational.zero) + a * f
                if s.isZero then sum.remove(u) else sum(u) = s
              rhs = rhs + q.inequality.rhs * f
            Proved(Inequality(sum.toMap, rhs), open, reasons)
          case Round(of) =>
            val q = prove(of)
            val coefs = q.inequality.coefs
            for u <- coefs.keys if !isInteger(u) do fail(s"rounding over the real u$u")
            if coefs.isEmpty then q
            else
              // Σ a·u = r·Σ n·u with integers n of gcd 1: the sum takes the multiples of r only.
              val l = coefs.valuesIterator.foldLeft(BigInt(1))((l, a) => l / (l gcd a.den) * a.den)
              val g = coefs.valuesIterator.foldLeft(BigInt(0))((g, a) => g gcd (a.num * (l / a.den)))
              val r = Rational(g, l)
              q.copy(inequality = Inequality(coefs, Delta(r * Rational((q.inequality.rhs / r).floor))))
          case Split(reason, x, floor, top, low, high, except, at, strict) =>
            if except >= 0 then distinct(except, x, at).foreach(e => fail(s"the disequality $except: $e"))
            if strict then
              // `x < at` or `x > at`: only `at` lies in between, which the disequality excludes.
              if except < 0 || floor != at || top != at then fail(s"a strict split at $floor and $top")
            else
              val f = formOf(x)
              for u <- f.keys if !isInteger(u) do fail(s"a split over the real u$u")
              if f.valuesIterator.exists(!_.isInteger) then fail("a split over an expression with fractions")
              // The expression's values are the multiples of the gcd of its coefficients: none strictly
              // between, or `at` alone when the disequality excludes it.
              val g = f.valuesIterator.foldLeft(BigInt(0))(_ gcd _.num)
              if g == 0 then fail("a split over a constant")
              val next = (floor - floor.mod(g)) + g // the least multiple of g above `floor`
              val left = if except >= 0 && next == at then next + g else next
              if left < top then fail(s"the split at $floor and $top leaves $left out")
            def discharge(q: Proved, upper: Boolean, c: BigInt): Set[Hyp] =
              val (mine, others) = q.open.partition(_.reason == reason)
              for h <- mine do
                if h.x != x || h.upper != upper || h.c != c || h.strict != strict then
                  fail(s"the hypothesis $h of the split")
              others
            val lo = prove(low)
            val hi = prove(high)
            for q <- Seq(lo, hi) do
              if !contradiction(q.inequality) then fail(s"a side of a split proves ${q.inequality}")
            Proved(
              Inequality(Map.empty, Delta(Rational(-1))),
              discharge(lo, true, floor) ++ discharge(hi, false, top),
              lo.reasons ++ hi.reasons ++ (if except >= 0 then Set(except) else Set.empty)
            )
        memo.put(c, p)
        p
      try
        val p = prove(certificate)
        if p.open.nonEmpty then Some(s"hypotheses of no split: ${p.open.mkString(", ")}")
        else if !contradiction(p.inequality) then Some(s"no contradiction: ${p.inequality}")
        else p.reasons.find(!assumed(_)).map(r => s"the hypothesis $r is not one of the lemma")
      catch case CheckFailed(msg) => Some(msg)

  private def contradiction(i: Inequality): Boolean = i.coefs.isEmpty && i.rhs < Delta.zero

  private final case class CheckFailed(msg: String) extends Exception(msg, null, false, false)
