package io.bovel.vik

import scala.collection.mutable.{ArrayBuffer, HashMap, HashSet}

import io.bovel.smtlib.{ArithOp, BvCmpOp, BvOp}
import io.bovel.smtlib as s2
import Formula.*
import Term.*

/** Lowers a surface script (`io.bovel.smtlib`) to the solver's language: the
 *  one function from the language the parser reads to the trees the solver
 *  plays — a [[Session]] applies it, and `io.bovel.vik.lower` prints its
 *  result. This is where the surface language's conveniences are compiled away
 *  and where the fragment line is drawn, with a message:
 *    - `let` names become substitutions; `define-fun` macros are expanded at
 *      their uses;
 *    - `+`, `-` and `*` by a literal become the linear normal form; rational
 *      literals and divisions become defined `Real` constants; `div`, `mod`,
 *      `abs` and nonlinear multiplication are rejected;
 *    - chained `=`, `distinct` and comparisons become pairwise bounds on
 *      numbers and bit-vectors, equalities and disequalities elsewhere;
 *    - a term-level `ite` becomes a fresh constant with two defining assertions
 *      placed before the assertion using it;
 *    - `select` is application, `store` an application of the array sort's
 *      `.store!N` symbol, which the solver's array lemmas recognize;
 *    - bit-vectors go to linear integer arithmetic: an `n`-bit term is an
 *      integer in `[0, 2^n)`, a sort `(_ BitVec n)` the sort of that range
 *      ([[Sort.IntRange]], whose terms the solver holds to it: no range is
 *      asserted here), and each operation a linear relation between its
 *      arguments, its result and fresh bounded integers — `bvadd` and friends
 *      through an overflow count `k` (`value = r + 2^n × k`), divisions, shifts
 *      and extractions through `x = d × q + r`, the signed comparisons and
 *      `sign_extend` through the sign bit (`x = u + 2^(n−1) × s`).
 *      Multiplication, division and shifts by a variable, and the other bitwise
 *      operations would need bit-blasting: rejected
 *      ([[io.bovel.smtlib.Unsupported]]).
 */
object Lowering:
  def apply(script: s2.Script): Script = Script(Lowerer().commands(script.commands))

/** One lowering: the declared sorts, the macros, the fresh constants of the
 *  assertion being lowered and their defining assertions.
 */
private final class Lowerer:
  private enum Value: // a `let`-bound value
    case T(term: Term, sort: s2.Sort)
    case F(formula: Formula)

  private type Env = Map[String, Value]

  private val functions = HashMap.empty[String, s2.Sort] // declared symbols, with their whole function sort
  private val macros = HashMap.empty[String, (List[(String, s2.Sort)], s2.Sort, s2.Term | s2.Formula)]

  // A declaration or a definition goes with its level's `pop`, unless `:global-declarations` is true
  // (issue 40): one list of undos per open level, as the parser keeps.
  private var globalDeclarations = false
  private val scopes = ArrayBuffer.empty[ArrayBuffer[() => Unit]]

  /** Records, before `map(key)` is set, how to restore it at the level's pop.
   */
  private def undoable[V](map: scala.collection.mutable.Map[String, V], key: String): Unit =
    if scopes.nonEmpty && !globalDeclarations then
      val previous = map.get(key)
      scopes.last += (() => previous.fold(map -= key)(v => map(key) = v))

  private var fresh = 0

  /** Whether a name is one of the lowering's own (or the solver's): a test for
   *  the session.
   */
  def minted(name: String): Boolean = Names.isOurs(name)

  /** A name of the lowering's own, `.prefix!N` ([[Names]]): no script symbol is
   *  one.
   */
  private def freshName(prefix: String): String =
    fresh += 1
    Names.minted(prefix, fresh)

  /** Refuses a script's declaration of a symbol that SMT-LIB reserves for the
   *  solver, and VIK takes for its own ([[Names]]): one starting with `.`. A
   *  `let` may bind such a name, which it does not declare.
   */
  private def reserve(name: String): Unit =
    if Names.isOurs(name) then
      throw s2.Smt2Error(s"$name: SMT-LIB reserves the symbols starting with `.` for the solver")
  // The fresh constants and the assertions defining them, which go out before the assertion they were made
  // for, in the order they were made: each constant is declared right before its definitions. The solver
  // meets a bit-vector constant's range at its declaration, and the search follows the order it meets things in.
  // `auxiliary`: a constant that is a bit of a term (see bits), whose atoms the search decides last.
  private val pending = ArrayBuffer.empty[Command]
  private def introduce(name: String, sort: Sort, auxiliary: Boolean = false): Unit =
    pending += Command.DeclareFun(name, Nil, sort, auxiliary)
  private def define(definition: Formula): Unit = pending += Command.Assert(definition)

  /** What the lowering minted, by what it was minted for. An entry stands for
   *  constants whose defining assertions went out at its level, and that
   *  level's `pop` retires them: found here after it, a constant would be
   *  unconstrained, and `(= a 0.5)` would accept any `a`. So an entry goes with
   *  the level that made it, under `:global-declarations` too (the constants
   *  stay declared then, their definitions do not), and the entries of the
   *  outer levels stay. Dropping one is always sound, the next use minting and
   *  defining again, and an entry is never replaced: a `pop` only ever has
   *  entries to drop, nothing to restore.
   */
  private final class Memo[K, V]:
    private val entries = HashMap.empty[K, V]
    def get(key: K): Option[V] = entries.get(key)
    def contains(key: K): Boolean = entries.contains(key)
    def apply(key: K): V = entries(key)
    def getOrElseUpdate(key: K, value: => V): V =
      entries.getOrElseUpdate(
        key, {
          if scopes.nonEmpty then scopes.last += (() => entries -= key)
          value
        }
      )
    def update(key: K, value: V): Unit = getOrElseUpdate(key, value)
    def clear(): Unit = entries.clear()

  /** The lowering of a bit-vector operation, once per level: the second
   *  occurrence of `bvmul 4 (bvadd 1 x)` in an assertion gets the constants of
   *  the first, not fresh ones defined the same way. Two chains of fresh
   *  constants are the same value only by an integer argument over `2^n` (`x +
   *  1 = r + 2^32 k` with `r` in `[0, 2^32)` pins `r`, but the solver has to
   *  see it), which branch and bound walked for minutes on
   *  `x0 = 4(x+1) ∧ x0 ≠ 4(x+1)`; one chain makes the equality syntactic. Keyed
   *  on the operation and its lowered operands.
   */
  private val loweredOperations = Memo[(String, List[Term], List[BigInt]), Term]()
  private val loweredDivisions = Memo[(Term, BigInt, BigInt), (Term, Term)]()
  private val loweredSignedDivisions = Memo[(Term, Int, BigInt, Boolean), (Term, Term)]()
  private val loweredBits = Memo[(Term, Int), IndexedSeq[Formula]]()
  private val bitConstants = Memo[Formula, Term]() // a bit back to the `{0, 1}` constant that carries it

  private def clearMemos(): Unit =
    rationals.clear()
    rationalProducts.clear()
    loweredOperations.clear()
    loweredDivisions.clear()
    quotients.clear()
    loweredSignedDivisions.clear()
    loweredBits.clear()
    bitConstants.clear()

  def commands(cs: List[s2.Command]): List[Command] = cs.flatMap(command)

  /** The value of a surface term or formula under `model`, as SMT-LIB writes it
   *  at the term's sort. Every construct is computed here from the model's
   *  values of the declared symbols: the lowering's fresh constants have no
   *  value in a model, so a value read through the lowered term stopped at them
   *  — `is_int` false, `floor!8` or `q!2` printed as a value, a select at a
   *  minted index (issues 45 to 48).
   */
  def evaluate(item: s2.Term | s2.Formula, model: Model): String = item match
    case f: s2.Formula => if truth(f, model, Scope.empty) then "true" else "false"
    case s2.Term.Const(name) if functions.get(name).flatMap(_.arrow).exists(_._1.nonEmpty) =>
      // A function symbol: its graph as a lambda, as cvc5 answers (issue 50).
      val Some((argSorts, result)) = functions(name).arrow: @unchecked
      val f =
        model.functions.getOrElse(name, Model.Function(argSorts.map(lowered), lowered(result), Nil, Const("@default")))
      val (params, body) = graph(f, argSorts, result)
      s"(lambda ($params) $body)"
    case t: s2.Term => written(eval(t, model, Scope.empty), sortOf(t, Map.empty))

  /** A declared function's graph as an `ite` chain over parameters `x!i`: the
   *  parameters' declarations and the body — a model's `define-fun`, a
   *  `get-value`'s `lambda`.
   */
  def graph(f: Model.Function, argSorts: List[s2.Sort], result: s2.Sort): (String, String) =
    val params = argSorts.zipWithIndex.map((s, i) => s"(x!$i ${s.text})").mkString(" ")
    val body = f.rows.foldRight(written(f.default, result)) { case ((args, r), els) =>
      val cond = args.zip(argSorts).zipWithIndex.map { case ((a, s), i) => s"(= x!$i ${written(a, s)})" } match
        case single :: Nil => single
        case cs => cs.mkString("(and ", " ", ")")
      s"(ite $cond ${written(r, result)} $els)"
    }
    (params, body)

  /** The `let`-bound names and macro parameters in scope while evaluating:
   *  their values, and their sorts for [[sortOf]].
   */
  private final case class Scope(values: Map[String, Term], sorts: Env):
    def bound(name: String, value: Term, sort: s2.Sort): Scope =
      val typed = if sort == s2.Sort.Bool then Value.F(True) else Value.T(Const(name), sort)
      Scope(values + (name -> value), sorts + (name -> typed))
  private object Scope:
    val empty: Scope = Scope(Map.empty, Map.empty)

  private def eval(t: s2.Term, model: Model, scope: Scope): Term = t match
    case s2.Term.Numeral(v) => Num(v)
    case s2.Term.Decimal(unscaled, scale) => Model.rationalTerm(io.bovel.lia.Rational(unscaled, BigInt(10).pow(scale)))
    case s2.Term.Bits(v, _) => Num(v)
    case s2.Term.Const(name) =>
      scope.values.get(name) match
        case Some(v) => v
        case None =>
          macros.get(name) match
            case Some((Nil, _, body)) => eval(body, model, Scope.empty)
            case _ => model.value(Const(name))
    case s2.Term.App(s2.Term.Const(name), args) if macros.contains(name) && !scope.values.contains(name) =>
      // The body sees its parameters and the declarations, never the caller's bindings (issue 10).
      val (params, _, body) = macros(name)
      if params.length != args.length then throw s2.Smt2Error(s"$name expects ${params.length} arguments")
      val inner = params.zip(args).foldLeft(Scope.empty) { case (inner, ((p, sort), a)) =>
        inner.bound(p, eval(a, model, scope), sort)
      }
      eval(body, model, inner)
    // A declared function's graph, a constructor, a selector, a tester, an array read: the model's.
    case s2.Term.App(fun, args) => model.value(App(eval(fun, model, scope), args.map(eval(_, model, scope))))
    case s2.Term.ArithApp(op, args) =>
      val values = args.map(a => rational(eval(a, model, scope)))
      op match
        case ArithOp.Add => number(values.reduce(_ + _))
        case ArithOp.Sub => number(values.reduce(_ - _))
        case ArithOp.Neg => number(-values.head)
        case ArithOp.Mul => number(values.reduce(_ * _))
        case ArithOp.Div => number(values.reduce(_ / _)) // a zero divisor is refused before this, by the lowering
        case ArithOp.ToReal => number(values.head)
        case ArithOp.ToInt => Num(values.head.floor)
        case ArithOp.Abs => Num(integer(eval(args.head, model, scope)).abs)
        case ArithOp.IntDiv | ArithOp.Mod =>
          // As SMT-LIB defines them: the remainder is in `[0, |b|)`.
          val (a, b) = (integer(eval(args.head, model, scope)), args.tail.map(d => integer(eval(d, model, scope))))
          if b.exists(_.signum == 0) then throw s2.Unsupported(s"${op.name} by zero is not supported")
          if op == ArithOp.Mod then Num(a.mod(b.head.abs))
          else Num(b.foldLeft(a)((n, d) => (n - n.mod(d.abs)) / d))
    case s2.Term.BvApp(op, args) =>
      val widths = args.map(a =>
        sortOf(a, scope.sorts) match
          case s2.Sort.BitVec(w) => w
          case _ => 0 // the integer of `int_to_bv`
      )
      Num(bitVector(op, args.map(a => integer(eval(a, model, scope))), widths))
    case s2.Term.Select(array, index) => Model.select(eval(array, model, scope), eval(index, model, scope))
    case s2.Term.Store(array, index, value) =>
      Model.store(eval(array, model, scope), eval(index, model, scope), eval(value, model, scope))
    case s2.Term.ConstArray(sort, value) => Model.constArray(lowered(sort), eval(value, model, scope))
    case s2.Term.MapArray(_, params, body, arrays) =>
      // The operator sees the elements and the declarations, never the bindings around the map.
      Model.mapArrays(
        lowered(sortOf(t, scope.sorts)),
        arrays.map(eval(_, model, scope)),
        elements =>
          eval(
            body,
            model,
            params.zip(elements).foldLeft(Scope.empty) { case (inner, ((p, sort), e)) => inner.bound(p, e, sort) }
          )
      )
    case s2.Term.Ite(c, thn, els) => if truth(c, model, scope) then eval(thn, model, scope) else eval(els, model, scope)
    case s2.Term.Let(bindings, body) => eval(body, model, bindAll(bindings, model, scope))
    case s2.Term.Bool(f) => Term.boolean(if truth(f, model, scope) then True else False)

  private def eval(body: s2.Term | s2.Formula, model: Model, scope: Scope): Term = body match
    case t: s2.Term => eval(t, model, scope)
    case f: s2.Formula => Term.boolean(if truth(f, model, scope) then True else False)

  /** The bindings of a `let`, each valued outside them all. */
  private def bindAll(bindings: List[(String, s2.Term | s2.Formula)], model: Model, scope: Scope): Scope =
    bindings.foldLeft(scope) { case (inner, (name, value)) =>
      value match
        case t: s2.Term => inner.bound(name, eval(t, model, scope), sortOf(t, scope.sorts))
        case f: s2.Formula => inner.bound(name, eval(f, model, scope), s2.Sort.Bool)
    }

  private def truth(f: s2.Formula, model: Model, scope: Scope): Boolean = f match
    case s2.Formula.True => true
    case s2.Formula.False => false
    case s2.Formula.Not(a) => !truth(a, model, scope)
    case s2.Formula.And(as) => as.forall(truth(_, model, scope))
    case s2.Formula.Or(as) => as.exists(truth(_, model, scope))
    case s2.Formula.Implies(as) => as.map(truth(_, model, scope)).reduceRight((a, b) => !a || b)
    case s2.Formula.Xor(as) => as.map(truth(_, model, scope)).reduceLeft(_ != _)
    case s2.Formula.Iff(as) =>
      val values = as.map(truth(_, model, scope))
      values.forall(_ == values.head)
    case s2.Formula.Eq(as) =>
      val values = as.map(eval(_, model, scope))
      values.zip(values.tail).forall((a, b) => Model.same(a, b, sizeOf))
    case s2.Formula.Distinct(as) =>
      val values = as.map(eval(_, model, scope))
      values.zipWithIndex.forall((a, i) => values.drop(i + 1).forall(b => !Model.same(a, b, sizeOf)))
    case s2.Formula.Cmp(op, as) =>
      val values = as.map(a => rational(eval(a, model, scope)))
      values.zip(values.tail).forall((a, b) =>
        op match
          case s2.CmpOp.Le => a <= b
          case s2.CmpOp.Lt => a < b
          case s2.CmpOp.Ge => a >= b
          case s2.CmpOp.Gt => a > b
      )
    case s2.Formula.BvCmp(op, l, r) =>
      val m = modulus(width(l, scope.sorts))
      def read(t: s2.Term): BigInt =
        val v = integer(eval(t, model, scope))
        if op.signed && v >= m / 2 then v - m else v
      val (a, b) = (read(l), read(r))
      op match
        case BvCmpOp.Ult | BvCmpOp.Slt => a < b
        case BvCmpOp.Ule | BvCmpOp.Sle => a <= b
        case BvCmpOp.Ugt | BvCmpOp.Sgt => a > b
        case BvCmpOp.Uge | BvCmpOp.Sge => a >= b
    case s2.Formula.Ite(c, t, e) => if truth(c, model, scope) then truth(t, model, scope) else truth(e, model, scope)
    case s2.Formula.IsConstructor(constructor, arg) =>
      eval(arg, model, scope) match
        case App(Const(c), _) => c == constructor
        case Const(c) => c == constructor
        case _ => false
    case s2.Formula.IsInt(arg) => rational(eval(arg, model, scope)).isInteger
    case s2.Formula.Let(bindings, body) => truth(body, model, bindAll(bindings, model, scope))
    case s2.Formula.Pred(t) => eval(t, model, scope) == Bool(True)

  private def rational(value: Term): io.bovel.lia.Rational = value match
    case Num(v) => io.bovel.lia.Rational(v)
    case App(Const("/"), List(Num(p), Num(q))) => io.bovel.lia.Rational(p) / io.bovel.lia.Rational(q)
    case other => throw s2.Smt2Error(s"not a number: $other")

  private def integer(value: Term): BigInt = value match
    case Num(v) => v
    case other => throw s2.Smt2Error(s"not a bit-vector: $other")

  private def number(r: io.bovel.lia.Rational): Term = Model.rationalTerm(r)

  /** A bit-vector operation on values, as SMT-LIB defines it — the divisions by
   *  zero included: `bvudiv` by zero is all ones, `bvurem` by zero the
   *  dividend, and the signed ones follow from those.
   */
  private def bitVector(op: BvOp, values: List[BigInt], widths: List[Int]): BigInt =
    val w = widths.headOption.getOrElse(0)
    val m = modulus(w)
    def signed(v: BigInt): BigInt = if v >= m / 2 then v - m else v
    def unsigned(v: BigInt): BigInt = v.mod(m)
    def udiv(a: BigInt, b: BigInt): BigInt = if b.signum == 0 then m - 1 else a / b
    def urem(a: BigInt, b: BigInt): BigInt = if b.signum == 0 then a else a % b
    val a = values.head
    lazy val b = values(1)
    lazy val sa = signed(a)
    lazy val sb = signed(b)
    op match
      case BvOp.Add => values.reduce(_ + _).mod(m)
      case BvOp.Sub => values.reduce(_ - _).mod(m)
      case BvOp.Neg => (-a).mod(m)
      case BvOp.Not => m - 1 - a
      case BvOp.Mul => values.reduce(_ * _).mod(m)
      case BvOp.And => values.reduce(_ & _)
      case BvOp.Or => values.reduce(_ | _)
      case BvOp.Xor => values.reduce(_ ^ _)
      case BvOp.Nand => m - 1 - (a & b)
      case BvOp.Nor => m - 1 - (a | b)
      case BvOp.Xnor => m - 1 - (a ^ b)
      case BvOp.Comp => if a == b then BigInt(1) else BigInt(0)
      case BvOp.Shl => if b >= w then BigInt(0) else (a << b.toInt).mod(m)
      case BvOp.Lshr => if b >= w then BigInt(0) else a >> b.toInt
      case BvOp.Ashr => if b >= w then (if sa.signum < 0 then m - 1 else BigInt(0)) else unsigned(sa >> b.toInt)
      case BvOp.Udiv => udiv(a, b)
      case BvOp.Urem => urem(a, b)
      case BvOp.Sdiv =>
        if sa.signum >= 0 && sb.signum >= 0 then udiv(a, b)
        else if sa.signum < 0 && sb.signum >= 0 then unsigned(-udiv(unsigned(-sa), b))
        else if sa.signum >= 0 then unsigned(-udiv(a, unsigned(-sb)))
        else udiv(unsigned(-sa), unsigned(-sb))
      case BvOp.Srem =>
        if sa.signum >= 0 && sb.signum >= 0 then urem(a, b)
        else if sa.signum < 0 && sb.signum >= 0 then unsigned(-urem(unsigned(-sa), b))
        else if sa.signum >= 0 then urem(a, unsigned(-sb))
        else unsigned(-urem(unsigned(-sa), unsigned(-sb)))
      case BvOp.Smod =>
        val u = urem(unsigned(sa.abs), unsigned(sb.abs))
        if u.signum == 0 || (sa.signum >= 0 && sb.signum >= 0) then u
        else if sa.signum < 0 && sb.signum >= 0 then unsigned(-u + sb)
        else if sa.signum >= 0 then unsigned(u + sb)
        else unsigned(-u)
      case BvOp.Concat => values.zip(widths).foldLeft(BigInt(0)) { case (acc, (v, wi)) => (acc << wi) + v }
      case BvOp.UbvToInt => a
      case BvOp.SbvToInt => sa
      case BvOp.IntToBv(n) => a.mod(modulus(n))
      case BvOp.Extract(i, j) => (a >> j) & (modulus(i - j + 1) - 1)
      case BvOp.ZeroExtend(_) => a
      case BvOp.SignExtend(k) => sa.mod(modulus(w + k))
      case BvOp.Repeat(k) => (1 to k).foldLeft(BigInt(0))((acc, _) => (acc << w) + a)
      case BvOp.RotateLeft(k) =>
        val r = k % w
        ((a << r) | (a >> (w - r))).mod(m)
      case BvOp.RotateRight(k) =>
        val r = k % w
        ((a >> r) | (a << (w - r))).mod(m)

  /** The model with the lowering's rational constants valued, and the constants
   *  `definitions` define — a query's, for the session to value the lowered
   *  items of a lowered `get-value`.
   */
  def fold(model: Model, definitions: List[Formula]): Model =
    val withRationals = rationalValues.foldLeft(model) {
      case (m, (Const(name), (p, q))) =>
        val value = Model.rationalTerm(io.bovel.lia.Rational(p) / io.bovel.lia.Rational(q))
        m.copy(constants = m.constants + (name -> value))
      case (m, _) => m
    }
    definitions.foldLeft(withRationals)((m, d) => m.defined(d, minted))

  /** A value as the script writes one of `sort`: a bit-vector in binary, as z3
   *  and cvc5 write it (`(_ bv1 4)` says the same and reads oddly), a real as a
   *  decimal, an array as its stores over a constant array of the script's
   *  sort, a constructor's arguments at its fields' sorts (issue 47).
   */
  def written(value: Term, sort: s2.Sort): String = (value, sort) match
    case (Num(v), s2.Sort.BitVec(w)) => s2.sexpr.SExpr.SBits(v.mod(modulus(w)), w, hexadecimal = false).toString
    case (Num(v), s2.Sort.Int) => s2.Printer.print(s2.Term.Numeral(v))
    // A real as a decimal, `4.0` and `(/ 9.0 2.0)`, as z3 writes one: a numeral is an integer where the
    // logic has both, and a definition `(define-fun e () Real 0)` is a sort mismatch to z3.
    case (Num(v), s2.Sort.Real) => decimal(v)
    case (App(Const("/"), List(Num(p), Num(q))), s2.Sort.Real) => s"(/ ${decimal(p)} ${decimal(q)})"
    case (Bool(f), s2.Sort.Bool) => if f == True then "true" else "false"
    case (App(Const("store"), List(a, i, v)), s2.Sort.Array(index, element)) =>
      s"(store ${written(a, sort)} ${written(i, index)} ${written(v, element)})"
    case (App(Const(name), List(d)), s2.Sort.Array(_, element)) if name.startsWith("(as const ") =>
      s"((as const ${sort.text}) ${written(d, element)})"
    case (App(Const(c), args), s2.Sort.Named(_))
        if functions.get(c).flatMap(_.arrow).exists(_._1.length == args.length) =>
      val fields = functions(c).arrow.get._1
      s"(${Printer.symbol(c)} ${args.zip(fields).map(written).mkString(" ")})"
    case (Const(c), _) => Printer.symbol(c) // a nullary constructor, an abstract element
    case _ => Printer.print(value)

  private def decimal(v: BigInt): String = if v.signum < 0 then s"(- ${-v}.0)" else s"$v.0"

  /** The sort the script declared `name` at, for the model's text; none for a
   *  name the script never declared, the lowering's own among them.
   */
  def declaredSort(name: String): Option[s2.Sort] = if minted(name) then None else functions.get(name)

  /** A sort of the script as the solver knows it ([[Sort]]). An array is the
   *  function of its index to its elements, which a `select` applies: an array
   *  field is so of the sort its stores and its array constants have, and the
   *  array lemmas pair a read with the stores of its array's sort. A bit-vector
   *  sort is the range of the integers its terms are lowered to: the solver
   *  gives the range to every term of the sort, the ones it makes itself as
   *  much as the script's (`Encoder.assertSorts`).
   */
  private def lowered(s: s2.Sort): Sort = s match
    case s2.Sort.Bool => Sort.Bool
    case s2.Sort.Int => Sort.Int
    case s2.Sort.Real => Sort.Real
    case s2.Sort.BitVec(width) => Sort.IntRange(0, modulus(width) - 1)
    case s2.Sort.Named(name) => Sort.Named(name)
    case s2.Sort.Fun(args, result) => Sort.fun(args.map(lowered), lowered(result))
    case s2.Sort.Array(index, element) => Sort.fun(List(lowered(index)), lowered(element))

  private def command(c: s2.Command): List[Command] = c match
    // The lowered script is in the corresponding integer logic.
    case s2.Command.SetLogic(logic) => List(Command.SetLogic(logic.replace("BV", "LIA")))
    case s2.Command.SetInfo(key, value) => List(Command.SetInfo(key, value))
    case s2.Command.DeclareSort(name, arity) => List(Command.DeclareSort(name, arity))
    case s2.Command.DeclareFun(name, argSorts, sort) =>
      reserve(name)
      undoable(functions, name)
      functions(name) = s2.Sort.fun(argSorts, sort)
      // An array constant is declared as a constant of its function sort — `(declare-fun a () (-> I E))` —
      // not flattened into a function symbol: the solver applies it either way, and the model knows an
      // array from a function by that.
      List(Command.DeclareFun(name, argSorts.map(lowered), lowered(sort)))
    case s2.Command.DeclareDatatypes(datatypes) =>
      for datatype <- datatypes do
        undoable(declaredDatatypes, datatype.name)
        declaredDatatypes(datatype.name) = datatype
      for datatype <- datatypes; constructor <- datatype.constructors do
        val d = s2.Sort.Named(datatype.name)
        reserve(constructor.name)
        undoable(functions, constructor.name)
        functions(constructor.name) = s2.Sort.fun(constructor.selectors.map(_._2), d)
        undoable(functions, constructor.tester)
        functions(constructor.tester) = s2.Sort.fun(List(d), s2.Sort.Bool)
        for (selector, s) <- constructor.selectors do
          reserve(selector)
          undoable(functions, selector)
          functions(selector) = s2.Sort.fun(List(d), s)
      List(Command.DeclareDatatypes(datatypes.map(d =>
        Datatype(d.name, d.constructors.map(c => Constructor(c.name, c.selectors.map((n, s) => (n, lowered(s))))))
      )))
    case s2.Command.DefineFun(name, params, sort, body) =>
      reserve(name)
      undoable(macros, name)
      macros(name) = (params, sort, body) // expanded at each use; the definition itself vanishes
      Nil
    case s2.Command.Assert(f) => flush(Command.Assert(formula(f, Map.empty)))
    case s2.Command.AssertNamed(name, f) => flush(Command.AssertNamed(name, formula(f, Map.empty)))
    case s2.Command.CheckSat => List(Command.CheckSat)
    case s2.Command.CheckSatAssuming(assumptions) =>
      flush(Command.CheckSatAssuming(assumptions.map(formula(_, Map.empty))))
    case s2.Command.Push(levels) =>
      for _ <- 1 to levels do scopes += ArrayBuffer.empty
      // What a command that failed halfway minted goes out before the level opens: its entries are below it.
      flush(Command.Push(levels))
    case s2.Command.Pop(levels) =>
      // More levels than are open: the session refuses the `pop` whole (issue 178), and nothing is undone.
      if levels <= scopes.length then
        for _ <- 1 to levels do scopes.remove(scopes.length - 1).reverseIterator.foreach(_())
      List(Command.Pop(levels))
    case s2.Command.ResetAssertions =>
      // The levels go, and the declarations made in them stay, as the session keeps them (issue 178).
      scopes.clear()
      clearMemos()
      List(Command.ResetAssertions)
    case s2.Command.Reset =>
      scopes.clear()
      globalDeclarations = false
      functions.clear()
      macros.clear()
      rationalValues.clear()
      storeSymbols.clear()
      constSymbols.clear()
      declaredDatatypes.clear()
      finiteSorts.clear()
      mapSymbols.clear()
      clearMemos()
      List(Command.Reset)
    case s2.Command.GetModel => List(Command.GetModel)
    case s2.Command.GetValue(items) =>
      // A compound operation's defining assertions (a term-level `ite`'s) cannot be asserted after a
      // check: they go with the command, for the session to evaluate under the model.
      val lowered = items.map((source, item) =>
        (
          source,
          (item match
            case f: s2.Formula => formula(f, Map.empty)
            case t: s2.Term => term(t, Map.empty)
          ): Formula | Term
        )
      )
      val defined = pending.toList.collect { case Command.Assert(definition) => definition }
      // The symbols minted here are declared for good: a `.store!N` stays in `storeSymbols`, and a later
      // assertion that reuses it needs the solver to know it (issue 16). Their definitions cannot be
      // asserted after a check and go with the command instead.
      val declared = pending.toList.filter {
        case _: Command.DeclareFun | _: Command.DeclareMap | _: Command.DeclareFinite => true
        case _ => false
      }
      pending.clear()
      clearMemos() // a constant minted here has no definition: later uses must not find it
      declared :+ Command.GetValue(lowered, defined)
    case s2.Command.GetUnsatCore => List(Command.GetUnsatCore)
    case s2.Command.GetAssertions => List(Command.GetAssertions)
    case s2.Command.Exit => List(Command.Exit)
    case s2.Command.SetOption(key, value) =>
      if key == ":global-declarations" then globalDeclarations = value == "true"
      List(Command.SetOption(key, value))
    case s2.Command.GetInfo(key) => List(Command.GetInfo(key))
    case s2.Command.Other(sexpr) => List(Command.Other(sexpr))

  /** The fresh constants' declarations and their defining assertions, then the
   *  command.
   */
  private def flush(command: Command): List[Command] =
    val out = pending.toList :+ command
    pending.clear()
    out

  /** The sort of a surface term, for the sort-directed encodings: which `=` a
   *  chain means, the widths of bit-vectors, what a `select` returns.
   */
  private def sortOf(t: s2.Term, env: Env): s2.Sort = t match
    case s2.Term.Const(name) =>
      env.get(name) match
        case Some(Value.T(_, sort)) => sort
        case Some(Value.F(_)) => s2.Sort.Bool
        case None =>
          functions.get(name).orElse(macros.get(name).map(_._2)).getOrElse(
            throw s2.Smt2Error(s"unknown symbol $name")
          )
    case s2.Term.Numeral(_) => s2.Sort.Int
    case s2.Term.Decimal(_, _) => s2.Sort.Real
    case s2.Term.Bits(_, width) => s2.Sort.BitVec(width)
    case s2.Term.App(s2.Term.Const(name), args) if macros.contains(name) => macros(name)._2
    case s2.Term.App(fun, args) =>
      sortOf(fun, env).applied(args.length).getOrElse(
        throw s2.Smt2Error(s"${sortOf(fun, env)} applied to ${args.length} arguments")
      )
    case s2.Term.ArithApp(op, args) =>
      op match
        case ArithOp.Div | ArithOp.ToReal => s2.Sort.Real
        case ArithOp.IntDiv | ArithOp.Mod | ArithOp.Abs | ArithOp.ToInt => s2.Sort.Int
        case _ => if args.exists(a => sortOf(a, env) == s2.Sort.Real) then s2.Sort.Real else s2.Sort.Int
    case s2.Term.BvApp(op, args) =>
      op match
        case BvOp.UbvToInt | BvOp.SbvToInt => s2.Sort.Int
        case BvOp.IntToBv(n) => s2.Sort.BitVec(n)
        case BvOp.Extract(i, j) => s2.Sort.BitVec(i - j + 1)
        case BvOp.ZeroExtend(k) => s2.Sort.BitVec(width(args.head, env) + k)
        case BvOp.SignExtend(k) => s2.Sort.BitVec(width(args.head, env) + k)
        case BvOp.Repeat(k) => s2.Sort.BitVec(width(args.head, env) * k)
        case BvOp.Concat => s2.Sort.BitVec(args.map(width(_, env)).sum)
        case BvOp.Comp => s2.Sort.BitVec(1)
        case _ => s2.Sort.BitVec(width(args.head, env))
    case s2.Term.Select(array, _) =>
      sortOf(array, env) match
        case s2.Sort.Array(_, element) => element
        case s => s.applied(1).getOrElse(throw s2.Smt2Error(s"select on $s"))
    case s2.Term.Store(array, _, _) => sortOf(array, env)
    case s2.Term.ConstArray(sort, _) => sort
    case s2.Term.MapArray(op, params, body, arrays) =>
      sortOf(arrays.head, env) match
        case s2.Sort.Array(index, _) => s2.Sort.Array(index, sortOf(body, elementsEnv(params)))
        case s => throw s2.Smt2Error(s"(_ map $op) on $s")
    case s2.Term.Ite(_, thn, els) =>
      // Real when either branch is: a numeral beside a real term is a real (issue 15).
      val t = sortOf(thn, env)
      if t == s2.Sort.Int && sortOf(els, env) == s2.Sort.Real then s2.Sort.Real else t
    case s2.Term.Let(bindings, body) =>
      sortOf(
        body,
        env ++ bindings.map((name, value) =>
          name ->
            (value match
              case t: s2.Term => Value.T(Num(0), sortOf(t, env)) // only the sort matters here
              case _: s2.Formula => Value.F(True))
        )
      )
    case s2.Term.Bool(_) => s2.Sort.Bool

  private def width(t: s2.Term, env: Env): Int = sortOf(t, env) match
    case s2.Sort.BitVec(w) => w
    case s => throw s2.Smt2Error(s"a bit-vector was expected, not $s")

  /** Whether terms of `sort` are numbers after lowering: where `=` and
   *  `distinct` mean bounds.
   */
  private def arithmetic(sort: s2.Sort): Boolean = sort match
    case s2.Sort.Int | s2.Sort.Real | s2.Sort.BitVec(_) => true
    case _ => false

  /** Equality of two lowered terms of `sort`: bit by bit when both sides' bits
   *  are known (a bitwise result, a literal), so that a bit-level fact stays
   *  with the SAT solver; otherwise the solver's.
   */
  private def equal(sort: s2.Sort, lhs: Term, rhs: Term): Formula = sort match
    case s2.Sort.BitVec(w) if bitwiseEquality(List(lhs, rhs), w) =>
      And(bits(lhs, w).zip(bits(rhs, w)).map(same).toList)
    case _ => if arithmetic(sort) then IntEq(lhs, rhs) else Eq(lhs, rhs)

  /** Whether an equality of these `width`-bit terms is one of bits: all their
   *  bits known, and not all of them literals.
   */
  private def bitwiseEquality(ts: List[Term], width: Int): Boolean =
    ts.forall(t => knownBits(t, width).isDefined) && ts.exists(!_.isInstanceOf[Num])

  /** The conjunction of `conditions`, itself when there is only one. */
  private def chain(conditions: List[Formula]): Formula = conditions match
    case single :: Nil => single
    case _ => And(conditions)

  private def formula(f: s2.Formula, env: Env): Formula =
    visits += 1
    lowerFormula(f, env)

  private def lowerFormula(f: s2.Formula, env: Env): Formula = f match
    case s2.Formula.True => True
    case s2.Formula.False => False
    case s2.Formula.Not(arg) => Not(formula(arg, env))
    case s2.Formula.And(args) => And(args.map(formula(_, env)))
    case s2.Formula.Or(args) => Or(args.map(formula(_, env)))
    case s2.Formula.Implies(args) => args.map(formula(_, env)).reduceRight(Implies(_, _))
    case s2.Formula.Xor(args) => args.map(formula(_, env)).reduceLeft((a, b) => Not(Iff(a, b)))
    case s2.Formula.Iff(args) =>
      val fs = args.map(formula(_, env))
      chain(fs.zip(fs.tail).map(Iff(_, _)))
    case s2.Formula.Eq(args) =>
      val sort = sortOf(args.head, env)
      val ts = args.map(term(_, env))
      chain(ts.zip(ts.tail).map(equal(sort, _, _)))
    case s2.Formula.Distinct(args) =>
      val sort = sortOf(args.head, env)
      val ts = args.map(term(_, env))
      sort match
        case s2.Sort.BitVec(w) if bitwiseEquality(ts, w) =>
          chain(for (a, i) <- ts.zipWithIndex; b <- ts.drop(i + 1) yield Not(equal(sort, a, b)))
        case _ =>
          // A numeral among reals says `Int` on its own, so any real side makes the whole `distinct` one.
          if !arithmetic(sort) then Distinct(ts)
          else if args.exists(a => sortOf(a, env) == s2.Sort.Real) then RealDistinct(ts)
          else IntDistinct(ts)
    case s2.Formula.Cmp(op, args) =>
      val real = args.exists(a => sortOf(a, env) == s2.Sort.Real) // any side: numerals alone say Int
      val ts = args.map(term(_, env))
      val compare: (Term, Term) => Formula = op match
        case s2.CmpOp.Le => Le(_, _)
        case s2.CmpOp.Lt => if real then Less(_, _) else Lt(_, _)
        case s2.CmpOp.Ge => Ge(_, _)
        case s2.CmpOp.Gt => if real then (lhs, rhs) => Less(rhs, lhs) else Gt(_, _)
      chain(ts.zip(ts.tail).map(compare(_, _)))
    case s2.Formula.BvCmp(op, lhs, rhs) =>
      val w = width(lhs, env)
      compare(op, term(lhs, env), term(rhs, env), w)
    case s2.Formula.Ite(cond, thn, els) => Ite(formula(cond, env), formula(thn, env), formula(els, env))
    case s2.Formula.IsConstructor(constructor, arg) =>
      Pred(App(Const(s"(_ is $constructor)"), List(term(arg, env))))
    case s2.Formula.IsInt(arg) => isInt(term(arg, env))
    case s2.Formula.Let(bindings, body) => formula(body, bind(bindings, env))
    case s2.Formula.Pred(t) => Formula.pred(term(t, env))

  /** The bindings of a `let`, evaluated in the outer environment (`let` binds
   *  in parallel).
   */
  private def bind(bindings: List[(String, s2.Term | s2.Formula)], env: Env): Env =
    env ++ bindings.map((name, value) =>
      name ->
        (value match
          case t: s2.Term =>
            val sort = sortOf(t, env)
            if sort == s2.Sort.Bool then Value.F(Formula.pred(term(t, env))) else Value.T(term(t, env), sort)
          case f: s2.Formula => Value.F(formula(f, env)))
    )

  /** The terms and formulas lowered so far, for a budget. */
  var visits = 0L

  private def term(t: s2.Term, env: Env): Term =
    visits += 1
    lowerTerm(t, env)

  private def lowerTerm(t: s2.Term, env: Env): Term = t match
    case s2.Term.Const(name) =>
      env.get(name) match
        case Some(Value.T(t, _)) => t
        case Some(Value.F(f)) => Term.boolean(f)
        case None =>
          if macros.contains(name) then expand(name, Nil, env)
          else if functions.contains(name) then Const(name)
          else throw s2.Smt2Error(s"unknown symbol $name")
    case s2.Term.Numeral(value) => Num(value)
    case s2.Term.Decimal(unscaled, scale) => rationalConst(unscaled, BigInt(10).pow(scale))
    case s2.Term.Bits(value, _) => Num(value)
    case s2.Term.App(s2.Term.Const(name), args) if macros.contains(name) => expand(name, args, env)
    case s2.Term.App(fun, args) => App(term(fun, env), args.map(term(_, env)))
    case s2.Term.ArithApp(op, args) => arith(op, args, env)
    case s2.Term.BvApp(op, args) => bv(op, args, env)
    case s2.Term.Select(array, index) =>
      App(term(array, env), List(term(index, env)))
    case s2.Term.Store(array, index, value) =>
      App(storeSymbol(sortOf(array, env)), List(term(array, env), term(index, env), term(value, env)))
    case s2.Term.ConstArray(sort, value) => App(constSymbol(sort), List(term(value, env)))
    case s2.Term.MapArray(op, params, body, arrays) =>
      val lowered = arrays.map(term(_, env))
      App(mapSymbol(op, params, body, arrays.map(sortOf(_, env)), sortOf(t, env), lowered), lowered)
    case s2.Term.Ite(cond, thn, els) =>
      // A fresh constant `k` with `cond => k = thn` and `not cond => k = els`, asserted before the
      // current assertion; one per distinct `ite`, like the bit-vector operations.
      val sort = sortOf(s2.Term.Ite(cond, thn, els), env)
      val c = formula(cond, env)
      val (t, e) = (term(thn, env), term(els, env))
      loweredOperations.getOrElseUpdate(
        ("ite", List(Term.boolean(c), t, e), Nil), {
          val name = freshName("ite")
          val k = Const(name)
          introduce(name, lowered(sort))
          functions(name) = sort
          define(Implies(c, equal(sort, k, t)))
          define(Implies(Not(c), equal(sort, k, e)))
          k
        }
      )
    case s2.Term.Let(bindings, body) => term(body, bind(bindings, env))
    case s2.Term.Bool(f) => Term.boolean(formula(f, env))

  /** Expands the macro `name` applied to `args` (evaluated in `env`). The body
   *  sees its parameters and the declarations, never the caller's bindings: a
   *  `define-fun` is a top-level command, and a body that reads a global must
   *  not be captured by a caller's parameter of the same name (issue 10).
   */
  private def expand(name: String, args: List[s2.Term], env: Env): Term =
    val (params, sort, body) = macros(name)
    if params.length != args.length then throw s2.Smt2Error(s"$name expects ${params.length} arguments")
    val inner = params.zip(args).foldLeft(Map.empty: Env) { case (e, ((p, s), a)) =>
      e +
        (p -> (
          if s == s2.Sort.Bool then Value.F(Formula.pred(term(a, env)))
          else Value.T(term(a, env), s)
        ))
    }
    body match
      case t: s2.Term => term(t, inner)
      case f: s2.Formula => Term.boolean(formula(f, inner))

  // Arithmetic: `+`, `-` and `*` by a literal fold into the linear normal form; rational literals
  // and divisions become defined `Real` constants (so every consumer sees only integers); the
  // integer division operators are outside the fragment.
  private def arith(op: ArithOp, args: List[s2.Term], env: Env): Term = op match
    case ArithOp.Add => Term.linear(args.map(a => (BigInt(1), term(a, env))))
    case ArithOp.Sub =>
      Term.linear((BigInt(1), term(args.head, env)) :: args.tail.map(a => (BigInt(-1), term(a, env))))
    case ArithOp.Neg => Term.linear(List((BigInt(-1), term(args.head, env))))
    case ArithOp.Mul =>
      // Linear: all factors but at most one are literals, rationals included.
      val (literals, others) = args.map(term(_, env)).partitionMap(t => literalValue(t).toLeft(t))
      val (p, q) = literals.foldLeft((BigInt(1), BigInt(1))) { case ((p, q), (a, b)) => (p * a, q * b) }
      others match
        case Nil => rationalConst(p, q)
        case t :: Nil => rationalProduct(p, q, t)
        case _ => throw s2.Smt2Error(s"non-linear multiplication")
    case ArithOp.Div =>
      // Real division by a rational literal, `(/ 1 3)` and `(/ x 2)` alike; the rest is nonlinear.
      args.map(term(_, env)).reduceLeft { (numerator, divisorTerm) =>
        val divisor = literalValue(divisorTerm).getOrElse(throw s2.Smt2Error(s"nonlinear division"))
        literalValue(numerator) match
          case Some((p, q)) => rationalConst(p * divisor._2, q * divisor._1)
          case None => rationalProduct(divisor._2, divisor._1, numerator)
      }
    case ArithOp.ToReal => term(args.head, env) // the same value: sorts decide integrality, not the tree
    case ArithOp.ToInt =>
      val r = term(args.head, env)
      literalValue(r) match
        case Some((p, q)) => Num(floorDiv(p, q))
        case None => floor(r)
    case ArithOp.Abs =>
      // A fresh constant `k` with `t ≥ 0 => k = t` and `t < 0 => k = -t`, like a term-level `ite`.
      term(args.head, env) match
        case Num(v) => Num(v.abs)
        case t =>
          loweredOperations.getOrElseUpdate(
            ("abs", List(t), Nil), {
              val name = freshName("abs")
              introduce(name, Sort.Int)
              functions(name) = s2.Sort.Int
              val k = Const(name)
              define(Implies(Ge(t, Num(0)), IntEq(k, t)))
              define(Implies(Lt(t, Num(0)), IntEq(k, Term.linear(List((BigInt(-1), t))))))
              k
            }
          )
    case ArithOp.IntDiv | ArithOp.Mod =>
      // By nonzero numerals only, which keeps it linear: the rest is outside the fragment.
      val divisors = args.tail.map(d =>
        term(d, env) match
          case Num(n) if n.signum != 0 => n
          case _ => throw s2.Unsupported(s"${op.name} by other than a nonzero numeral is not supported")
      )
      if op == ArithOp.Mod then quotient(term(args.head, env), divisors.head)._2
      else divisors.foldLeft(term(args.head, env))((t, n) => quotient(t, n)._1)

  private val quotients = Memo[(Term, BigInt), (Term, Term)]()

  /** `(div t n, mod t n)` for a nonzero numeral `n`, as SMT-LIB defines them:
   *  fresh constants `q` and `r` with `t = n q + r` and `0 ≤ r < |n|`, which
   *  pins both, so the definition is sound under both polarities.
   */
  private def quotient(t: Term, n: BigInt): (Term, Term) = t match
    case Num(v) =>
      val r = v.mod(n.abs)
      (Num((v - r) / n), Num(r))
    case _ =>
      quotients.getOrElseUpdate(
        (t, n), {
          val name = freshName("div")
          introduce(name, Sort.Int)
          functions(name) = s2.Sort.Int
          val q = Const(name)
          val r = freshInt("mod", 0, n.abs - 1)
          define(IntEq(t, Term.linear(List((n, q), (BigInt(1), r)))))
          (q, r)
        }
      )

  /** `is_int r`: `r` equals its own floor — sound under negation too, the floor
   *  being pinned uniquely by its definition. A literal folds.
   */
  private def isInt(r: Term): Formula = literalValue(r) match
    case Some((p, q)) => if p.mod(q).signum == 0 then True else False
    case None => IntEq(r, floor(r))

  /** The floor of `r` (`to_int`): a fresh `Int` constant `k` with
   *  `k ≤ r < k + 1`, declared and defined before the current assertion —
   *  determined uniquely by `r`, so the definition is sound under both
   *  polarities.
   */
  private def floor(r: Term): Term =
    val name = freshName("floor")
    introduce(name, Sort.Int)
    functions(name) = s2.Sort.Int
    val k = Const(name)
    define(Le(k, r))
    define(Less(r, Term.linear(List((BigInt(1), k)), 1)))
    k

  private def floorDiv(p: BigInt, q: BigInt): BigInt =
    val (d, r) = p /% q
    if r.signum != 0 && r.signum != q.signum then d - 1 else d

  private val rationals = Memo[(BigInt, BigInt), Term]()

  /** The value `p / q` of every term made by [[rationalConst]], for the literal
   *  folding of products and divisions.
   */
  private val rationalValues = HashMap.empty[Term, (BigInt, BigInt)]

  /** The rational value of a term when it is a literal: a numeral, a rational
   *  constant, or an integer multiple of one — `(- 0.1)` lowers to the latter.
   */
  private def literalValue(t: Term): Option[(BigInt, BigInt)] = t match
    case Num(v) => Some((v, BigInt(1)))
    case _ if rationalValues.contains(t) => Some(rationalValues(t))
    case Linear(List((a, u)), c) if c.signum == 0 && rationalValues.contains(u) =>
      val (p, q) = rationalValues(u)
      Some((a * p, q))
    case _ => None

  /** The term standing for the rational `p / q`: a numeral when integral, else
   *  a fresh `Real` constant `k` defined by `q k = p` before the current
   *  assertion — the mechanism of the bit-vector lowering, so every consumer
   *  (the solver, the models, the z3 replay) sees only integers.
   */
  private def rationalConst(p0: BigInt, q0: BigInt): Term =
    require(q0.signum != 0, "division by zero")
    val g = p0.gcd(q0) * q0.signum
    val (p, q) = (p0 / g, q0 / g)
    if q == BigInt(1) then Num(p)
    else
      rationals.getOrElseUpdate(
        (p, q), {
          val name = freshName("rat")
          introduce(name, Sort.Real)
          functions(name) = s2.Sort.Real
          val k = Const(name)
          define(IntEq(Term.linear(List((q, k))), Num(p)))
          rationalValues(k) = (p, q)
          k
        }
      )

  /** The term standing for `(p / q) × t`: `t` scaled by an integer when `q`
   *  divides `p`, else a fresh `Real` constant `k` defined by `q k = p t`.
   */
  private def rationalProduct(p0: BigInt, q0: BigInt, t: Term): Term =
    require(q0.signum != 0, "division by zero")
    val g = p0.gcd(q0) * q0.signum
    val (p, q) = (p0 / g, q0 / g)
    if q == BigInt(1) then Term.linear(List((p, t)))
    else
      rationalProducts.getOrElseUpdate(
        (p, q, t), {
          val name = freshName("rat")
          introduce(name, Sort.Real)
          functions(name) = s2.Sort.Real
          val k = Const(name)
          define(IntEq(Term.linear(List((q, k))), Term.linear(List((p, t)))))
          k
        }
      )

  /** The datatypes declared, as written, whose values the lowering counts and
   *  builds for [[noteIndex]].
   */
  private val declaredDatatypes = HashMap.empty[String, s2.Datatype]

  /** The finite index sorts of the constant arrays and maps, by their text,
   *  whose count and values went to the solver: undone with the level of their
   *  datatype, which a later declaration may name anew.
   */
  private val finiteSorts = HashMap.empty[String, BigInt]

  /** How many values an index sort has, by its text, where it is known. */
  private def sizeOf(text: String): Option[BigInt] = Model.knownSize(text).orElse(finiteSorts.get(text))

  private val manyValues = BigInt(1) << 62

  /** Tells the solver how many values the index sort of a constant array or a
   *  map has, and how to build the `k`-th of them ([[Command.DeclareFinite]]),
   *  for a finite sort other than `Bool` and the bit-vectors, whose values the
   *  solver knows: the index it takes beyond the writes ([[Encoder.beyond]]) is
   *  apart from fewer of them than the sort has values, and the arrays are read
   *  at every value from then on, which the solver builds then.
   */
  private def noteIndex(arraySort: s2.Sort): Unit = arraySort match
    case s2.Sort.Array(s2.Sort.Bool | s2.Sort.BitVec(_), _) => ()
    case s2.Sort.Array(index, _) =>
      val key = lowered(index)
      if !finiteSorts.contains(key.text) then
        for n <- cardinality(index) do
          undoable(finiteSorts, key.text)
          finiteSorts(key.text) = n
          val build = shape(index) // its symbols declared now: the solver declares none of its own
          pending += Command.DeclareFinite(key, n, k => build.value(k))
    case _ => ()

  /** A finite sort as the solver builds its values: what a value is made of,
   *  with the symbols that make it, and how many values there are.
   */
  private sealed trait Shape:
    def size: BigInt

    /** The `k`-th value, for `0 ≤ k < size`: `k` read in mixed radix. */
    def value(k: BigInt): Term

  private final case class Constructors(constructors: List[(String, List[Shape])]) extends Shape:
    private val sizes = constructors.map(_._2.foldLeft(BigInt(1))((n, f) => (n * f.size).min(manyValues)))
    val size: BigInt = sizes.sum.min(manyValues)
    def value(k: BigInt): Term =
      // The constructor whose values `k` falls among, then its fields: the last varies fastest.
      val starts = sizes.scanLeft(BigInt(0))(_ + _)
      val c = sizes.indices.find(i => k < starts(i + 1)).get
      val (name, fields) = constructors(c)
      if fields.isEmpty then Const(name)
      else
        val (args, _) = fields.foldRight((List.empty[Term], k - starts(c))) { case (f, (done, rest)) =>
          (f.value(rest % f.size) :: done, rest / f.size)
        }
        App(Const(name), args)

  private final case class Bits(width: Int) extends Shape:
    val size: BigInt = BigInt(2).pow(width)
    def value(k: BigInt): Term = Num(k)

  private object Booleans extends Shape:
    val size: BigInt = BigInt(2)
    def value(k: BigInt): Term = Term.boolean(if k == 0 then True else False)

  /** The arrays from `index` to `element`; `index` is `None` (and may be
   *  infinite) when `element` has a single value, and so do the arrays.
   */
  private final case class Arrays(index: Option[Shape], element: Shape, const: Term, store: Term) extends Shape:
    val size: BigInt = index match
      case None => BigInt(1)
      case Some(i) => if i.size >= 64 then manyValues else element.size.pow(i.size.toInt).min(manyValues)
    def value(k: BigInt): Term = index match
      case None => App(const, List(element.value(0)))
      case Some(i) =>
        // A store at every index, over the constant array of the first element.
        val (at, _) = (0 until i.size.toInt).foldLeft((List.empty[(Term, Term)], k)) { case ((done, rest), j) =>
          ((i.value(BigInt(j)), element.value(rest % element.size)) :: done, rest / element.size)
        }
        at.reverse.foldLeft(App(const, List(element.value(0))): Term) { case (a, (j, v)) => App(store, List(a, j, v)) }

  /** The shape of a finite sort, declaring the symbols of its arrays. */
  private def shape(sort: s2.Sort): Shape = sort match
    case s2.Sort.Bool => Booleans
    case s2.Sort.BitVec(w) => Bits(w)
    case s2.Sort.Named(name) =>
      Constructors(declaredDatatypes(name).constructors.map(c => (c.name, c.selectors.map((_, f) => shape(f)))))
    case s2.Sort.Array(index, element) =>
      val e = shape(element)
      Arrays(if e.size == 1 then None else Some(shape(index)), e, constSymbol(sort), storeSymbol(sort))
    case _ => throw s2.Smt2Error(s"the values of the infinite sort ${sort.text}")

  /** How many values a sort has, `None` for infinitely many: `Bool`, a
   *  bit-vector, a datatype with no field of an infinite sort or of its own, an
   *  array between finite sorts or into a sort of one value. An uninterpreted
   *  sort has as many as a model needs. Capped at [[manyValues]].
   */
  private def cardinality(sort: s2.Sort, open: Set[String] = Set.empty): Option[BigInt] = sort match
    case s2.Sort.Bool => Some(BigInt(2))
    case s2.Sort.BitVec(w) => Some(if w >= 62 then manyValues else BigInt(2).pow(w))
    case s2.Sort.Named(name) if !open(name) =>
      declaredDatatypes.get(name).flatMap { d =>
        val counts = d.constructors.map(_.selectors.foldLeft(Option(BigInt(1)))((acc, field) =>
          for n <- acc; m <- cardinality(field._2, open + name) yield (n * m).min(manyValues)
        ))
        if counts.forall(_.isDefined) then Some(counts.flatten.sum.min(manyValues)) else None
      }
    case s2.Sort.Array(index, element) =>
      (cardinality(index, open), cardinality(element, open)) match
        case (_, Some(m)) if m == 1 => Some(m)
        case (Some(n), Some(m)) => Some(if n >= 64 then manyValues else m.pow(n.toInt).min(manyValues))
        case _ => None
    case _ => None

  /** The `.array.const!N` function symbol for the constant arrays of `sort`,
   *  declared on first use like a [[storeSymbol]]: a function of the element to
   *  the array, which the solver's array lemmas recognize by the name.
   */
  private val constSymbols = HashMap.empty[Sort, String]

  private def constSymbol(arraySort: s2.Sort): Term =
    noteIndex(arraySort)
    val key = lowered(arraySort)
    val name = constSymbols.getOrElseUpdate(
      key, {
        val element = key.after(1).getOrElse(throw s2.Smt2Error(s"a constant array of $arraySort"))
        val n = freshName("array.const")
        introduce(n, Sort.fun(List(element), key))
        functions(n) = s2.Sort.Named(n)
        n
      }
    )
    Const(name)

  /** The `.array.map!N` function symbol for the map of an operator over arrays,
   *  declared on first use like a [[storeSymbol]], with the [[Pointwise]]
   *  template that says what the map holds at an index: the solver's array
   *  lemmas instantiate it there. Keyed on the template itself, its names aside
   *  ([[Pointwise.canonical]]), and on the sorts of the arrays and of the map:
   *  the operator as it stands where the map is, a macro defined anew after a
   *  `pop` making another template, and the bit-vector operations of each width
   *  theirs. The numerals of the constant arrays among the arrays are folded
   *  into the template: `div` by `((as const (Array I Int)) 2)` is linear that
   *  way.
   */
  private val mapSymbols = HashMap.empty[(Pointwise, List[Sort], Sort), String]

  /** The parameters of a map's operator as an environment, for [[sortOf]]. */
  private def elementsEnv(params: List[(String, s2.Sort)]): Env =
    params.map((p, s) => p -> (if s == s2.Sort.Bool then Value.F(True) else Value.T(Const(p), s))).toMap

  private def mapSymbol(
      op: String,
      params: List[(String, s2.Sort)],
      body: s2.Term,
      arraySorts: List[s2.Sort],
      result: s2.Sort,
      arrays: List[Term]
  ): Term =
    noteIndex(result)
    val keys = arraySorts.map(lowered)
    val resultKey = lowered(result)
    if (resultKey :: keys).exists(_.arrow.isEmpty) then
      throw s2.Smt2Error(s"(_ map $op) on ${arraySorts.map(_.text).mkString(" ")}")
    val literals = arrays.map {
      case App(Const(c), List(v @ Num(_))) if Names.isConstArray(c) => Some(v)
      case _ => None
    }
    // The operator is lowered on its own, over placeholders for the elements: what that mints belongs to
    // the template, and nothing of the assertion around the map is to be found in it.
    val around = pending.toList
    pending.clear()
    clearMemos()
    val (kept, pointwise) =
      try
        val elements = params.zip(literals).map {
          case (_, Some(v)) => v
          case ((_, _), None) => Const(freshName("element"))
        }
        val inner: Env = params.zip(elements).map { case ((p, sort), x) =>
          p -> (if sort == s2.Sort.Bool then Value.F(Formula.pred(x)) else Value.T(x, sort))
        }.toMap
        val value = term(body, inner)
        val formals = params.zip(elements).collect { case ((_, sort), Const(_)) => lowered(sort) }
        // An array operation of the operator's is declared like any other; the rest is the template's.
        val (kept, auxiliaries, definitions) = pending.toList.foldRight(
          (List.empty[Command], List.empty[(String, List[Sort], Sort)], List.empty[Formula])
        ) {
          case (Command.DeclareFun(n, Nil, sort, _), (k, a, d)) if !Names.isArrayOperation(n) =>
            (k, (n, formals, sort) :: a, d)
          case (Command.Assert(definition), (k, a, d)) => (k, a, definition :: d)
          case (command, (k, a, d)) => (command :: k, a, d)
        }
        val pointwise = Pointwise(elements, auxiliaries, value, definitions, resultKey)
        val locals = elements.collect { case Const(n) => n }.toSet ++ auxiliaries.map(_._1)
        if (value :: definitions.flatMap(_.terms)).exists(readsAt(_, locals)) then
          throw s2.Unsupported(s"(_ map $op): an operator that reads or writes an array at an element is not supported")
        (kept, pointwise)
      finally
        pending.clear()
        pending ++= around
        clearMemos()
    pending ++= kept
    val name = mapSymbols.getOrElseUpdate(
      (pointwise.canonical, keys, resultKey), {
        val f = freshName("array.map")
        pending += Command.DeclareMap(f, Sort.fun(keys, resultKey), pointwise)
        functions(f) = s2.Sort.Named(f)
        f
      }
    )
    Const(name)

  /** Whether `t` reads or writes an array at an index that one of `locals` (the
   *  elements of a map's operator, its auxiliaries) is in: the map's lemmas
   *  would make an index of each element, and read every array of its sort
   *  there, the map among them, whose elements there are indices in turn,
   *  without end — `c = ((_ map g) a)` with `g(x) = (select c x)` says
   *  `c[j] = c[a[j]]` at every index `j`. A read or a write at a fixed index,
   *  of an element that is itself an array as much as of another array, is
   *  fine, and so is an application of a declared function.
   */
  private def readsAt(t: Term, locals: Set[String]): Boolean =
    def mentions(u: Term) = Term.constants(u).exists(locals)
    t match
      case App(Const(n), List(a, i, v)) if Names.isStore(n) =>
        mentions(i) || readsAt(a, locals) || readsAt(i, locals) || readsAt(v, locals)
      case App(Const(n), args) if Names.isConstArray(n) || Names.isMap(n) => args.exists(readsAt(_, locals))
      case App(fun, args) =>
        val array = fun match
          case Const(n) => locals(n) || functions.get(n).exists(_.isInstanceOf[s2.Sort.Array])
          case _ => true // an array that is itself a read or a write
        (array && args.exists(mentions)) || readsAt(fun, locals) || args.exists(readsAt(_, locals))
      case Term.Linear(terms, _) => terms.exists((_, u) => readsAt(u, locals))
      case Term.Bool(formula) => formula.terms.exists(readsAt(_, locals))
      case _ => false

  private val rationalProducts = Memo[(BigInt, BigInt, Term), Term]()

  /** The `.store!N` function symbol for arrays of `sort`, declared on first
   *  use: `store` is not a function of the tree, each array sort gets its own
   *  uninterpreted symbol, and the solver's array lemmas recognize the name.
   */
  private val storeSymbols = HashMap.empty[Sort, String]

  private def storeSymbol(arraySort: s2.Sort): Term =
    val key = lowered(arraySort)
    val name = storeSymbols.getOrElseUpdate(
      key, {
        // The array's function sort, flattened when its elements are arrays: the index is the first
        // parameter, the value sort what the array applied to one index has.
        val (params, _) = key.arrow.getOrElse(throw s2.Smt2Error(s"store on $arraySort"))
        val n = freshName("store")
        val argSorts = key :: params.head :: List(key.after(1).get) // the array, the index, the value
        introduce(n, Sort.fun(argSorts, key))
        functions(n) = s2.Sort.Named(n) // the solver reads the introduced declaration; the name is enough here
        n
      }
    )
    Const(name)

  // Bit-vectors, to linear integer arithmetic.

  /** A fresh `Int` constant in `[lo, hi]`, declared and bounded before the
   *  current assertion. `aux`: declared auxiliary (see [[Command.DeclareFun]]).
   */
  private def freshInt(prefix: String, lo: BigInt, hi: BigInt, aux: Boolean = false): Term =
    val name = freshName(prefix)
    introduce(name, Sort.Int, aux)
    val k = Const(name)
    define(Ge(k, Num(lo)))
    define(Le(k, Num(hi)))
    k

  private def modulus(width: Int): BigInt = BigInt(2).pow(width)

  private def bv(op: BvOp, args: List[s2.Term], env: Env): Term = op match
    // The value of a lowered bit-vector is its unsigned value: `ubv_to_int` vanishes, `sbv_to_int`
    // splits off the sign bit, `(_ int_to_bv n)` is the value modulo 2^n through a pinned overflow
    // count — determined uniquely, so sound under both polarities.
    case BvOp.UbvToInt => term(args.head, env)
    case BvOp.SbvToInt => signed(term(args.head, env), width(args.head, env))
    case BvOp.IntToBv(n) => intToBv(term(args.head, env), n)
    case BvOp.Extract(i, j) => extract(i, j, term(args.head, env), width(args.head, env))
    case BvOp.ZeroExtend(_) => term(args.head, env)
    case BvOp.SignExtend(k) => signExtend(k, term(args.head, env), width(args.head, env))
    case BvOp.Repeat(k) =>
      val (t, w) = (term(args.head, env), width(args.head, env))
      Term.linear((0 until k).toList.map(j => (modulus(j * w), t)))
    case BvOp.RotateLeft(k) => rotate(k, term(args.head, env), width(args.head, env))
    case BvOp.RotateRight(k) =>
      val w = width(args.head, env)
      rotate(w - k % w, term(args.head, env), w)
    case BvOp.Concat =>
      args.map(a => (term(a, env), width(a, env))).reduceLeft { case ((hi, wh), (lo, wl)) =>
        (Term.linear(List((BigInt(2).pow(wl), hi), (BigInt(1), lo))), wh + wl)
      }._1
    case _ =>
      val w = width(args.head, env)
      arithmeticBv(op, args.map(term(_, env)), w)

  private def arithmeticBv(op: BvOp, args: List[Term], width: Int): Term =
    val m = modulus(width)
    (op, args) match
      case (BvOp.Add, _ :: _ :: _ :: _) => args.reduceLeft((a, b) => arithmeticBv(BvOp.Add, List(a, b), width))
      case (BvOp.Mul, _ :: _ :: _ :: _) => args.reduceLeft((a, b) => arithmeticBv(BvOp.Mul, List(a, b), width))
      case (BvOp.Add, a :: b :: Nil) => modulo(a + b, width, 0, 1)
      case (BvOp.Sub, a :: b :: Nil) => modulo(a - b, width, -1, 0)
      case (BvOp.Neg, a :: Nil) => modulo(Term.linear(List((BigInt(-1), a))), width, -1, 0)
      case (BvOp.Not, a :: Nil) => not(a, width)
      case (BvOp.Mul, a :: b :: Nil) =>
        (a, b) match
          case (Num(u), Num(v)) => Num((u * v).mod(m))
          case (t, Num(c)) => times(t, c.mod(m), width)
          case (Num(c), t) => times(t, c.mod(m), width)
          case _ => product(a, b, width)
      case (BvOp.Shl, a :: Num(c) :: Nil) =>
        if c >= width then Num(0) else times(a, BigInt(2).pow(c.toInt), width)
      case (BvOp.Lshr, a :: Num(c) :: Nil) =>
        if c >= width then Num(0) else divide(a, BigInt(2).pow(c.toInt), m / BigInt(2).pow(c.toInt) - 1)._1
      case (BvOp.Udiv, a :: Num(c) :: Nil) => if c.signum == 0 then Num(m - 1) else divide(a, c, (m - 1) / c)._1
      case (BvOp.Urem, a :: Num(c) :: Nil) => if c.signum == 0 then a else divide(a, c, (m - 1) / c)._2
      case (BvOp.Sdiv | BvOp.Srem | BvOp.Smod, a :: Num(c) :: Nil) => signedDivision(op, a, c, width)
      case (BvOp.Ashr, Num(v) :: Num(c) :: Nil) =>
        Num(((if v >= m / 2 then v - m else v) >> c.min(width).toInt).mod(m))
      case (BvOp.Ashr, a :: Num(c) :: Nil) => // the floor of the signed value over 2^c: all ones or zero past the width
        val q =
          if c >= width then cases("sign", negative(a, width), Num(-1), Num(0), -1, 0)
          else divideSigned(a, width, BigInt(2).pow(c.toInt), floor = true)._1
        modulo(q, width, -1, 0)
      case (BvOp.Shl | BvOp.Lshr | BvOp.Ashr, a :: b :: Nil) => shifted(op, a, b, width)
      case (BvOp.Udiv, a :: b :: Nil) => divideUnknown(a, b, width)._1
      case (BvOp.Urem, a :: b :: Nil) => divideUnknown(a, b, width)._2
      case (BvOp.Sdiv | BvOp.Srem | BvOp.Smod, a :: b :: Nil) => signedDivisionUnknown(op, a, b, width)
      case (BvOp.And | BvOp.Or | BvOp.Xor, _) => args.reduceLeft((a, b) => bitwise(op, a, b, width))
      case (BvOp.Nand, a :: b :: Nil) => not(bitwise(BvOp.And, a, b, width), width)
      case (BvOp.Nor, a :: b :: Nil) => not(bitwise(BvOp.Or, a, b, width), width)
      case (BvOp.Xnor, a :: b :: Nil) => not(bitwise(BvOp.Xor, a, b, width), width)
      case (BvOp.Comp, a :: b :: Nil) =>
        (a, b) match
          case (Num(u), Num(v)) => Num(if u == v then 1 else 0)
          case _ => cases("comp", equal(s2.Sort.BitVec(width), a, b), Num(1), Num(0), 0, 1)
      case _ => throw s2.Unsupported(s"${op.name} with these arguments is not supported")
    end match

  /** `a × b` modulo `2^width`, neither a constant: shift-and-add over the bits
   *  of one operand — each partial product `2^i × a` a case on bit `i`, the sum
   *  reduced once, its overflow count an unknown.
   */
  private def product(a: Term, b: Term, width: Int): Term =
    val (kept, blasted) = if knownBits(a, width).isDefined && knownBits(b, width).isEmpty then (b, a) else (a, b)
    loweredOperations.getOrElseUpdate(
      ("bvmul", List(kept, blasted), List(width)), {
        val m = modulus(width)
        val partials = bits(blasted, width).zipWithIndex.map((bit, i) =>
          bit match
            case True => kept * modulus(i)
            case False => Num(0)
            case _ => cases("part", bit, kept * modulus(i), Num(0), 0, modulus(i) * (m - 1))
        )
        modulo(Term.linear(partials.toList.map(p => (BigInt(1), p))), width, 0, m - 2)
      }
    )

  /** `a` divided by an unknown `b`: fresh `q` and `r` in `[0, 2^n)` with
   *  `a = b·q + r` and `r < b` — the product exact, not modulo, so that `q` is
   *  the quotient and not a wrapped one — and SMT-LIB's answer to a zero
   *  divisor, all ones and `a`. The pair `(q, r)`.
   */
  private def divideUnknown(a: Term, b: Term, width: Int): (Term, Term) =
    val m = modulus(width)
    val (q, r) = loweredDivisions.getOrElseUpdate(
      (Term.linear(List((BigInt(1), a), (m, b))), m, m), {
        val q = freshInt("q", 0, m - 1)
        val r = freshInt("r", 0, m - 1)
        val zero = IntEq(b, Num(0))
        define(Implies(zero, And(List(IntEq(q, Num(m - 1)), IntEq(r, a)))))
        define(Implies(Not(zero), And(List(IntEq(a, exactProduct(b, q, width) + r), Less(r, b)))))
        (q, r)
      }
    )
    (q, r)

  /** `a × b` as an integer, without the reduction modulo `2^n`: shift-and-add
   *  over the bits of `b`, for a division, where the product cannot wrap.
   */
  private def exactProduct(a: Term, b: Term, width: Int): Term =
    val m = modulus(width)
    val partials = bits(b, width).zipWithIndex.map((bit, i) =>
      bit match
        case True => a * modulus(i)
        case False => Num(0)
        case _ => cases("part", bit, a * modulus(i), Num(0), 0, modulus(i) * (m - 1))
    )
    Term.linear(partials.toList.map(p => (BigInt(1), p)))

  /** A signed division by an unknown: the unsigned division of the absolute
   *  values, its quotient and remainder given the signs SMT-LIB asks for —
   *  `bvsdiv` truncates, so the remainder takes the dividend's sign and
   *  `bvsmod` the divisor's — and the zero divisor answered as for a constant.
   */
  private def signedDivisionUnknown(op: BvOp, a: Term, b: Term, width: Int): Term =
    val m = modulus(width)
    val (na, nb) = (negative(a, width), negative(b, width))
    def magnitude(t: Term, n: Formula): Term =
      cases("abs", n, Term.linear(List((BigInt(-1), t)), m), t, 0, m / 2)
    val (q, r) = divideUnknown(magnitude(a, na), magnitude(b, nb), width)
    val zero = IntEq(b, Num(0))
    op match
      case BvOp.Sdiv =>
        // Negated as `2^n − q` when the signs differ and the quotient is not zero: `2^n − 0` is
        // outside the width, and a case constant with no value made the script unsat (issue 9).
        // `q ≥ 1` is one bound where `q ≠ 0` would be two; ranging the case up to `2^n` and
        // reducing it with `modulo` costs no atom but measured slower (2020-Weber, 9.2 s to 7.8 s).
        val negate = And(List(Not(Iff(na, nb)), Ge(q, Num(1))))
        val signed = cases("sdivq", negate, Term.linear(List((BigInt(-1), q)), m), q, 0, m - 1)
        cases("sdiv0", zero, cases("sdiv0!", na, Num(1), Num(m - 1), 1, m - 1), signed, 0, m - 1)
      case _ =>
        // The remainder of the sign of the dividend (`bvsrem`), then of the divisor (`bvsmod`).
        val negate = And(List(na, Ge(r, Num(1)))) // as for the quotient: never `2^n − 0`
        val rem = cases("sremr", negate, Term.linear(List((BigInt(-1), r)), m), r, 0, m - 1)
        val result =
          if op == BvOp.Srem then rem
          else
            val differ = And(List(Not(Iff(na, nb)), Not(IntEq(r, Num(0)))))
            cases("smodr", differ, modulo(rem + b, width, 0, 1), rem, 0, m - 1)
        cases("srem0", zero, a, result, 0, m - 1)

  /** A shift by an unknown amount: a barrel shifter over the amount's bits —
   *  stage `j` shifts by `2^j` or not, on bit `j` of the amount — so `log n`
   *  cases and not `n`, and zero (or the sign, for `bvashr`) when the amount
   *  reaches the width.
   */
  private def shifted(op: BvOp, a: Term, amount: Term, width: Int): Term =
    loweredOperations.getOrElseUpdate(
      (op.name, List(a, amount), List(width)), {
        val stages = Iterator.iterate(1)(_ * 2).takeWhile(_ < width).length // ⌈log₂ width⌉
        val bs = bits(amount, width)
        val shifted = (0 until stages).foldLeft(a) { (t, j) =>
          val by = modulus(1 << j)
          val step = op match
            case BvOp.Shl => times(t, by, width)
            case BvOp.Lshr => divide(t, by, modulus(width) / by - 1)._1
            case _ => modulo(divideSigned(t, width, by, floor = true)._1, width, -1, 0)
          bs(j) match
            case True => step
            case False => t
            case bit => cases(op.name, bit, step, t, 0, modulus(width) - 1)
        }
        // The amount reaches the width exactly when a bit above the stages is set, or the stages'
        // bits spell a value the width does not hold.
        val far = Or(
          bs.drop(stages).toList.filter(_ != False) ++
            (if (1 << stages) == width then Nil else List(Ge(amount, Num(width))))
        )
        val past = op match
          case BvOp.Ashr => cases("sign", negative(a, width), Num(modulus(width) - 1), Num(0), 0, modulus(width) - 1)
          case _ => Num(0)
        far match
          case False => shifted
          case True => past
          case _ => cases(op.name + "!far", far, past, shifted, 0, modulus(width) - 1)
      }
    )

  /** `2^width − 1 − t`; the complement of known bits is known. */
  private def not(t: Term, width: Int): Term =
    val r = Term.linear(List((BigInt(-1), t)), modulus(width) - 1)
    for bs <- loweredBits.get((t, width)) do loweredBits((r, width)) = bs.map(Not(_))
    r

  /** `t` rotated left by `k` bits: `t = 2^(width−k) × q + r`, the result
   *  `2^k × r + q`.
   */
  private def rotate(k: Int, t: Term, width: Int): Term =
    val shift = k % width
    if shift == 0 then t
    else
      val (q, r) = divide(t, modulus(width - shift), modulus(shift) - 1)
      Term.linear(List((modulus(shift), r), (BigInt(1), q)))

  // Bitwise operations: the bits of a term, as formulas the SAT solver decides.

  /** The bits of a `width`-bit term, lowest first: a literal's are literal, a
   *  complement's (`bvnot`) are negations, a bitwise result keeps its own; any
   *  other term is decomposed once at a level — fresh constants `b_i` in
   *  `{0, 1}` with `t = Σ 2^i b_i`, bit `i` the atom `b_i ≥ 1`.
   */
  private def bits(t: Term, width: Int): IndexedSeq[Formula] =
    knownBits(t, width).getOrElse {
      val bs = (0 until width).map(_ => freshInt("bit", 0, 1, aux = true))
      define(IntEq(t, Term.linear(bs.toList.zipWithIndex.map((b, i) => (modulus(i), b)))))
      val fs = bs.map(b => Ge(b, Num(1)))
      for (f, b) <- fs.zip(bs) do bitConstants(f) = b
      loweredBits((t, width)) = fs
      fs
    }

  /** The bits of `t` if they are known without a decomposition. */
  private def knownBits(t: Term, width: Int): Option[IndexedSeq[Formula]] = t match
    case Num(v) => Some((0 until width).map(i => if v.testBit(i) then True else False))
    case Linear(List((a, u)), c) if a == -1 && c == modulus(width) - 1 => knownBits(u, width).map(_.map(Not(_)))
    case _ => loweredBits.get((t, width))

  /** The `{0, 1}` constant carrying a bit: the one it came from, its
   *  complement, or a fresh case on the bit's formula.
   */
  private def bitConstant(f: Formula): Term = f match
    case True => Num(1)
    case False => Num(0)
    case Not(g) if bitConstants.contains(g) => Num(1) - bitConstants(g)
    case _ => bitConstants.getOrElseUpdate(f, cases("bit", f, Num(1), Num(0), 0, 1))

  /** The term with these bits: the weighted sum of their constants. */
  private def fromBits(fs: IndexedSeq[Formula]): Term =
    Term.linear(fs.toList.zipWithIndex.collect { case (f, i) if f != False => (modulus(i), bitConstant(f)) })

  /** `f ↔ g`, folded on literals. */
  private def same(f: Formula, g: Formula): Formula = (f, g) match
    case (True, _) => g
    case (_, True) => f
    case (False, _) => Not(g)
    case (_, False) => Not(f)
    case _ => if f == g then True else Iff(f, g)

  /** `bvand`, `bvor` or `bvxor` of two `width`-bit terms, the operands in a
   *  fixed order (the operation is commutative, and one lowering for both
   *  orders makes that syntactic): a mask that is a run of low or high bits
   *  goes through one division; anything else is bit by bit, the result the
   *  weighted sum of its bits.
   */
  private def bitwise(op: BvOp, a: Term, b: Term, width: Int): Term =
    (a, b) match
      case (Num(u), Num(v)) =>
        Num(op match
          case BvOp.And => u & v
          case BvOp.Or => u | v
          case _ => u ^ v)
      case _ =>
        val (l, r) = if a.hashCode <= b.hashCode then (a, b) else (b, a)
        loweredOperations.getOrElseUpdate(
          (op.name, List(l, r), List(width)), {
            val run = (l, r) match
              case (t, Num(mask)) => masked(op, t, mask, width)
              case (Num(mask), t) => masked(op, t, mask, width)
              case _ => None
            run.getOrElse {
              val (ls, rs) = (bits(l, width), bits(r, width))
              val fs = (0 until width).map(i => gate(op, ls(i), rs(i)))
              val result = fromBits(fs)
              loweredBits((result, width)) = fs
              result
            }
          }
        )

  /** One bit of a bitwise operation, folded on literals and on equal bits. */
  private def gate(op: BvOp, x: Formula, y: Formula): Formula = (op, x, y) match
    case (BvOp.And, True, f) => f
    case (BvOp.And, f, True) => f
    case (BvOp.And, False, _) => False
    case (BvOp.And, _, False) => False
    case (BvOp.Or, True, _) => True
    case (BvOp.Or, _, True) => True
    case (BvOp.Or, False, f) => f
    case (BvOp.Or, f, False) => f
    case (BvOp.Xor, True, f) => Not(f)
    case (BvOp.Xor, f, True) => Not(f)
    case (BvOp.Xor, False, f) => f
    case (BvOp.Xor, f, False) => f
    case (_, f, g) if f == g => if op == BvOp.Xor then False else f
    case (BvOp.And, _, _) => And(List(x, y))
    case (BvOp.Or, _, _) => Or(List(x, y))
    case _ => Not(Iff(x, y))

  /** `value` reduced modulo `2^width`: a fresh result `r` with
   *  `value = r + 2^width × k`, the overflow count `k` in `[lo, hi]`.
   */
  private def modulo(value: Term, width: Int, lo: BigInt, hi: BigInt): Term = value match
    case Num(v) => Num(v.mod(modulus(width)))
    case _ =>
      loweredOperations.getOrElseUpdate(
        ("modulo", List(value), List(width, lo, hi)), {
          val r = freshInt("bv", 0, modulus(width) - 1)
          // A few overflow counts are a choice for the SAT solver — `value = r`, or `value = r + 2^width` —
          // rather than an integer unknown `k` with `2^width` as its coefficient, on which the simplex
          // pivots into huge rationals and walks; a wide range of counts stays an unknown.
          if hi - lo < splitCases then
            define(Or((lo to hi).toList.map(k => IntEq(value, r + Num(k * modulus(width))))))
          else
            val k = freshInt("k", lo, hi)
            define(IntEq(value, r + k * modulus(width)))
          r
        }
      )

  /** Up to this many overflow counts, [[modulo]] is a disjunction of
   *  equalities.
   */
  private val splitCases = 4

  /** Whether the `width`-bit term is negative as a signed value: its top bit,
   *  as the atom `t ≥ 2^(width−1)` — a bound the solver decides, not an unknown
   *  of the simplex.
   */
  private def negative(t: Term, width: Int): Formula = t match
    case Num(v) => if v >= modulus(width - 1) then True else False
    case _ => Ge(t, Num(modulus(width - 1)))

  /** A constant defined by cases: `thn` when `cond`, `els` otherwise, within
   *  `[lo, hi]`; once per distinct case split at a level.
   */
  private def cases(tag: String, cond: Formula, thn: Term, els: Term, lo: BigInt, hi: BigInt): Term =
    loweredOperations.getOrElseUpdate(
      (tag, List(Term.boolean(cond), thn, els), List(lo, hi)), {
        val k = freshInt(tag, lo, hi)
        define(Implies(cond, IntEq(k, thn)))
        define(Implies(Not(cond), IntEq(k, els)))
        k
      }
    )

  /** `value = divisor × q + r` with `0 ≤ r < divisor` and `q ≤ quotientMax`:
   *  the pair `(q, r)`.
   */
  private def divide(value: Term, divisor: BigInt, quotientMax: BigInt): (Term, Term) = value match
    case Num(v) => (Num(v / divisor), Num(v.mod(divisor)))
    case _ =>
      loweredDivisions.getOrElseUpdate(
        (value, divisor, quotientMax), {
          val q = freshInt("q", 0, quotientMax)
          val r = freshInt("r", 0, divisor - 1)
          define(IntEq(value, q * divisor + r))
          (q, r)
        }
      )

  /** `bvsdiv`, `bvsrem` and `bvsmod` of `a` by the constant `c`, of signed
   *  value `T`: the truncating division of the signed value of `a` by `|T|`,
   *  `S = |T| × q + r` with `r` of the sign of `S` ([[divideSigned]]), then the
   *  quotient negated when `T < 0`, the remainder as it is, or the remainder
   *  moved to the sign of `T` (`r + T` when the signs differ and `r ≠ 0`, a
   *  choice bit `z` for the latter), each reduced modulo `2^width`. By zero, as
   *  the standard says: the quotient is all ones for `S ≥ 0` and one for
   *  `S < 0`, the remainders are `a`.
   */
  private def signedDivision(op: BvOp, a: Term, c: BigInt, width: Int): Term =
    val m = modulus(width)
    val t = if c >= m / 2 then c - m else c
    (a, op) match
      case (Num(v), _) =>
        val sv = if v >= m / 2 then v - m else v
        val result = op match
          case BvOp.Sdiv => if t.signum == 0 then (if sv.signum >= 0 then BigInt(-1) else BigInt(1)) else sv / t
          case BvOp.Srem => if t.signum == 0 then sv else sv % t
          case _ =>
            val r = if t.signum == 0 then sv else sv % t
            if r.signum == 0 || t.signum == 0 || r.signum == t.signum then r else r + t
        Num(result.mod(m))
      case (_, BvOp.Sdiv) if t.signum == 0 => cases("sdiv0", negative(a, width), Num(1), Num(m - 1), 1, m - 1)
      case (_, _) if t.signum == 0 => a
      case _ =>
        val (q, r) = divideSigned(a, width, t.abs)
        op match
          case BvOp.Sdiv => modulo(if t.signum > 0 then q else q * -1, width, -1, 0)
          case BvOp.Srem => modulo(r, width, -1, 0)
          case _ =>
            val differ = if t.signum > 0 then negative(a, width) else Not(negative(a, width)) // the signs differ
            val z = freshInt("z", 0, 1)
            define(Implies(Not(differ), IntEq(z, Num(0))))
            define(Implies(IntEq(r, Num(0)), IntEq(z, Num(0))))
            define(Implies(And(List(differ, Not(IntEq(r, Num(0))))), IntEq(z, Num(1))))
            modulo(r + z * t, width, -1, 0)

  /** The signed value `S` of `t` divided by `d > 0`: `S = d × q + r` with
   *  `|r| < d`, truncating — `r` of the sign of `S` (`r ≤ 0` when `t` is
   *  negative, `r ≥ 0` otherwise) — or, with `floor`, `r ∈ [0, d)`. Either
   *  determines `q` and `r`. The pair `(q, r)`.
   */
  private def divideSigned(t: Term, width: Int, d: BigInt, floor: Boolean = false): (Term, Term) =
    loweredSignedDivisions.getOrElseUpdate(
      (t, width, d, floor), {
        val half = modulus(width - 1)
        val q = freshInt("q", -(half / d) - 1, (half - 1) / d)
        val r = freshInt("r", if floor then 0 else -(d - 1), d - 1)
        define(IntEq(signed(t, width), q * d + r))
        if !floor then
          define(Implies(negative(t, width), Le(r, Num(0))))
          define(Implies(Not(negative(t, width)), Ge(r, Num(0))))
        (q, r)
      }
    )

  /** The signed value of an `width`-bit term: `t − 2^width` when its top bit is
   *  set, `t` otherwise — a constant defined by the two cases.
   */
  private def signed(t: Term, width: Int): Term = t match
    case Num(v) => Num(if v >= modulus(width - 1) then v - modulus(width) else v)
    case _ =>
      cases("signed", negative(t, width), t - Num(modulus(width)), t, -modulus(width - 1), modulus(width - 1) - 1)

  /** `(_ int_to_bv width) t`: `t mod 2^width` — a fresh result `r` in
   *  `[0, 2^width)` and an unbounded overflow count `k` with
   *  `t = r + 2^width × k`, both determined uniquely by `t`.
   */
  private def intToBv(t: Term, width: Int): Term = t match
    case Num(v) => Num(v.mod(modulus(width)))
    case _ =>
      loweredOperations.getOrElseUpdate(
        ("int_to_bv", List(t), List(width)), {
          val r = freshInt("bv", 0, modulus(width) - 1)
          val name = freshName("k")
          introduce(name, Sort.Int)
          val k = Const(name)
          define(IntEq(t, r + k * modulus(width)))
          r
        }
      )

  /** `c × t` modulo `2^width`, for `0 ≤ c < 2^width`. */
  private def times(t: Term, c: BigInt, width: Int): Term =
    if c.signum == 0 then Num(0) else modulo(t * c, width, 0, c - 1)

  /** `t` under a mask that is a run of low bits (`2^k − 1`) or of high bits
   *  (`2^width − 2^k`): the one division `t = 2^k × high + low` gives the and,
   *  the or and the xor as sums.
   */
  private def masked(op: BvOp, t: Term, mask: BigInt, width: Int): Option[Term] =
    val m = modulus(width)
    val k = (0 to width).find(k => mask == modulus(k) - 1 || mask == m - modulus(k))
    k.map { k =>
      val low = if k == width then t else if k == 0 then Num(0) else divide(t, modulus(k), m / modulus(k) - 1)._2
      val high = t - low
      val (kept, masked) = if mask == modulus(k) - 1 then (high, low) else (low, high)
      op match
        case BvOp.And => masked
        case BvOp.Or => kept + Num(mask)
        case _ => kept + (Num(mask) - masked)
    }

  /** Bits `i` down to `j` of `t`: `t = 2^j × q + low`,
   *  `q = 2^(i−j+1) × high + bits`.
   */
  private def extract(i: Int, j: Int, t: Term, width: Int): Term =
    val q = if j == 0 then t else divide(t, BigInt(2).pow(j), modulus(width - j) - 1)._1
    if i == width - 1 then q else divide(q, modulus(i - j + 1), modulus(width - i - 1) - 1)._2

  /** `t` extended by `k` copies of its sign bit: `t + (2^(width+k) − 2^width)`
   *  when it is negative, `t` otherwise.
   */
  private def signExtend(k: Int, t: Term, width: Int): Term =
    if k == 0 then t
    else
      t match
        case Num(v) => Num(if v >= modulus(width - 1) then v + modulus(width + k) - modulus(width) else v)
        case _ =>
          val extended = modulus(width + k) - modulus(width)
          cases("ext", negative(t, width), t + Num(extended), t, 0, modulus(width + k) - 1)

  /** A comparison as the solver decides it: the unsigned ones are the bounds as
   *  they stand; a signed one is Boolean structure over the two top bits and
   *  the unsigned comparison — `a <ₛ b` is `a` negative and `b` not, or both
   *  the same sign and `a < b` — with no unknown for a sign.
   */
  private def compare(op: BvCmpOp, a: Term, b: Term, width: Int): Formula =
    val (strict, flipped) = op match
      case BvCmpOp.Ult | BvCmpOp.Slt => (true, false)
      case BvCmpOp.Ule | BvCmpOp.Sle => (false, false)
      case BvCmpOp.Ugt | BvCmpOp.Sgt => (true, true)
      case BvCmpOp.Uge | BvCmpOp.Sge => (false, true)
    val (l, r) = if flipped then (b, a) else (a, b)
    val unsigned = if strict then Lt(l, r) else Le(l, r)
    if !op.signed then unsigned
    else
      val (nl, nr) = (negative(l, width), negative(r, width))
      Or(List(And(List(nl, Not(nr))), And(List(Iff(nl, nr), unsigned))))
