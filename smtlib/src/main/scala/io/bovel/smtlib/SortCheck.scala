package io.bovel.smtlib

/** Checks the sorts of parsed terms, in one pass over each tree. The parser's
 *  own `sortOf` asks only what picks a tree, so an ill-sorted script used to
 *  reach the solver and get a definite answer (corpus file
 *  `alpha-beta_reduce-932bafde0fe6`, a Function1 equated with an `Any`,
 *  answered `sat` against its `:status unsat`). z3 and cvc5 refuse such a
 *  script, and so does this.
 *
 *  Beyond SMT-LIB, an Int fits where a Real is expected, as in z3: scripts rely
 *  on it. z3's other coercions, a Real to an Int and a Bool to a number, are
 *  refused, as cvc5 does: a Real read as an Int where the solver does not
 *  truncate it gave `sat` where z3 says `unsat`.
 *
 *  Arity of the theory operations stays with the lowering, which draws the
 *  fragment's line.
 */
private[smtlib] final class SortCheck(
    functions: scala.collection.Map[String, Sort],
    macros: scala.collection.Map[String, (List[(String, Sort)], Sort, Term | Formula)]
):
  private type Env = Map[String, Sort]

  /** Checks that `actual` fits where `expected` is wanted. */
  def expect(actual: Sort, expected: Sort, where: => String): Unit =
    if actual != expected && !(actual == Sort.Int && expected == Sort.Real) then
      throw Smt2Error(s"$where: ${expected.text} expected, not ${actual.text}")

  private def numeric(s: Sort, where: => String): Unit =
    if s != Sort.Int && s != Sort.Real then throw Smt2Error(s"$where: a number expected, not ${s.text}")

  /** The common sort of two terms that must agree: `=`, `distinct`, `ite`. */
  private def join(a: Sort, b: Sort, where: => String): Sort =
    if a == b then a
    else if (a == Sort.Int && b == Sort.Real) || (a == Sort.Real && b == Sort.Int) then Sort.Real
    else throw Smt2Error(s"$where: ${a.text} and ${b.text} do not mix")

  private def width(s: Sort, where: => String): Int = s match
    case Sort.BitVec(w) => w
    case _ => throw Smt2Error(s"$where: a bit-vector expected, not ${s.text}")

  /** The sort of `t`, every subterm checked. */
  def term(t: Term, env: Env): Sort = t match
    case Term.Const(name) => symbol(name, env)
    case Term.Numeral(_) => Sort.Int
    case Term.Decimal(_, _) => Sort.Real
    case Term.Bits(_, w) => Sort.BitVec(w)
    case Term.App(Term.Const(name), args) =>
      val (params, result) = rank(name, env)
      if params.length != args.length then throw Smt2Error(s"$name expects ${params.length} arguments")
      for (a, p) <- args.zip(params) do expect(term(a, env), p, s"an argument of $name")
      result
    case Term.App(fun, _) => throw Smt2Error(s"not a function: $fun")
    case Term.ArithApp(op, args) => arith(op, args.map(term(_, env)))
    case Term.BvApp(op, args) => bv(op, args.map(term(_, env)))
    case Term.Select(a, i) =>
      term(a, env) match
        case Sort.Array(index, element) =>
          expect(term(i, env), index, "the index of a select")
          element
        case s => throw Smt2Error(s"select on ${s.text}")
    case Term.Store(a, i, v) =>
      term(a, env) match
        case s @ Sort.Array(index, element) =>
          expect(term(i, env), index, "the index of a store")
          expect(term(v, env), element, "the value of a store")
          s
        case s => throw Smt2Error(s"store on ${s.text}")
    case Term.MapArray(op, arrays) =>
      val sorts = arrays.map(term(_, env))
      sorts.head match
        case s @ Sort.Array(_, Sort.Bool) =>
          for other <- sorts.tail do if other != s then throw Smt2Error(s"(_ map $op) on ${s.text} and ${other.text}")
          s
        case s => throw Smt2Error(s"(_ map $op) on ${s.text}")
    case Term.ConstArray(sort, v) =>
      sort match
        case Sort.Array(_, element) =>
          expect(term(v, env), element, "the value of a constant array")
          sort
        case s => throw Smt2Error(s"a constant array of ${s.text}")
    case Term.Ite(c, thn, els) =>
      formula(c, env)
      join(term(thn, env), term(els, env), "the branches of an ite")
    case Term.Let(bindings, body) => term(body, bound(bindings, env))
    case Term.Bool(f) =>
      formula(f, env)
      Sort.Bool

  /** Checks every subterm of `f`. */
  def formula(f: Formula, env: Env): Unit = f match
    case Formula.True | Formula.False => ()
    case Formula.Not(a) => formula(a, env)
    case Formula.And(args) => args.foreach(formula(_, env))
    case Formula.Or(args) => args.foreach(formula(_, env))
    case Formula.Implies(args) => args.foreach(formula(_, env))
    case Formula.Xor(args) => args.foreach(formula(_, env))
    case Formula.Iff(args) => args.foreach(formula(_, env))
    case Formula.Eq(args) => args.map(term(_, env)).reduceOption(join(_, _, "the sides of ="))
    case Formula.Distinct(args) => args.map(term(_, env)).reduceOption(join(_, _, "the arguments of distinct"))
    case Formula.Cmp(op, args) => for a <- args do numeric(term(a, env), op.name)
    case Formula.BvCmp(op, a, b) =>
      if width(term(a, env), op.name) != width(term(b, env), op.name) then
        throw Smt2Error(s"${op.name}: the widths differ")
    case Formula.Ite(c, thn, els) =>
      formula(c, env)
      formula(thn, env)
      formula(els, env)
    case Formula.IsConstructor(c, a) =>
      val (params, _) = rank(s"(_ is $c)", env)
      expect(term(a, env), params.head, s"(_ is $c)")
    case Formula.IsInt(a) => numeric(term(a, env), "is_int")
    case Formula.Let(bindings, body) => formula(body, bound(bindings, env))
    case Formula.Pred(t) => expect(term(t, env), Sort.Bool, "a formula")

  private def symbol(name: String, env: Env): Sort =
    env.get(name).orElse(functions.get(name)).orElse(macros.get(name).map(_._2))
      .getOrElse(throw Smt2Error(s"unknown symbol $name"))

  /** The argument sorts and the result of a symbol applied. */
  private def rank(name: String, env: Env): (List[Sort], Sort) =
    macros.get(name).filter(_ => !env.contains(name)) match
      case Some((params, result, _)) => (params.map(_._2), result)
      case None =>
        val s = symbol(name, env)
        s.arrow.getOrElse(throw Smt2Error(s"${s.text} is not a function sort: $name"))

  /** The environment of a `let`'s body; its values read the outer one. */
  private def bound(bindings: List[(String, Term | Formula)], env: Env): Env =
    env ++ bindings.map {
      case (name, t: Term) => name -> term(t, env)
      case (name, f: Formula) =>
        formula(f, env)
        name -> Sort.Bool
    }

  private def arith(op: ArithOp, args: List[Sort]): Sort =
    for s <- args do numeric(s, op.name)
    op match
      case ArithOp.Div | ArithOp.ToReal => Sort.Real
      case ArithOp.ToInt => Sort.Int
      case ArithOp.IntDiv | ArithOp.Mod =>
        for s <- args do expect(s, Sort.Int, op.name)
        Sort.Int
      case _ => if args.contains(Sort.Real) then Sort.Real else Sort.Int

  private def bv(op: BvOp, args: List[Sort]): Sort = op match
    case BvOp.IntToBv(n) =>
      for s <- args do expect(s, Sort.Int, op.name)
      Sort.BitVec(n)
    case BvOp.Concat => Sort.BitVec(args.map(width(_, op.name)).sum)
    case _ =>
      val widths = args.map(width(_, op.name)).distinct
      if widths.length != 1 then throw Smt2Error(s"${op.name}: the widths differ, or no argument")
      val w = widths.head
      op match
        case BvOp.Comp => Sort.BitVec(1)
        case BvOp.UbvToInt | BvOp.SbvToInt => Sort.Int
        case BvOp.Extract(i, j) =>
          if j > i || i >= w then throw Smt2Error(s"(_ extract $i $j) of ${w} bits")
          Sort.BitVec(i - j + 1)
        case BvOp.ZeroExtend(k) => Sort.BitVec(w + k)
        case BvOp.SignExtend(k) => Sort.BitVec(w + k)
        case BvOp.Repeat(k) =>
          if k < 1 then throw Smt2Error(s"(_ repeat $k): at least one copy")
          Sort.BitVec(w * k)
        case _ => Sort.BitVec(w)
