package io.bovel.vik

/** A sort as the solver knows it: what [[Lowering]] makes of a sort of the
 *  script, and what [[Solver.declare]] takes. The sorts of SMT-LIB live in
 *  `io.bovel.smtlib`, as its terms do; these say what the solver itself knows
 *  of a term. An array is the function of its index to its elements, which a
 *  `select` applies. A bit-vector sort is an [[Sort.IntRange]]: the solver
 *  knows the integers its terms range over and nothing of its operations, which
 *  the lowering turns into arithmetic on those integers.
 */
enum Sort:
  case Bool
  case Int
  case Real

  /** The integers from `lower` to `upper`, both included: `(_ BitVec n)` is
   *  `IntRange(0, 2^n − 1)`. The solver gives these bounds to every term of the
   *  sort, whoever made the term (`Encoder.assertSorts`).
   */
  case IntRange(lower: BigInt, upper: BigInt)

  /** An uninterpreted sort or a datatype: which of the two a name is, the
   *  declarations say.
   */
  case Named(name: String)

  /** The sort of a function symbol or of an array, its parameters and its
   *  result: [[Sort.fun]] keeps nested arrows flattened.
   */
  case Fun(args: List[Sort], result: Sort)

  /** The sort as a lowered script writes it. `(_ IntRange l u)` is VIK's own:
   *  SMT-LIB has no sort for a range of the integers.
   */
  def text: String = this match
    case Bool => "Bool"
    case Int => "Int"
    case Real => "Real"
    case IntRange(lower, upper) => s"(_ IntRange ${Printer.print(Term.Num(lower))} ${Printer.print(Term.Num(upper))})"
    // `|a b|` when the name needs its bars; an instance of a parametric sort keeps the parenthesised
    // text the parser names it by, `(List Int)`, which is how it is written.
    case Named(name) => if name.startsWith("(") then name else io.bovel.smtlib.sexpr.SExpr.SSymbol(name).toString
    case Fun(args, result) => s"(-> ${(args.map(_.text) :+ result.text).mkString(" ")})"

  override def toString: String = text

  /** The parameter sorts and the result of a function sort; `None` for a value
   *  sort.
   */
  def arrow: Option[(List[Sort], Sort)] = this match
    case Fun(args, result) => Some((args, result))
    case _ => None

  /** The sort of a term of this sort applied to its first `n` arguments, as the
   *  solver applies a function symbol or reads an array of arrays: what is left
   *  of the function sort, `(-> A B C)` after one argument is `(-> B C)`.
   *  `None` when it is not a function sort of at least that many.
   */
  def after(n: scala.Int): Option[Sort] = this match
    case Fun(args, result) if n <= args.length => Some(Sort.fun(args.drop(n), result))
    case _ => None

  /** The array sort that a function sort stands for, as SMT-LIB writes it:
   *  `(-> I E)` is `(Array I E)`, `(-> I J E)` is `(Array I (Array J E))`; a
   *  value sort is its own text.
   */
  def arrayText: String = this match
    case Fun(args, result) => args.foldRight(result.text)((index, element) => s"(Array ${index.text} $element)")
    case _ => text

object Sort:
  /** The function sort of `args` to `result` (`result` itself when there are
   *  none), nested arrows in the result flattened: `(-> A (-> B C))` is
   *  `(-> A B C)`.
   */
  def fun(args: List[Sort], result: Sort): Sort =
    if args.isEmpty then result
    else
      result match
        case Fun(more, r) => Fun(args ++ more, r)
        case _ => Fun(args, result)
