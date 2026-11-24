package io.bovel.vik

/** Sorts as the proof code names them: SMT-LIB text, a function sort
 *  `(-> S1 ... Sn R)` with `(-> S1 (-> S2 R))` the same as `(-> S1 S2 R)`, and
 *  the range of a bit-vector of `n` bits ([[Sort.IntRange]] from 0 to
 *  `2^n − 1`) `(_ BitVec n)`, which the certificate gives a sort of its own.
 */
private[vik] object SortText:
  def of(sort: Sort): String = sort match
    case Sort.Bool => "Bool"
    case Sort.Int => "Int"
    case Sort.Real => "Real"
    case Sort.IntRange(lower, upper) =>
      val n = (upper + 1).bitLength - 1
      if lower == 0 && upper + 1 == BigInt(2).pow(n) && n > 0 then s"(_ BitVec $n)" else "Int"
    case Sort.Named(_) => sort.text
    case Sort.Fun(args, result) => function(args.map(of), of(result))

  /** The parameter sorts and the result sort of a function sort, nested arrows
   *  in the result flattened; `None` for a value sort.
   */
  def arrow(sort: String): Option[(List[String], String)] =
    if !sort.startsWith("(-> ") || !sort.endsWith(")") then None
    else
      val parts = split(sort.drop(4).dropRight(1))
      if parts.length < 2 then None
      else
        arrow(parts.last) match
          case Some((more, result)) => Some((parts.init ++ more, result))
          case None => Some((parts.init, parts.last))

  /** The sort of a function of `params` to `result` (`result` itself when there
   *  are no parameters).
   */
  def function(params: List[String], result: String): String =
    if params.isEmpty then result
    else
      arrow(result) match
        case Some((more, r)) => function(params ++ more, r)
        case None => s"(-> ${params.mkString(" ")} $result)"

  /** The sort of a term of `sort` applied to `n` arguments; `?` when `sort` is
   *  not a function sort of that many.
   */
  def applied(sort: String, n: Int): String = arrow(sort) match
    case Some((params, result)) if n <= params.length => function(params.drop(n), result)
    case _ => "?"

  /** The items of `s` separated by spaces at parenthesis depth 0 and outside
   *  the bars of a quoted symbol.
   */
  private def split(s: String): List[String] =
    val items = List.newBuilder[String]
    var depth = 0
    var quoted = false
    var start = 0
    for i <- s.indices do
      s(i) match
        case '|' => quoted = !quoted
        case '(' if !quoted => depth += 1
        case ')' if !quoted => depth -= 1
        case ' ' if depth == 0 && !quoted =>
          if i > start then items += s.substring(start, i)
          start = i + 1
        case _ => ()
    if s.length > start then items += s.substring(start)
    items.result()
