package io.bovel.vik

import scala.collection.mutable.ArrayBuffer

/** Turns the Lean terms [[ProofExport]] writes into the S-expressions that
 *  `sexp%` (`proofs/lean/Vik/Sexp.lean`) reads back, as Lean's parser and
 *  elaborator are slow on large literals.
 *
 *  The terms are those of data: numerals, `true`, `false`, `none`, lists
 *  `[a, b]`, tuples `(a, b)`, anonymous constructors `⟨a, b⟩`, applications of
 *  `some` or of a constructor `.c a b`, and numerals with their type,
 *  `(-1 : Int)` or `((1 : Rat) / 2)`. A list, tuple or anonymous constructor
 *  becomes `(a b)`, an application `(c a b)`, a numeral with its type the
 *  numeral, and a fraction `1/2`.
 */
private[vik] object LeanSexp:

  final class Malformed(message: String) extends Exception(message)

  private def tokens(s: String): IndexedSeq[String] =
    val out = ArrayBuffer.empty[String]
    var i = 0
    while i < s.length do
      val c = s.charAt(i)
      if c.isWhitespace then i += 1
      else if "⟨⟩[](),:/".indexOf(c) >= 0 then
        out += c.toString; i += 1
      else if c == '-' || c.isDigit || c == '.' || c.isLetter || c == '_' then
        val j = i
        i += 1
        while i < s.length && { val d = s.charAt(i); d.isLetterOrDigit || d == '_' || d == '.' || d == '!' } do i += 1
        out += s.substring(j, i)
      else throw Malformed(s"unexpected '$c' in a Lean term")
    out.toIndexedSeq

  private final class Parser(ts: IndexedSeq[String]):
    private var i = 0
    def done: Boolean = i >= ts.length
    private def peek: String | Null = if i < ts.length then ts(i) else null
    private def next(): String =
      if i >= ts.length then throw Malformed("unexpected end of a Lean term")
      val t = ts(i)
      i += 1
      t
    private def expect(t: String): Unit =
      val n = next()
      if n != t then throw Malformed(s"expected '$t', got '$n'")

    private def startsPrimary: Boolean = peek match
      case null => false
      case p: String =>
        p == "[" || p == "(" || p == "⟨" || p.head == '.' || p.head == '-' || p.head.isLetterOrDigit || p.head == '_'

    def term(): String =
      val p = peek
      if p != null && (p.startsWith(".") || p == "some") then
        next()
        val name = if p.startsWith(".") then p.substring(1) else p
        val args = ArrayBuffer.empty[String]
        while startsPrimary do args += primary()
        if args.isEmpty then name else args.mkString(s"($name ", " ", ")")
      else primary()

    private def items(close: String): String =
      val xs = ArrayBuffer.empty[String]
      if peek != close then
        xs += term()
        while peek == "," do
          next()
          xs += term()
      expect(close)
      xs.mkString("(", " ", ")")

    private def primary(): String =
      val p = next()
      p match
        case "[" => items("]")
        case "⟨" => items("⟩")
        case "(" =>
          val x = term()
          if peek == ":" then
            next(); next(); expect(")")
            if peek == "/" then
              next(); s"$x/${next()}"
            else x
          else if peek == "/" then
            next()
            val d = next()
            expect(")")
            s"$x/$d"
          else if peek == "," then
            val xs = ArrayBuffer(x)
            while peek == "," do
              next()
              xs += term()
            expect(")")
            xs.mkString("(", " ", ")")
          else
            expect(")")
            x
        case _ => if p.startsWith(".") then p.substring(1) else p

  /** The S-expression of a Lean term. */
  def apply(term: String): String =
    val p = Parser(tokens(term))
    val s = p.term()
    if !p.done then throw Malformed(s"trailing text in a Lean term: $term")
    s

  /** A section of a certificate, `(name (field value) …)`, from the Lean terms
   *  of a structure's fields: `sexp%` reads the part after `name`.
   */
  def section(name: String, fields: Seq[(String, String)]): String =
    fields.map((f, v) => s"($f ${apply(v)})").mkString(s"($name\n  ", "\n  ", ")")
