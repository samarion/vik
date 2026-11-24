package io.bovel.vik

import scala.collection.mutable.ArrayBuffer

/** An S-expression of a certificate: an atom, or a list of S-expressions. The
 *  atoms of certificates are numerals, fractions and names, without quotes.
 */
enum Sexp:
  case Atom(text: String)
  case Lst(items: Vector[Sexp])

  /** The S-expression as text, on one line. */
  override def toString: String = this match
    case Atom(t) => t
    case Lst(xs) => xs.mkString("(", " ", ")")

object Sexp:

  /** Not an S-expression, or not a certificate a driver reads. */
  final class Malformed(message: String) extends Exception(message)

  /** The sections of a certificate ([[ProofExport]]), by name: the items of
   *  each after its name.
   */
  def sections(certificate: String): Map[String, Vector[Sexp]] = parse(certificate) match
    case Lst(Atom("vik-proof") +: Atom(v) +: rest) if v == ProofExport.version.toString =>
      rest.map {
        case Lst(Atom(name) +: fields) => name -> fields
        case s => throw Malformed(s"not a section: ${s.toString.take(100)}")
      }.toMap
    case Lst(Atom("vik-proof") +: v +: _) => throw Malformed(s"unknown version $v")
    case _ => throw Malformed("not a Vik certificate")

  /** The items of a list. */
  def items(s: Sexp): Vector[Sexp] = s match
    case Lst(xs) => xs
    case _ => throw Malformed(s"not a list: ${s.toString.take(100)}")

  /** The S-expression of `text`, which holds exactly one. */
  def parse(text: String): Sexp =
    var i = 0
    def skip(): Unit = while i < text.length && text.charAt(i).isWhitespace do i += 1
    def one(): Sexp =
      skip()
      if i >= text.length then throw Malformed("unexpected end of an S-expression")
      text.charAt(i) match
        case '(' =>
          i += 1
          val xs = ArrayBuffer.empty[Sexp]
          skip()
          while i < text.length && text.charAt(i) != ')' do
            xs += one()
            skip()
          if i >= text.length then throw Malformed("unclosed '('")
          i += 1
          Lst(xs.toVector)
        case ')' => throw Malformed(s"unexpected ')' at $i")
        case _ =>
          val j = i
          while i < text.length && { val c = text.charAt(i); !c.isWhitespace && c != '(' && c != ')' } do i += 1
          Atom(text.substring(j, i))
    val s = one()
    skip()
    if i < text.length then throw Malformed(s"trailing text at $i")
    s
