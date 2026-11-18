package io.bovel.vik

import scala.collection.mutable.ArrayBuffer

/** An exported Lean proof checked by `native_decide` rather than the kernel:
 *  the checkers run as compiled code, far faster, at the cost of trusting
 *  Lean's compiler (the axiom `Lean.ofReduceBool`).
 *
 *  The definitions become computable, `sexp%` splits their large lists into
 *  definitions of about `vik.sexp.chunk` atoms (Lean compiles one large term
 *  slowly), and each theorem the kernel checked in slices is one
 *  `native_decide`. `proofs/lean/check-native.sh` checks the file against the
 *  compiled library.
 */
private[vik] object LeanNative:

  private val chunk = 1000

  /** The proof `text` for `native_decide`. */
  def apply(text: String): String =
    val lines = text.linesIterator.toVector
    val out = ArrayBuffer.empty[String]
    var i = 0
    while i < lines.length do
      val l = lines(i)
      if l.startsWith("noncomputable def ") then
        out += l.stripPrefix("noncomputable ")
        i += 1
      else if l == "set_option maxHeartbeats 0" then
        out += l
        out += s"set_option vik.sexp.chunk $chunk"
        i += 1
      else if l.startsWith("theorem ") && l.endsWith(":= by decide +kernel") then
        // a slice: the whole theorem is checked at once
        i += 1
      else if l.startsWith("theorem ") && l.endsWith(" :=") && !l.contains("{") &&
        lines.lift(i + 1).exists(n => n.contains("_of_slices "))
      then
        out += l + " by native_decide"
        i += 1
        while i < lines.length && lines(i).startsWith(" ") do i += 1
      else
        out += l
        i += 1
    out.mkString("", "\n", "\n")
