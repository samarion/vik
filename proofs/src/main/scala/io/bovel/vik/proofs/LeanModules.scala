package io.bovel.vik.proofs

import scala.collection.mutable.ArrayBuffer

/** Splits an exported Lean proof into modules, for Lean to check its slices in
 *  parallel, each in a process of its own: Lean keeps what the kernel computes
 *  for the whole of a file, which on a large proof takes more memory than one
 *  process can have.
 *
 *  `Data` holds the definitions, each `S…` module one theorem the kernel checks
 *  by `decide +kernel`, and `Main` the theorems that put them together. The
 *  modules of `name` are `name.Data`, `name.S…` and `name.Main`, for
 *  `proofs/lean/check-modules.sh` to check.
 */
object LeanModules:

  /** The modules of the proof `text`, each its file name and content. */
  def apply(name: String, text: String): List[(String, String)] =
    val lines = text.linesIterator.toVector
    val firstDef = lines.indexWhere(_.startsWith("noncomputable def "))
    if firstDef < 0 then throw IllegalArgumentException("no definitions in the proof")
    val header = lines.take(firstDef).filterNot(_.startsWith("import ")).mkString("\n")
    val end = lines.reverseIterator.find(_.startsWith("end ")).getOrElse("")
    val data = ArrayBuffer.empty[String]
    val slices = ArrayBuffer.empty[(String, String)]
    val main = ArrayBuffer.empty[String]
    var i = firstDef
    while i < lines.length do
      val l = lines(i)
      if l.startsWith("noncomputable def ") then
        // a definition, to the line that closes its S-expression
        var j = i
        while j < lines.length && !lines(j).endsWith(")\"") do j += 1
        data ++= lines.slice(i, j + 1)
        data += ""
        i = j + 1
      else if l.startsWith("theorem ") && l.endsWith(":= by decide +kernel") then
        slices += (l.stripPrefix("theorem ").takeWhile(c => c != ' ' && c != ':') -> l)
        i += 1
      else
        if l != end then main += l
        i += 1
    val module = (body: String, imports: Seq[String]) =>
      imports.map(m => s"import $m").mkString("\n") + "\n\n" + header + "\n" + body + "\n" + end + "\n"
    (s"Data.lean" -> module(data.mkString("\n"), Seq("Vik"))) ::
      slices.toList.map((t, l) => s"S_$t.lean" -> module(l + "\n", Seq(s"$name.Data"))) :::
      List("Main.lean" -> module(main.mkString("\n"), s"$name.Data" +: slices.map(t => s"$name.S_${t._1}").toSeq))
