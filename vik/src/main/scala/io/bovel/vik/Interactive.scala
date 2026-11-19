package io.bovel.vik

import java.io.{PrintStream, Reader}

/** A [[Session]] that reads its commands from a stream as they arrive and
 *  answers each at once: what a tool that drives a solver process over pipes
 *  (`z3 -in`) waits for.
 *
 *  Beyond the commands a [[Session]] plays:
 *    - `(set-option :print-success true)` makes every command that answers
 *      nothing else answer `success`, as the SMT-LIB standard says;
 *    - `(get-proof)` answers, with `proofs`, the certificate of the last
 *      `check-sat` or `check-sat-assuming` that answered `unsat`, the
 *      S-expression `(vik-proof 1 ...)` of [[Session.proof]], which the
 *      `proofs` project writes as Lean files;
 *    - `(exit)` stops reading.
 *
 *  A command that fails answers `(error "...")`, and the session goes on.
 */
final class Interactive(proofs: Boolean = false):
  private val session = Session(Solver(proofs = proofs))
  // The proof of an `unsat` is written at the check: `check-sat-assuming` pops its assumptions right
  // after, and the proof is made of them.
  session.keepProofs = proofs
  // A model is asked for after its `check-sat`, which must keep it: there is no script to look ahead in.
  session.solver.produceModels = true
  private var printSuccess = false

  /** Answers the commands of `in` on `out`, until `(exit)` or the end of `in`.
   */
  def serve(in: Reader, out: PrintStream): Unit =
    val commands = Interactive.commands(in)
    var done = false
    while !done && commands.hasNext do
      val text = commands.next()
      val head = Interactive.head(text)
      if head == "exit" then
        if printSuccess then out.println("success")
        done = true
      else
        answer(head, text).foreach(out.println)
        out.flush()
    out.flush()

  /** The responses to one command, given as text with its head symbol. */
  def answer(head: String, text: String): List[String] =
    try
      head match
        case "set-option" if Interactive.option(text).exists(_._1 == ":print-success") =>
          printSuccess = Interactive.option(text).exists(_._2 == "true")
          List("success")
        case "set-option" if Interactive.option(text).exists(_._1 == ":produce-proofs") =>
          val wanted = Interactive.option(text).exists(_._2 == "true")
          if wanted && !proofs then List("(error \"proofs need the --proofs flag\")")
          else success
        case "get-proof" =>
          if !proofs then List("(error \"proofs need the --proofs flag\")")
          else
            session.proof() match
              case Right(certificate) => List(certificate)
              case Left(why) => List(s"(error ${Interactive.quote(why)})")
        case _ =>
          val responses = session.run(text)
          if responses.isEmpty then success else responses
    catch
      case e: Exception =>
        val message = Option(e.getMessage).getOrElse(e.getClass.getSimpleName)
        List(s"(error ${Interactive.quote(message)})")

  private def success: List[String] = if printSuccess then List("success") else Nil

object Interactive:
  /** The complete top-level S-expressions of `in`, as text, each as soon as its
   *  closing parenthesis is read: string literals, quoted symbols and comments
   *  taken into account.
   */
  def commands(in: Reader): Iterator[String] = new Iterator[String]:
    private var nextCommand: Option[String] = None
    private var ended = false

    def hasNext: Boolean =
      if nextCommand.isEmpty && !ended then nextCommand = read()
      nextCommand.nonEmpty

    def next(): String =
      if !hasNext then throw java.util.NoSuchElementException("no more commands")
      val c = nextCommand.get
      nextCommand = None
      c

    private def read(): Option[String] =
      val text = StringBuilder()
      var depth = 0
      var inString = false
      var inQuoted = false
      var inComment = false
      var c = in.read()
      while c != -1 do
        val ch = c.toChar
        if inComment then
          if ch == '\n' then
            inComment = false
            text += ch
        else
          text += ch
          if inString then
            if ch == '"' then inString = false // `""` inside reads as end and start
          else if inQuoted then
            if ch == '|' then inQuoted = false
          else
            ch match
              case '"' => inString = true
              case '|' => inQuoted = true
              case ';' =>
                text.deleteCharAt(text.length - 1)
                inComment = true
              case '(' => depth += 1
              case ')' =>
                depth -= 1
                if depth == 0 then return Some(text.toString.trim)
              case _ => ()
        c = in.read()
      ended = true
      val rest = text.toString.trim
      if rest.isEmpty then None else Some(rest)

  /** The head symbol of a command: `check-sat` of `(check-sat)`. */
  def head(text: String): String =
    text.dropWhile(c => c == '(' || c.isWhitespace).takeWhile(c => !c.isWhitespace && c != '(' && c != ')')

  /** The keyword and value of a `set-option` command. */
  def option(text: String): Option[(String, String)] =
    text.stripPrefix("(").stripSuffix(")").trim.split("\\s+").toList match
      case "set-option" :: key :: value :: _ => Some((key, value))
      case _ => None

  /** `s` as an SMT-LIB string literal, its quotes doubled. */
  def quote(s: String): String = "\"" + s.replace("\"", "\"\"") + "\""
