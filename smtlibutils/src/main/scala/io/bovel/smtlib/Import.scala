package io.bovel.smtlib

import java.nio.file.{Files, Path}

import scala.collection.mutable
import scala.jdk.CollectionConverters.*
import scala.util.Try

/** Imports SMT-LIB files into the corpus (see `corpus/README.md`):
 *  `sbt "smtlibutils/runMain io.bovel.smtlib.smt2import <origin> <source root> [files per family]"`.
 *  Origins: `cvc5` (`test/regress/cli`, answers in `; EXPECT:` lines, or the
 *  file's own statuses where it has none), `z3test` (`regressions/smt2`,
 *  answers in `.expected.out` files), `princess` (`testcases`, answers in each
 *  directory's `Answers` log), `smtinterpol` (`SMTInterpolTest/test`, statuses
 *  in the files), `submission` and `smt-lib`/`smt-lib-incremental` (statuses in
 *  the files), `cvc5-examples` (`examples/api/smtlib` of the cvc5 repository)
 *  and `z3guide` (`website/docs-smtlib` of the z3 guide's repository: every
 *  `z3` code block of its pages), the last two without answers — `statusstamp`
 *  supplies them. Every candidate is parsed: only the files in the supported
 *  fragment are copied, into `<logic>/<origin>/<family>__<file>.smt2`, with a
 *  header naming the origin, the original path and the license, and a
 *  `(set-info :status ...)` before each `check-sat` when the answers are known.
 */
@main def smt2import(origin: String, root: String, perFamily: Int = 0): Unit =
  Import.run(origin, Path.of(root), perFamily)

object Import:
  private val licenses = Map(
    "cvc5" -> "modified BSD, LICENSES/cvc5.txt",
    "cvc5-examples" -> "modified BSD, LICENSES/cvc5.txt",
    "z3guide" -> "MIT, LICENSES/z3guide.txt",
    "z3test" -> "MIT, LICENSES/z3test.txt",
    "princess" -> "BSD, LICENSES/princess.txt",
    "smtinterpol" -> "LGPL-3.0, LICENSES/smtinterpol.txt",
    "submission" -> "see the file's header",
    "smt-lib-incremental" -> "CC BY 4.0 (SMT-LIB release 2025, incremental, Zenodo 15493096)",
    "smt-lib" -> "CC BY 4.0 (SMT-LIB release 2025, non-incremental, Zenodo 16740866)"
  )
  private val maxSize = 200000L
  private val answers = Set("sat", "unsat", "unknown")

  /** A file to import: its text, the expected answers when they come from
   *  outside it, its family, and its file name when not the original's (a block
   *  cut out of a page).
   */
  final case class Candidate(
      rel: String,
      text: String,
      expected: Option[List[String]],
      family: String,
      name: String = ""
  )

  /** The directory of the corpus for a file: the smallest standard logic it
   *  fits ([[Logic.smallest]]), or, where z3 cannot tell, the logic it sets if
   *  standard, else a guess from what it declares.
   */
  def classify(text: String): String = Logic.smallest(text).getOrElse(fallback(text))

  private def fallback(text: String): String = Logic.claimed(text) match
    case List(name) if Logic.standard.contains(name) => name
    case _ =>
      if text.contains("declare-datatype") then "QF_DT"
      else if "\\(_ bv\\d+ \\d+\\)|\\(_ BitVec".r.findFirstIn(text).isDefined then "QF_BV"
      else if "\\bInt\\b".r.findFirstIn(text).isDefined then
        if "\\(declare-fun \\S+ \\([^)]".r.findFirstIn(text).isDefined || text.contains("declare-sort") then "QF_UFLIA"
        else "QF_LIA"
      else "QF_UF"

  /** The `z3` code blocks of a page of the z3 guide (not the `z3-duo`, `z3-py`,
   *  `z3-js` ones), each a script of its own.
   */
  private def guideBlocks(page: String): List[String] =
    "(?ms)^```z3(?: [^\n]*)?\n(.*?)^```".r.findAllMatchIn(page).map(_.group(1).nn).toList

  /** `02 - basiccommands.md` as `basiccommands`: the guide numbers its pages
   *  and sections.
   */
  private def guideSlug(file: String): String =
    file.stripSuffix(".md").replaceFirst("^\\d+ - ", "").replace(" ", "-").toLowerCase

  def candidates(origin: String, root: Path): List[Candidate] =
    val extension = if origin == "z3guide" then ".md" else ".smt2"
    val stream = Files.walk(root)
    val paths =
      try stream.iterator().asScala.filter(p => Files.isRegularFile(p) && p.toString.endsWith(extension)).toList.sorted
      finally stream.close()
    paths.flatMap { path =>
      val rel = root.relativize(path).toString
      val parts = rel.split("/").toList
      Try(Files.readString(path)).toOption.filter(_ => Files.size(path) <= maxSize).toList.flatMap { text =>
        if origin == "z3guide" then
          val family = guideSlug(parts.head)
          guideBlocks(text).zipWithIndex.collect {
            case (block, i) if block.contains("check-sat") =>
              Candidate(s"$rel (block ${i + 1})", block, None, family, s"${guideSlug(parts.last)}_${i + 1}.smt2")
          }
        else if !text.contains("check-sat") then None
        else
          origin match
            case "cvc5-examples" => Some(Candidate(rel, text, None, "examples"))
            case "cvc5" =>
              val options = "(?m)^; COMMAND-LINE: (.*)$".r.findAllMatchIn(text).flatMap(_.group(1).nn.split(" ")).toList
              val harmless = List(
                "--incremental",
                "--produce-models",
                "--produce-unsat-cores",
                "--lang",
                "-q",
                "--no-",
                "--check-",
                "--strings-exp",
                "--fmf",
                "--full-saturate",
                "--ee-mode",
                "--strict-parsing",
                "--model-u-print",
                "-o",
                "-i"
              )
              val expected =
                "(?m)^; EXPECT: (.*)$".r.findAllMatchIn(text).map(_.group(1).nn.trim).toList.filter(answers)
              if "(?m)^; (EXIT: [1-9]|EXPECT-ERROR|REQUIRES:)".r.findFirstIn(text).isDefined then None
              else if options.exists(o => o.startsWith("-") && !harmless.exists(o.startsWith)) then
                None // the answers may depend on it
              else if !text.contains("; EXPECT:") then
                // No `; EXPECT:` lines: cvc5's runner checks the `(set-info :status ...)` before each
                // check-sat, which the file keeps — read as `Script.expectedStatuses` reads it, the last
                // since the previous check-sat, so an old header's `unknown` does not count.
                Option.when(Try(Parser.parse(text).expectedStatuses.exists(_.isDefined)).getOrElse(false))(
                  Candidate(rel, text, None, if parts.length > 2 then parts(0) + "-" + parts(1) else parts(0))
                )
              else if expected.isEmpty || !expected.exists(answers) then None
              else if !expected.forall(answers) && !text.contains("get-value") && !text.contains("get-model") &&
                !text.contains("get-unsat-core")
              then None // a non-answer expectation with no value query: options or errors we do not model
              else
                Some(Candidate(
                  rel,
                  text,
                  Some(expected),
                  if parts.length > 2 then parts(0) + "-" + parts(1) else parts(0)
                ))
            case "z3test" =>
              val out = path.resolveSibling(path.getFileName.nn.toString.dropRight(5) + ".expected.out")
              Option.when(Files.exists(out))(
                Files.readAllLines(out).asScala.map(_.trim).filter(_.nonEmpty).toList.filter(answers)
              ).filter(_.nonEmpty)
                .map(e => Candidate(rel, text, Some(e), "regressions"))
            case "princess" =>
              val log = path.resolveSibling("Answers")
              Option.when(Files.exists(log))(Files.readString(log)).flatMap { answersLog =>
                val name = java.util.regex.Pattern.quote(path.getFileName.nn.toString)
                s"(?ms)^Loading $name \\.\\.\\.\\n(.*?)(?=^Loading |\\z)".r.findFirstMatchIn(
                  answersLog
                ).map(_.group(1).nn)
              }.map(_.linesIterator.map(_.trim).filter(answers).toList).filter(_.nonEmpty)
                .map(e => Candidate(rel, text, Some(e), parts(parts.length - 2)))
            case "smtinterpol" => // SMTInterpolTest/test/<family>/[subdirs/]file, statuses in the files
              Some(Candidate(rel, text, None, if parts.length > 1 then parts.init.mkString("__") else "root"))
            case "submission" => // <non-incremental|incremental>/<logic>/<family>/.../file
              val family =
                if parts.length > 3 then parts(2) else if parts.length > 1 then parts(parts.length - 2) else "root"
              Some(Candidate(rel, text, None, if parts.head == "incremental" then "incremental-" + family else family))
            case _ => // smt-lib, smt-lib-incremental: <logic>/<family>/[subdirs/]file
              val family = if parts.length > 2 then parts.slice(1, parts.length - 1).mkString("__")
              else if parts.length > 1 then parts(parts.length - 2) else "root"
              Some(Candidate(rel, text, None, family))
      }
    }

  /** `(set-info :status X)` before each `check-sat` (also `-assuming`,
   *  `-using`), `X` from `expected` in order.
   */
  def withStatuses(text: String, expected: List[String]): String =
    val checks = "\\(check-sat-assuming|\\(check-sat-using|\\(check-sat(?=[ )])".r
    // A check-sat inside a comment is no check-sat: a status spliced into `;(check-sat)` stayed in the
    // comment, made the command live, and shifted the answers of the real ones (issue 56).
    def commented(at: Int): Boolean = text.lastIndexOf(';', at) > text.lastIndexOf('\n', at)
    val out = StringBuilder()
    var last = 0
    var k = 0
    for m <- checks.findAllMatchIn(text) if !commented(m.start) do
      out ++= text.substring(last, m.start)
      out ++= s"(set-info :status ${expected.lift(k).getOrElse("unknown")})\n" + m.matched
      k += 1
      last = m.end
    out ++= text.substring(last)
    out.toString

  private val parallelism = 32
  private val loweringSeconds = 120L

  def run(origin: String, root: Path, perFamily: Int): Unit =
    val found = candidates(origin, root)
    val chosen =
      if perFamily > 0 then found.groupBy(_.family).values.flatMap(_.sortBy(_.text.length).take(perFamily)).toList
      else found
    val rejected = mutable.Map.empty[String, Int]
    var copied = 0
    // The parser reads the whole language; the fragment line is the lowering's, so both must pass — on a
    // pool of threads, the lowering being the cost; a candidate whose lowering outlasts the limit is
    // rejected as such (its thread runs on, so a few of them cost parallelism, not the run).
    val pool = java.util.concurrent.Executors.newFixedThreadPool(
      parallelism,
      r =>
        val t = new Thread(r)
        t.setDaemon(true)
        t
    )
    val lowered = chosen.map { c =>
      val content = s"; From $origin: ${c.rel} (${licenses(origin)})\n" +
        c.expected.fold(c.text)(withStatuses(c.text, _))
      // The file goes to the smallest logic it fits, and says so (`Logic.relabel`) where it set another.
      val outcome = pool.submit[Try[(String, String)]](() =>
        Try {
          io.bovel.vik.Lowering(Parser.parse(content))
          Logic.smallest(content) match
            case Some(logic) =>
              (logic, if Logic.claimed(content) == List(logic) then content else Logic.relabel(content, logic))
            case None => (fallback(content), content)
        }
      )
      (c, content, outcome)
    }
    for (c, content, outcome) <- lowered do
      Try(outcome.get(loweringSeconds, java.util.concurrent.TimeUnit.SECONDS)).flatten.recoverWith {
        case _: java.util.concurrent.TimeoutException =>
          scala.util.Failure(RuntimeException(s"lowering past $loweringSeconds s"))
      } match
        case scala.util.Success((logic, text)) =>
          val dir = Corpus.root.resolve(logic).resolve(origin)
          Files.createDirectories(dir)
          val file = if c.name.nonEmpty then c.name else Path.of(c.rel).getFileName.toString
          val name = s"${c.family}__$file".replace("/", "_")
          Files.writeString(dir.resolve(name), text)
          copied += 1
        case scala.util.Failure(e) =>
          val message = s"${e.getClass.getSimpleName}: ${e.getMessage}".take(60)
          rejected(message) = rejected.getOrElse(message, 0) + 1
    println(s"$origin: ${chosen.length} candidates, $copied in the fragment, copied")
    for (message, n) <- rejected.toList.sortBy(-_._2).take(15) do println(f"  rejected $n%5d  $message")
