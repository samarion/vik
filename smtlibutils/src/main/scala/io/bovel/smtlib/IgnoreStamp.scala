package io.bovel.smtlib

import java.nio.file.{Files, Path}
import java.util.concurrent.{Executors, TimeUnit}

import scala.jdk.CollectionConverters.*

/** Brings `corpus/ignore.txt` up to date with what the solver does today: runs
 *  the corpus under the rules of `CorpusTest` ([[CorpusCheck]]) and rewrites
 *  the list where a file's standing changed.
 *
 *    - A listed file that passes loses its line.
 *    - A file that fails without a line gets one: `timeout (5 s limit)`,
 *      `wrong: ...` for an answer against its status, `model: ...` for a model
 *      that fails its check, or the error it ends on.
 *    - A listed file that fails in another way than its line says (a `model:`
 *      file that now times out, a timeout that now answers wrongly) gets the
 *      new reason. One that fails the same way keeps its line as it is, with
 *      the words and the issue number a person wrote: a generated reason has
 *      neither, and is for a person to complete.
 *    - A line that names no file of the corpus goes.
 *
 *  The files run four at a time, with the test's fuel and budget, and every
 *  change is confirmed by a second run of the file alone, which must come to
 *  the same verdict: time is the one thing here that depends on the machine. A
 *  file listed for its time leaves the list only when it passes that second run
 *  within half the budget, so that it does not come back at the next load.
 *
 *  The `skip` files exhaust the heap or the stack, or run on past the budget,
 *  and would take this JVM with them as they would the test's. Each is probed
 *  in a JVM of its own instead, with half the heap of the tests and killed soon
 *  after the budget. One that ends by itself there, without an error of the
 *  heap or the stack, needs no skipping any more: its line goes when it passes
 *  within half the budget, and else becomes the reason of that run. The others
 *  keep their lines.
 *
 *  The changes are printed; review the diff and commit it:
 *  `sbt "smtlibutils/runMain io.bovel.smtlib.ignorestamp [regex]"` — all the
 *  corpus, or the files whose path the regex finds (`/stainless/`, `^QF_BV/`).
 */
@main def ignorestamp(args: String*): Unit =
  val regex = args.headOption.getOrElse("").r
  val path = Corpus.root.resolve("ignore.txt")
  val header = Files.readAllLines(path).asScala.toList.takeWhile(_.startsWith("#"))
  val listed = Corpus.ignored
  val files = Corpus.files
  val (skipped, selected) =
    files.filter(regex.findFirstIn(_).isDefined).partition(listed.get(_).exists(_.startsWith("skip")))
  println(s"${selected.length} files, ${IgnoreRun.budgetMs / 1000} s each, and ${skipped.length} `skip` files probed")

  val pool = Executors.newFixedThreadPool(4)
  val first = selected.map(f => f -> pool.submit(() => IgnoreRun.run(f)))
  val probes = skipped.map(f => f -> pool.submit(() => IgnoreRun.probe(f)))
  pool.shutdown()
  // The files whose line would change, by the first run: each one again, alone.
  val candidates = first.map((f, run) => (f, run.get())).filter((f, run) => !IgnoreRun.stands(listed.get(f), run))

  var entries = listed.filter((f, _) => files.contains(f))
  for f <- listed.keys.toList.sorted if !files.contains(f) do println(s"removed  $f (no such file)")
  for (f, before) <- candidates do
    val run = IgnoreRun.run(f)
    val was = listed.get(f)
    val seconds = f"${run.ms / 1000.0}%.1f s"
    if run.kind != before.kind then println(s"unstable $f (${before.kind}, then ${run.kind} alone): left as it is")
    else if run.kind != "passes" then
      entries += f -> run.reason
      println(was.fold(s"added    $f\t${run.reason}")(old => s"changed  $f\t$old -> ${run.reason}"))
    else if IgnoreRun.kind(was.get) == "other" && run.ms > IgnoreRun.budgetMs / 2 then
      println(s"kept     $f\t${was.get} (passes in $seconds, too close to the limit)")
    else
      entries -= f
      println(s"removed  $f (passes in $seconds; was: ${was.get})")
  for (f, probe) <- probes; run <- probe.get() do
    val seconds = f"${run.ms / 1000.0}%.1f s"
    if run.kind == "passes" && run.ms <= IgnoreRun.budgetMs / 2 then
      entries -= f
      println(s"removed  $f (passes in $seconds in a JVM of its own; was: ${listed(f)})")
    else
      val reason = if run.kind == "passes" then IgnoreRun.timeout else run.reason
      entries += f -> reason
      println(s"changed  $f\t${listed(f)} -> $reason (ended by itself in $seconds)")
  for (f, run) <- first if !run.get().matches do
    println(s"expect   $f: the responses are not its `; EXPECT:` lines (see expectstamp)")

  if entries == listed then println("corpus/ignore.txt is up to date")
  else
    Files.writeString(
      path,
      (header ++ entries.toList.map((f, reason) => s"$f\t$reason").sorted).mkString("", "\n", "\n")
    )
    println(s"corpus/ignore.txt: ${listed.size} lines before, ${entries.size} now")
  System.exit(0) // whatever the files left behind

private object IgnoreRun:
  val budgetMs = 5000L // the test's budget where the machine is one's own

  /** What a run came to: `passes`, or the way it failed — `wrong`, `model`, or
   *  `other` for no answer in time and for an error — with the reason to list
   *  it under, and its time.
   */
  final case class Run(kind: String, reason: String, ms: Long, matches: Boolean)

  val timeout = s"timeout (${budgetMs / 1000} s limit)"

  /** The way a line says its file fails. */
  def kind(reason: String): String =
    if reason.startsWith("wrong") then "wrong" else if reason.startsWith("model") then "model" else "other"

  /** Whether a run leaves the file's standing as the list has it. */
  def stands(reason: Option[String], run: Run): Boolean = reason match
    case None => run.kind == "passes"
    case Some(why) => run.kind == kind(why)

  private def short(text: String, length: Int): String =
    val line = text.replaceAll("\\s+", " ")
    if line.length > length then line.take(length) + "..." else line

  /** One file as the test runs it: a thread of its own, left behind when it is
   *  still running at the budget (the deadline does not reach everywhere).
   */
  def run(file: String): Run =
    @volatile var result: Option[Run] = None
    val start = System.nanoTime
    def ms = (System.nanoTime - start) / 1000000
    val worker = Thread(() =>
      val run =
        try
          val check = CorpusCheck(file, CorpusCheck.fuel, start + budgetMs * 1000000, expects = true)
          if check.sound then Run("passes", "", ms, check.matches)
          else if check.wrong then
            // What the search answered, where the model check may have made an `unknown` of it.
            val i = check.searched.zip(check.expected).indexWhere((g, e) => g.isDefined && e.isDefined && g != e)
            val said = if check.searched(i).get then "sat" else "unsat"
            Run("wrong", s"wrong: check-sat ${i + 1} answers $said against its status", ms, true)
          else if check.failedCheck.isDefined then
            val error = check.failedCheck.get.stripPrefix("(error \"model check: ").stripSuffix("\")")
            Run("model", s"model: ${short(error, 150)}", ms, true)
          else if ms >= budgetMs * 9 / 10 then Run("other", timeout, ms, true)
          else Run("other", short(s"not answered: ${check.message}", 160), ms, true)
        catch
          case e: (Exception | StackOverflowError | OutOfMemoryError) =>
            Run("other", short(s"${e.getClass.getSimpleName}: ${e.getMessage}", 160), ms, true)
      result = Some(run)
    )
    worker.setDaemon(true)
    worker.start()
    worker.join(budgetMs)
    result.getOrElse(Run("other", timeout, ms, true))

  /** A `skip` file in a JVM of its own, with half the tests' heap, killed three
   *  seconds past the budget: its run, or `None` when it did not end by itself
   *  or ended on an error of the heap or the stack — what `skip` is for.
   */
  def probe(file: String): Option[Run] =
    val java = Path.of(System.getProperty("java.home"), "bin", "java").toString
    val output = Files.createTempFile("ignoreprobe", ".txt")
    val process = ProcessBuilder(
      java,
      "-Xmx1g",
      "-cp",
      System.getProperty("java.class.path"),
      "io.bovel.smtlib.ignoreprobe",
      file
    ).redirectErrorStream(true).redirectOutput(output.toFile).start()
    val ended = process.waitFor(budgetMs + 3000, TimeUnit.MILLISECONDS)
    if !ended then process.destroyForcibly().waitFor()
    val lines = Files.readAllLines(output).asScala.toList
    Files.delete(output)
    if !ended then None
    else
      lines.map(_.split("\t", -1)).collectFirst { case Array("ended", kind, ms, reason) =>
        Run(kind, reason, ms.toLong, true)
      }

/** One file for [[ignorestamp]]'s probe of a `skip` file, in this JVM: a line
 *  with its run when it ended by itself, and nothing when it was left behind at
 *  the budget or ended on an error of the heap or the stack.
 */
@main def ignoreprobe(file: String): Unit =
  val run = IgnoreRun.run(file)
  val contained = run.reason != IgnoreRun.timeout || run.ms < IgnoreRun.budgetMs
  val crashed = List("OutOfMemoryError", "StackOverflowError").exists(run.reason.startsWith)
  if contained && !crashed then println(s"ended\t${run.kind}\t${run.ms}\t${run.reason}")
  System.exit(0)
