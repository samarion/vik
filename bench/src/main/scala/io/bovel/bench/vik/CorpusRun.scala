package io.bovel.bench.vik

import java.lang.management.ManagementFactory
import java.nio.file.{Files, Path}
import java.util.concurrent.Executors

import scala.jdk.CollectionConverters.*

import io.bovel.smtlib.{Corpus, Parser}
import io.bovel.vik.{Session, Solver}

/** Runs corpus files through VIK, warm, in one JVM, and writes how long each
 *  took and what it answered:
 *  `sbt "bench/runMain io.bovel.bench.vik.CorpusRun <seconds per file> <threads> <passes> <output tsv> [regex] [--proofs]"`.
 *  The regex selects files among the whole corpus (`/stainless/`, `^QF_BV/`;
 *  all of them by default); an absolute directory in its place is run instead,
 *  for files outside the corpus — the sessions `bench/import-stainless.py` is
 *  about to import. `--proofs` has the solver record proofs. The tsv has a line
 *  per file of the last pass, the earlier ones being the warm-up: its path, the
 *  wall-clock milliseconds, the CPU milliseconds of the file's thread, the work
 *  (as the fuel counts it, `Session.spent`: the same on every machine for a
 *  file that finishes), the kilobytes the thread allocated (nearly the same on
 *  every machine), then `ok`, `timeout` or the error, then the answers as `s`,
 *  `u` and `?`, then the work by kind (`Session.statistics`, `kind=count`
 *  separated by spaces: what the costs of `Solver.kinds` are fitted to).
 *
 *  The times are for comparing two builds file by file, not for a table: the
 *  files share the JVM, its compiler and its collector, `threads` at a time.
 *  The budget is the session's deadline, which ends a search; a file that is
 *  still running two seconds past it is somewhere the deadline does not reach,
 *  and is left behind on its thread, which it keeps along with its memory. The
 *  files that `corpus/ignore.txt` says to `skip` do just that, enough of them
 *  to fill the heap, and are left out.
 */
object CorpusRun:
  def main(arguments: Array[String]): Unit =
    val proofs = arguments.contains("--proofs")
    val args = arguments.filterNot(_ == "--proofs")
    val seconds = args(0).toLong
    val threads = args(1).toInt
    val passes = args(2).toInt
    val files: List[(String, Path)] = args.lift(4).map(Path.of(_)) match
      case Some(directory) if directory.isAbsolute && Files.isDirectory(directory) =>
        val stream = Files.walk(directory)
        try
          stream.iterator().asScala.map(_.toString).filter(_.endsWith(".smt2")).toList.sorted.map(f => f -> Path.of(f))
        finally stream.close()
      case _ =>
        val regex = args.lift(4).getOrElse("").r
        val skipped = Corpus.ignored.filter(_._2.startsWith("skip")).keySet
        val selected = Corpus.files.filter(regex.findFirstIn(_).isDefined)
        System.err.println(s"${selected.count(skipped)} files left out: `skip` in corpus/ignore.txt")
        selected.filterNot(skipped).map(f => f -> Corpus.root.resolve(f))
    var last = Vector.empty[String]
    for pass <- 1 to passes do
      val pool = Executors.newFixedThreadPool(threads)
      val lines = files.map((name, path) => pool.submit(() => s"$name\t${run(path, seconds, proofs)}"))
      pool.shutdown()
      last = lines.map(_.get()).toVector
      System.err.println(s"pass $pass: ${files.length} files, ${last.map(_.split("\t")(1).toLong).sum} ms")
    Files.write(Path.of(args(3)), last.asJava)
    System.exit(0) // whatever the files left behind

  /** One file in a session of its own: the milliseconds, the CPU milliseconds,
   *  the steps, the kilobytes, the outcome and the answers, as the tsv has
   *  them. The thread has the stack a deep script asks of the parser.
   */
  private def run(path: Path, seconds: Long, proofs: Boolean): String =
    var outcome = "timeout"
    var answers = ""
    @volatile var cpu = 0L
    @volatile var kb = 0L
    @volatile var session: Session | Null = null
    val threads = ManagementFactory.getThreadMXBean.asInstanceOf[com.sun.management.ThreadMXBean]
    val start = System.nanoTime
    val worker = Thread(
      null,
      () =>
        val cpuStart = threads.getCurrentThreadCpuTime
        val bytesStart = threads.getCurrentThreadAllocatedBytes
        try
          val script = Parser.parse(Files.readString(path))
          val s = Session(Solver(proofs = proofs), deadline = Some(start + seconds * 1000000000L))
          session = s
          val responses = s.run(script)
          answers = responses.collect { case "sat" => "s"; case "unsat" => "u"; case "unknown" => "?" }.mkString
          outcome = "ok"
        catch
          case _: StackOverflowError => outcome = "stackoverflow"
          case _: OutOfMemoryError => outcome = "oom"
          case e: Throwable =>
            outcome = s"${e.getClass.getSimpleName}: ${e.getMessage}".replaceAll("\\s+", " ").take(160)
        finally
          cpu = (threads.getCurrentThreadCpuTime - cpuStart) / 1000000
          kb = (threads.getCurrentThreadAllocatedBytes - bytesStart) / 1024
      ,
      "corpusrun",
      1L << 29
    )
    worker.setDaemon(true)
    worker.start()
    worker.join(seconds * 1000 + 2000)
    val ms = (System.nanoTime - start) / 1000000
    // A file left behind has not set its CPU time yet: read it from here, from the thread's start.
    if worker.isAlive then
      cpu = threads.getThreadCpuTime(worker.threadId) / 1000000
      kb = threads.getThreadAllocatedBytes(worker.threadId) / 1024
    val s = session
    val statistics = if s == null then "" else s.statistics.map((k, v) => s"$k=$v").mkString(" ")
    s"$ms\t$cpu\t${if s == null then 0L else s.spent}\t$kb\t$outcome\t$answers\t$statistics"
