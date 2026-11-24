package io.bovel.bench.vik

import java.io.{FileDescriptor, FileOutputStream, PrintStream}
import java.nio.file.{Files, Path}

import io.bovel.smtlib.Parser
import io.bovel.vik.Session

/** VIK's responses to the scripts of the differential fuzzer (`bench/fuzz.py`),
 *  many scripts in one JVM:
 *  `java -cp <bench/runtimeClasspath> io.bovel.bench.vik.FuzzBatch <seconds> <file>...`.
 *  For each file it prints a line `=== <file>`, then the responses, one per
 *  line (a model on one line): `(crash <class>: <message>)` when the run threw,
 *  `(hung)` when it was still running two seconds past its deadline. Each
 *  script runs in a session of its own with `seconds` as its deadline, on a
 *  daemon thread with the stack a deep script asks of the parser; a hung one is
 *  left behind.
 */
object FuzzBatch:
  def main(args: Array[String]): Unit =
    val seconds = args(0).toLong
    val out = PrintStream(FileOutputStream(FileDescriptor.out), true, "UTF-8")
    for file <- args.iterator.drop(1) do
      out.println(s"=== $file")
      @volatile var responses: Option[List[String]] = None
      val worker = Thread(
        null,
        () =>
          responses = Some(
            try
              val script = Parser.parse(Files.readString(Path.of(file)))
              Session.run(script, deadline = Some(System.nanoTime + seconds * 1000000000L))
            catch
              case e: Throwable =>
                val message = String.valueOf(e.getMessage).replaceAll("\\s+", " ").take(300)
                List(s"(crash ${e.getClass.getName}: $message)")
          ),
        "fuzz",
        1L << 29
      )
      worker.setDaemon(true)
      worker.start()
      worker.join(seconds * 1000 + 2000)
      responses match
        case Some(lines) => lines.foreach(line => out.println(line.replaceAll("\\s*\n\\s*", " ")))
        case None => out.println("(hung)")
    System.exit(0) // whatever was left behind
