package io.bovel.vik.proofs

import java.nio.file.{Files, Path}

import scala.jdk.CollectionConverters.*

import io.bovel.smtlib.Parser
import io.bovel.vik.{Session, Solver}

/** The loop of the corpus drivers ([[LeanCorpus]], [[CpcCorpus]]): `args` are
 *  `<corpus> <out> [seconds]`, the corpus a directory or a file listing the
 *  scripts' paths, each script solved with proofs within `seconds` (10 by
 *  default). For each script whose last answer is `unsat`, `write` gets the
 *  output directory, the script's name `Cnnnnn` and the certificate, and says
 *  what came of it. Prints a line per script: its path, its name, and what came
 *  of it — `write`'s word, why there is no proof, or the answer when it is not
 *  `unsat`.
 */
object Corpus:
  def run(args: Array[String])(write: (Path, String, String) => String): Unit =
    val root = Path.of(args(0))
    val out = Path.of(args(1))
    val seconds = args.lift(2).fold(10L)(_.toLong)
    Files.createDirectories(out)
    val files =
      if Files.isDirectory(root) then
        Files.walk(root).iterator.asScala.filter(_.toString.endsWith(".smt2")).map(_.toString).toList.sorted
      else Files.readAllLines(root).asScala.toList.filter(_.nonEmpty)
    for (path, i) <- files.zipWithIndex do
      val name = f"C$i%05d"
      val outcome =
        try
          val script = Parser.parse(Files.readString(Path.of(path)))
          val session = Session(
            Solver(proofs = true),
            timeoutMs = Some(seconds * 1000),
            deadline = Some(System.nanoTime + seconds * 1000000000L)
          )
          session.keepProofs = true
          val answers = session.run(script).filter(a => a == "sat" || a == "unsat" || a == "unknown")
          if answers.lastOption != Some("unsat") then answers.lastOption.getOrElse("no answer")
          else
            session.proof() match
              case Right(certificate) => write(out, name, certificate)
              case Left(why) => s"no proof: ${why.linesIterator.nextOption().getOrElse("").take(200)}"
        catch case e: Throwable => s"error: ${e.getClass.getSimpleName}: ${String.valueOf(e.getMessage).take(200)}"
      println(s"$path\t$name\t$outcome")
