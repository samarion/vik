package io.bovel.vik

import java.nio.file.{Files, Path}

import scala.jdk.CollectionConverters.*

import io.bovel.smtlib.Parser

/** Writes the Lean proof of each script of a corpus whose last answer is
 *  `unsat`, for `proofs/lean` to check: `vik/Test/runMain
 *  io.bovel.vik.LeanCorpus <corpus> <out> [seconds]`, the corpus a directory or
 *  a file listing the scripts' paths, each script solved with proofs within
 *  `seconds` (10 by default). Each proof is written as one file, `Cnnnnn.lean`,
 *  split into modules, `Cnnnnn/`, for `proofs/lean/check-modules.sh`, and for
 *  `native_decide`, `native/Cnnnnn.lean`, for `proofs/lean/check-native.sh`.
 *  Prints a line per script: its path, the file written, and what came of it —
 *  `written`, why no proof was written, or the answer when it is not `unsat`.
 */
object LeanCorpus:
  def main(args: Array[String]): Unit =
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
          session.keepLeanProofs = true
          val answers = session.run(script).filter(a => a == "sat" || a == "unsat" || a == "unknown")
          if answers.lastOption != Some("unsat") then answers.lastOption.getOrElse("no answer")
          else
            session.leanProof() match
              case Right(text) =>
                val header = s"import Vik\n\nnamespace Vik.Low.Exported.$name\n\nopen Vik.Low Vik.Surf Vik.Clausal\n\n"
                val full = header + text + s"\nend Vik.Low.Exported.$name\n"
                Files.writeString(out.resolve(s"$name.lean"), full)
                val dir = Files.createDirectories(out.resolve(name))
                for (file, content) <- LeanModules(name, full) do Files.writeString(dir.resolve(file), content)
                val native = Files.createDirectories(out.resolve("native"))
                Files.writeString(native.resolve(s"$name.lean"), LeanNative(full))
                "written"
              case Left(why) => s"no proof: ${why.linesIterator.nextOption.getOrElse("").take(200)}"
        catch case e: Throwable => s"error: ${e.getClass.getSimpleName}: ${String.valueOf(e.getMessage).take(200)}"
      println(s"$path\t$name\t$outcome")
