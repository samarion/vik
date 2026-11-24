package io.bovel.vik.proofs

import java.nio.file.Files

/** Writes the Lean proof of each script of a corpus whose last answer is
 *  `unsat`, for `proofs/lean` to check: `proofs/runMain
 *  io.bovel.vik.proofs.LeanCorpus <corpus> <out> [seconds]`, as [[Corpus]]
 *  reads them. Each proof is written as one file, `Cnnnnn.lean`, split into
 *  modules, `Cnnnnn/`, for `proofs/lean/check-modules.sh`, and for
 *  `native_decide`, `native/Cnnnnn.lean`, for `proofs/lean/check-native.sh`.
 *  Prints a line per script: its path, the file written, and what came of it —
 *  `written`, why no proof was written, or the answer when it is not `unsat`.
 */
object LeanCorpus:
  def main(args: Array[String]): Unit = Corpus.run(args) { (out, name, certificate) =>
    val full = Lean(certificate, s"Vik.Low.Exported.$name")
    Files.writeString(out.resolve(s"$name.lean"), full)
    val dir = Files.createDirectories(out.resolve(name))
    for (file, content) <- LeanModules(name, full) do Files.writeString(dir.resolve(file), content)
    val native = Files.createDirectories(out.resolve("native"))
    Files.writeString(native.resolve(s"$name.lean"), LeanNative(full))
    "written"
  }
