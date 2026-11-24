package io.bovel.vik.proofs

import java.nio.file.Files

import io.bovel.vik.Cpc

/** Writes the CPC proof of each script of a corpus whose last answer is
 *  `unsat`: `proofs/runMain io.bovel.vik.proofs.CpcCorpus <corpus> <out>
 *  [seconds] [plain]`, as [[Corpus]] reads them. Each proof is written as
 *  `Cnnnnn.cpc`, compact unless `plain` is given, for `proofs/cpc/check.sh`.
 *  Prints a line per script: its path, the file written, and what came of it —
 *  `written`, why no proof was written, or the answer when it is not `unsat`.
 */
object CpcCorpus:
  def main(args: Array[String]): Unit =
    val compact = !args.lift(3).contains("plain")
    Corpus.run(args) { (out, name, certificate) =>
      try
        Files.writeString(out.resolve(s"$name.cpc"), Cpc(certificate, compact))
        if sys.env.contains("CPC_CERTS") then Files.writeString(out.resolve(s"$name.cert"), certificate)
        "written"
      catch case e: Cpc.Unsupported => s"unsupported: ${String.valueOf(e.getMessage).take(200)}"
    }
