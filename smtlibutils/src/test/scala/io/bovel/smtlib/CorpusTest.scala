package io.bovel.smtlib

import scala.concurrent.{Await, Future}
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.duration.Duration
import scala.jdk.CollectionConverters.*
import scala.util.Try

/** The corpus of SMT-LIB files (`corpus/`, see its README), one test per file:
 *  the answers must be the statuses in the file, within a fuel per `check-sat`
 *  (conflicts and branches: deterministic, the same on every machine) and
 *  within five seconds of wall clock — the budget the benchmarks also hold to;
 *  a file over either goes to `corpus/ignore.txt`, nobody waits on it. Every
 *  `sat` is model-checked (`Session`'s `checkModels`): each assertion in force
 *  must be true in the model, as lowered and as written. A file on
 *  `corpus/ignore.txt` (out of fuel or time, a wrong answer, a model that fails
 *  its check, an unsupported feature) is expected to fail, with a tenth of the
 *  fuel unless its model is the problem; when it passes, the test asks for its
 *  line to be removed.
 */
class CorpusTest extends munit.FunSuite:
  override val munitTimeout = Duration(30, "min")
  private val ignoredFuel = 1_000_000L // enough to notice a file that became easy
  /** The wall-clock guard: five seconds, the budget of the benchmarks, where
   *  the machine is one's own; CI sets a hard limit above it
   *  (`VIK_CORPUS_BUDGET_MS`, see build.sbt), since a file at the edge of the
   *  budget is caught here, not on a shared runner.
   */
  // The wall a file may take. The property is how the forked JVM tests carry it; the variable is how a
  // run with no JVM to configure gets it — the suites in the native image (`graal/nativeImageTestRun`).
  private val budget = Duration(
    Option(System.getProperty("vik.corpus.budgetMs")).orElse(sys.env.get("VIK_CORPUS_BUDGET_MS"))
      .map(_.toLong).getOrElse(5000L),
    "ms"
  )
  private val ignored = Corpus.ignored

  test("ignore.txt is sorted"):
    val lines = java.nio.file.Files.readAllLines(Corpus.root.resolve("ignore.txt")).asScala.toList
      .filter(l => l.nonEmpty && !l.startsWith("#"))
    assertEquals(lines, lines.sorted, "corpus/ignore.txt: keep the lines sorted (byte order)")

  test("ignore.txt names files of the corpus"):
    val files = Corpus.files.toSet
    val stale = ignored.keys.filterNot(files).toList.sorted
    assert(stale.isEmpty, s"corpus/ignore.txt: no such files: ${stale.mkString(", ")}")

  for file <- Corpus.files do
    val reason = ignored.get(file)
    test(if reason.exists(_.startsWith("skip")) then file.ignore else munit.TestOptions(file)):
      // The budget, as a wall-clock guard under the fuel, and as the solver's own deadline for the whole
      // script: a run over it is failed from outside, and the search stops by itself a step later — a
      // thread left running keeps its memory, and a script of many check-sats, each with a deadline of
      // its own, ran on for minutes and exhausted the fork's heap on CI.
      val outcome = Try {
        Await.result(
          Future {
            // A `model:` file is answered: its fuel is the full one, for the check to be reached. A file
            // with `; EXPECT:` lines (stamped by `expectstamp`) holds every response to them, unless listed.
            val reduced = reason.exists(!_.startsWith("model"))
            CorpusCheck(
              file,
              if reduced then ignoredFuel else CorpusCheck.fuel,
              System.nanoTime() + budget.toNanos,
              expects = reason.isEmpty
            )
          },
          budget
        )
      }
      reason match
        case None => assert(outcome.get.passes, outcome.get.message)
        case Some(why) =>
          // An ignored file may run out of fuel or time, or fail as its `wrong:` or `model:` line says; it
          // may not answer against its status under another reason — that is a wrong answer filed as a timeout.
          for check <- outcome.toOption do
            assert(
              !check.wrong || why.startsWith("wrong"),
              s"${check.message}: a wrong answer, not what ignore.txt says ($why)"
            )
          assert(
            outcome.toOption.forall(!_.passes),
            s"passes now: remove it from corpus/ignore.txt, by hand or with `ignorestamp` (was: $why)"
          )
