package io.bovel.smtlib

import io.bovel.vik.Session

/** One run of a corpus file, held to what the file says: the rules that
 *  `CorpusTest` enforces and that `ignorestamp` records in `corpus/ignore.txt`.
 *
 *  `expected` are the statuses before each `check-sat` and `got` the answers;
 *  `failedCheck` is the error of the first model that fails its check
 *  (`Session`'s `checkModels`), where the answer is then `unknown`; `searched`
 *  are the answers of the search, before that check: `sat` where a model failed
 *  it; `matches` says the responses are the file's `; EXPECT:` lines, when it
 *  has some and queries values (see `expectstamp`).
 */
final case class CorpusCheck(
    expected: List[Option[Boolean]],
    got: List[Option[Boolean]],
    failedCheck: Option[String],
    searched: List[Option[Boolean]],
    matches: Boolean
):
  /** Every `check-sat` answered `sat` or `unsat`. */
  def answered: Boolean = got.length == expected.length && got.forall(_.isDefined)

  /** An answer against its status: a soundness bug, whatever the file's
   *  standing. A `sat` against an `unsat` status counts when the model check
   *  turned it into `unknown` too: the search was wrong all the same, and
   *  answers so with the check off.
   */
  def wrong: Boolean = searched.zip(expected).exists((g, e) => g.isDefined && e.isDefined && g != e)

  /** Answered as the statuses say, with models that pass their check. */
  def sound: Boolean = answered && !wrong && failedCheck.isEmpty

  def passes: Boolean = sound && matches

  def message: String =
    s"expected ${CorpusCheck.show(expected)}, got ${CorpusCheck.show(got)}" + failedCheck.fold("")(e => s", and $e")

object CorpusCheck:
  /** The fuel of each `check-sat`: about 80 s of the JVM's time, above the
   *  wall-clock budget, which is about the machine.
   */
  val fuel = 20_000_000_000L

  /** Runs `file` (a path relative to the corpus) in a session of its own, with
   *  `fuel` per `check-sat` and no search past `deadline`, a point in
   *  `System.nanoTime`. The `; EXPECT:` lines are compared when `expects` is
   *  set.
   */
  def apply(file: String, fuel: Long, deadline: Long, expects: Boolean): CorpusCheck =
    val text = Corpus.read(file)
    val script = Parser.parse(text)
    val responses = Session.run(script, fuel = fuel, deadline = Some(deadline), checkModels = true)
    val expected = text.linesIterator.filter(_.startsWith("; EXPECT: ")).map(_.drop(10)).toList
    val failed = (r: String) => r.startsWith("(error \"model check")
    // Each answer with whether the model-check error follows it.
    val answers = responses.zip(responses.drop(1).map(failed) :+ false).collect {
      case ("sat", _) => (Some(true), false)
      case ("unsat", _) => (Some(false), false)
      case ("unknown", caught) => (None, caught)
    }
    CorpusCheck(
      script.expectedStatuses,
      answers.map(_._1),
      responses.find(failed),
      answers.map((answer, caught) => if caught then Some(true) else answer),
      !expects || expected.isEmpty ||
        !List("(get-value", "(get-model", "(get-unsat-core", "(get-assertions").exists(text.contains) ||
        responses == expected
    )

  private def show(answers: List[Option[Boolean]]): String =
    answers.map(_.map(if _ then "sat" else "unsat").getOrElse("unknown")).mkString(",")
