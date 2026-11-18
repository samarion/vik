package io.bovel.smtlib

import scala.concurrent.{Await, Future}
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.duration.Duration

import io.bovel.vik.{Session, Solver}

/** The proofs of the corpus's `unsat` answers, one test per file that the
 *  corpus test answers (not on `corpus/ignore.txt`) and that has an `unsat`
 *  status: every `check-sat` answered `unsat` has a proof whose derivations
 *  check, and so do the certificates of the theory lemmas that come with one.
 *  `VIK_PROOFS_FILTER`, a regex, keeps the files whose path it matches.
 */
class ProofsTest extends munit.FunSuite:
  override val munitTimeout = Duration(30, "min")
  private val fuel = 2000000L
  private val budget = Duration(5000L, "ms")
  private val filter = sys.env.getOrElse("VIK_PROOFS_FILTER", "").r
  private val ignored = Corpus.ignored

  for
    file <- Corpus.files
    if filter.findFirstIn(file).isDefined && !ignored.contains(file)
    text = Corpus.read(file)
    if text.contains(":status unsat")
  do
    test(file):
      val outcome = Await.result(
        Future {
          val script = Parser.parse(text)
          val deadline = Some(System.nanoTime() + budget.toNanos)
          val session = Session(Solver(proofs = true), fuel = fuel, deadline = deadline)
          val errors = scala.collection.mutable.ArrayBuffer.empty[String]
          for command <- script.commands do
            // One command at a time: each proof is checked before the next command changes it.
            if session.run(Script(List(command))).contains("unsat") then
              session.solver.proof match
                case None => errors += "an unsat without a proof"
                case Some(_) => errors ++= session.checkProof()
          errors.toList
        },
        budget * 2
      )
      assert(outcome.isEmpty, outcome.mkString("; "))
