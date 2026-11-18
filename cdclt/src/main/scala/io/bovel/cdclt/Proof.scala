package io.bovel.cdclt

import scala.collection.mutable.ArrayBuffer

/** A clausal proof of an `Unsat` of [[Solver]], in the style of LRAT (Cruz-
 *  Filipe, Heule, Hunt, Kaufmann and Schneider-Kamp 2017): a list of steps,
 *  each a clause with its justification, referring to earlier steps by their
 *  index.
 *
 *    - `Input`: a clause given to [[Solver.addClause]] (`origin` is the
 *      client's account of where it comes from, when it gives one);
 *    - `Lemma`: a clause of the theory, a conflict or an explanation — valid in
 *      the theory, which the proof takes on trust (`certificate` is the
 *      theory's account of it, when it gives one);
 *    - `Derived`: a clause that follows from the clauses of its `hints` by unit
 *      propagation alone: with the clause false, each hint in turn is unit, and
 *      the last one false.
 *
 *  [[conclusion]] is the step of the empty clause, or after an `Unsat` under
 *  assumptions, of the clause of their negations (the failed ones, see
 *  [[Solver.unsatCore]]); `-1` before any `Unsat`. [[check]] checks the derived
 *  steps.
 */
final class Proof:
  import Proof.Step

  val steps = ArrayBuffer.empty[Step]
  var conclusion: Int = -1

  def add(step: Step): Int =
    steps += step
    steps.length - 1

  /** Checks every derived step up to the conclusion by unit propagation over
   *  its hints, every lemma with `lemma` and every input with `input` (`None`
   *  when it holds): `None` when they all hold, the first that does not
   *  otherwise.
   */
  def check(
      lemma: Step.Lemma => Option[String] = _ => None,
      input: Step.Input => Option[String] = _ => None
  ): Option[String] =
    var value = new Array[Byte](0) // per literal index: 1 true, -1 false
    def assign(l: Lit, trail: ArrayBuffer[Lit]): Unit =
      if l.index + 2 > value.length then value = java.util.Arrays.copyOf(value, 2 * (l.index + 2))
      value(l.index) = 1
      value(l.neg.index) = -1
      trail += l
    def valueOf(l: Lit): Int = if l.index < value.length then value(l.index) else 0
    def rup(clause: Array[Lit], hints: Array[Int], at: Int): Option[String] =
      val trail = ArrayBuffer.empty[Lit]
      try
        var tautology = false
        for l <- clause do if valueOf(l) > 0 then tautology = true else if valueOf(l) == 0 then assign(l.neg, trail)
        if tautology then None
        else
          var i = 0
          var refuted = false
          while i < hints.length && !refuted do
            val h = hints(i)
            if h < 0 || h >= at then return Some(s"step $at: hint $h is not an earlier step")
            var unassigned = -1 // the index of the open literal
            var open = 0
            var satisfied = false
            for l <- steps(h).clause do
              val v = valueOf(l)
              if v > 0 then satisfied = true
              else if v == 0 && unassigned != l.index then
                unassigned = l.index
                open += 1
            if satisfied then return Some(s"step $at: hint $h is satisfied")
            if open == 0 then refuted = true
            else if open == 1 then assign(Lit.fromIndex(unassigned), trail)
            else return Some(s"step $at: hint $h is not unit")
            i += 1
          if refuted then None else Some(s"step $at: the hints do not refute the clause")
      finally
        for l <- trail do
          value(l.index) = 0
          value(l.neg.index) = 0
    var i = 0
    var error: Option[String] = if conclusion < 0 then Some("no conclusion") else None
    while i <= conclusion && error.isEmpty do
      error = steps(i) match
        case Step.Derived(clause, hints) => rup(clause, hints, i)
        case l: Step.Lemma => lemma(l).map(e => s"step $i: the lemma ${l.clause.map(_.show).mkString(" ")}: $e")
        case in: Step.Input => input(in).map(e => s"step $i: the input ${in.clause.map(_.show).mkString(" ")}: $e")
      i += 1
    error

object Proof:
  enum Step:
    case Input(clause: Array[Lit], origin: AnyRef | Null = null)
    case Lemma(clause: Array[Lit], certificate: AnyRef | Null = null)
    case Derived(clause: Array[Lit], hints: Array[Int])

    def clause: Array[Lit]
