package io.bovel.bench.vik

import io.bovel.smtlib.{Corpus, Parser}
import io.bovel.vik.{Command, Lowering, Solver}

/** Prints the wall time of every `check-sat` of a script, one solver for the
 *  whole run: `sbt "bench/runMain io.bovel.bench.vik.checktimes file.smt2"`.
 *  The shape of the curve tells persistence stories: flat means checks are
 *  independent, growing means state accumulates.
 */
@main def checktimes(file: String): Unit =
  val script = Lowering(Parser.parse(java.nio.file.Files.readString(Corpus.find(file))))
  val solver = Solver()
  var check = 0
  for command <- script.commands do
    command match
      case Command.DeclareFun(name, argSorts, sort, auxiliary) => solver.declare(name, argSorts, sort, auxiliary)
      case Command.DeclareDatatypes(datatypes) => datatypes.foreach(solver.declare)
      case Command.Assert(formula) => solver.assert(formula)
      case Command.Push(n) => for _ <- 0 until n do solver.push()
      case Command.Pop(n) => for _ <- 0 until n do solver.pop()
      case Command.CheckSat =>
        check += 1
        val start = System.nanoTime()
        val result = solver.solve()
        val ms = (System.nanoTime() - start) / 1e6
        println(f"check $check%3d: $ms%9.2f ms  $result")
      case _ => ()
