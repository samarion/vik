# Benchmarks

One [JMH](https://github.com/openjdk/jmh) project for all the modules, in [src/main/scala/io/bovel/bench](src/main/scala/io/bovel/bench):
a package per module with its benchmark class, and `evaluation` for the comparison with other solvers on SMT-LIB
files. The workloads and the results are kept per module:

| Module | Benchmark class | Workloads and results |
|---|---|---|
| `egraph` | `egraph.EGraphBench` | [results/egraph](results/egraph/README.md) |
| `cdclt` | `cdclt.CdcltBench` | [results/cdclt](results/cdclt/README.md) |
| `lia` | `lia.LiaBench` | [results/lia](results/lia/README.md) |
| `smtlib` | `smtlib.SExprBench` (the reader), `smtlib.SmtlibBench` (the parser and the printer) | [results/sexpr](results/sexpr/README.md), [results/smtlib](results/smtlib/README.md) |
| `vik` (random integer and datatype instances through the API) | `vik.UfliaBench`, `vik.AdtBench` | [results/smt](results/smt/README.md) |
| `evaluation` (VIK, z3, cvc5, princess and SMTInterpol in process on the SMT-LIB instances of the evaluation) | `evaluation.VikBench`, `Z3Bench`, `Z3TextBench`, `Cvc5Bench`, `PrincessBench`, `SmtInterpolBench`; `SolverCheck`, `ModelCheck`, `replaycheck` | [results/evaluation](results/evaluation/README.md), and [results/smt](results/smt/README.md) up to September 2026 |

## The checkers

`SolverCheck` runs the in-process solvers on the corpus files a regex selects (`/smt-lib/` by default) and
reports, check-sat by check-sat, every answer against the file's status for that check and every check on
which the solvers disagree, stamped or not — never the last answer against the first status, which on a
script of several checks was inverted. A file the replay cannot compile is reported as not checked, and
so is a solver's own limit; a solver has `VIK_CHECK_SECONDS` per file, 30 by default, on a thread the
tool leaves behind past it. The exit code says whether a disagreement was found, which CI runs on the
hand-written files with VIK. The replay itself covers declarations, terms, asserts, `push`/`pop`,
`reset-assertions` and `reset`, `check-sat`, `check-sat-assuming` and `get-model`; what it does not (sort parameters)
is reported, never answered.
`ModelCheck` takes every `get-model` of the selected files, puts VIK's model into the script in place of
the declarations it values — abstract elements declared and told apart — and asks z3 whether the script
is then satisfiable: a model that contradicts its script is not. `CoreCheck` does the same for every
`get-unsat-core`: the script with the named assertions outside the core dropped must be unsat for z3.
`replaycheck` times a replay. [platforms.sh](platforms.sh) runs a list of corpus files through the solver
on another platform — the Scala Native binary, `node bench/vik-node.mjs` (with `--stack-size`, since a
deep script overflows Node's default), a GraalVM image — against the files' statuses, and CI runs the
hand-written files that way on Scala.js and Scala Native; the corpus test itself is JVM only.
[fuzz.py](fuzz.py) is a differential fuzzer: random scripts, VIK (through `vik.FuzzBatch`) against z3 and cvc5,
run by hand; "Fuzzing" in [CONTRIBUTING.md](../CONTRIBUTING.md) says how to run it and reproduce a run.

## The evaluation page

[evaluate.sh](evaluate.sh) reproduces the two tables of
[the evaluation](../docs/_docs/evaluation.md) end to end and rewrites the page in place; the chart of the
page is drawn from those tables in the browser ([evaluation.js](../docs/_assets/js/evaluation.js)), so it
follows them. The warm table is a
JMH run of the suites of `io.bovel.bench.evaluation` — one per solver, `VikBench`, `Z3Bench` and `Z3TextBench`,
`Cvc5Bench`, `PrincessBench`, `SmtInterpolBench`, each listing the instances it takes and, commented, the ones
it does not and why. VIK and the other solvers are measured apart: the others are pinned, and a change to
VIK does not move their times.

```sh
bench/evaluate.sh vik      # VIK alone, both tables: the run a change to VIK calls for
bench/evaluate.sh others   # z3, cvc5, princess and SMTInterpol alone
bench/evaluate.sh all      # both families in one run
bench/evaluate.sh regen    # only regenerate the page from the history (seconds)
```

A second word keeps a run to one table: `warm`, the in-process JMH one (the z3 and cvc5 bindings of
fetch-native.sh), or `cold`, the process-per-question one (their binaries).

Every run joins the history in [results/evaluation](results/evaluation/README.md): for each table it
measured, a CSV file for VIK and one for the other solvers, named by the run's time and machine, with a row
of raw samples per solver and instance, and beside each a JSON file with the commit, the JDK and the
versions measured. A table shows each solver's
newest run and names, in its caption, the version and the time of each. The other solvers are therefore
due a new run when one of them or the JDK changes version, when a replay or the list of instances changes,
and on another machine; and `all` is the run to make when the columns of a table must come from the same
hours, the machine being shared.

Every single measurement holds to a ten-second budget. A warm operation past it is halted by a watchdog
([Budget.scala](src/main/scala/io/bovel/bench/evaluation/Budget.scala)) and noted on [timeouts.txt](timeouts.txt) —
committed, so the combination is refused on every later run and its cell reads 🐢. A solver that answers
neither `sat` nor `unsat` is noted the same way — reporting its `unknown` as `unsat` made a solver that
gave up look like one that decided — so the mark means "did not answer in ten seconds", either way; a fixed solver
earns its line's removal. A cold run is cut by `timeout 10` (in [cold.sh](cold.sh)) with the same cell.
The instances of both tables, in their order, are [evaluation-instances.txt](evaluation-instances.txt).

It checks its prerequisites first (the Python venv above, `bench/fetch-native.sh`) and fails with the
command to run; the cold run builds VIK's own binaries — the native one, the WebAssembly module, the GraalVM
image, the AOT cache — from the tree it measures, so no VIK column is stale or missing. What JMH and
`cold.sh` wrote stays in `target/evaluation/`; the history is what is committed, so it is the reference:
`regen` rebuilds the page from it, and a fresh machine reproduces the trends, not the exact milliseconds.
The runs up to September 2026, a JSON and a TSV file per day with every solver in each, are in
[results/smt](results/smt/README.md).

## Running

From the repository root:

```sh
python3 -m venv bench/.venv && bench/.venv/bin/pip install -r bench/requirements.txt   # once, for jmh2md.py
bench/fetch-native.sh                                                 # once, the native libraries of z3 and cvc5 (Linux x86-64)
sbt "bench/Jmh/run -l"                                                # lists the benchmarks
sbt "bench/Jmh/run .*EGraphBench.*"                                   # one module
sbt "bench/Jmh/run -rf json -rff target/jmh-result.json .*LiaBench.*" # with the JSON results
bench/.venv/bin/python bench/jmh2md.py target/jmh-result.json         # Markdown table with 95% confidence intervals
```

To sweep an arbitrary corpus subset one process per solver and instance, hand [cold.sh](cold.sh) a file
list and a timeout: `find corpus -name '*.smt2' | grep -E <regex> > /tmp/list && bench/cold.sh /tmp/list 1 60`.

To compare two builds of VIK file by file, over the whole corpus or the part a regex selects, `vik.CorpusRun`
runs the files warm in one JVM, several at a time, and writes the time and the answers of each to a tsv:
`sbt "bench/runMain io.bovel.bench.vik.CorpusRun 5 16 3 target/corpus-run.tsv /stainless/"` gives each file
5 s, on 16 threads, and keeps the third pass.

Configuration (annotations in the benchmark classes): 3 forks, 5 warmup and 5 measurement iterations of 1 s each
for the modules' benchmarks, 3 forks, 3 and 3 for the solver suites, average time per operation, which gives 95%
confidence intervals of a few percent; `-f 5 -wi 10` on the command line for a closer call. Every run gets a `timeout`: an sbt client can block on an unresponsive server (see
[external-issues.md](../external-issues.md)).

`jmh2md.py` prints a Markdown table with a 95% confidence interval computed from the raw per-iteration samples of all
forks (JMH's own `Error` column is a 99.9% interval). Its only dependency, `scipy`, is listed in
[requirements.txt](requirements.txt).

> [!WARNING]
> Do not chain `shutdown` after `Jmh/run` in the same sbt command string: with sbt 2's thin client the forked JMH
> process is still starting when the server shuts down and deletes the classpath copy under `target/bg-jobs/`.

### Calibrating the fuel

VIK's fuel (`:rlimit`, the `fuel` of `Solver.solve` and `Session`) counts work, not time: each kind of work in
`Solver.kinds` (SAT steps, decisions, conflicts, propagations and clause visits, the encoder's steps, the e-graph's
merges, explanations and disequality scans, the LIA solver's reasons and tableau entries, the words of rationals
past `Long` and the overflows into them) and the terms lowered have a cost, in units of about 4 ns of JVM time. The
costs come from a fit of the thread CPU time of the corpus files against their counts, which `CorpusRun` writes in
its last column:

```sh
sbt "bench/runMain io.bovel.bench.vik.CorpusRun 5 3 2 target/fuel-stainless.tsv /stainless/"
sbt "bench/runMain io.bovel.bench.vik.CorpusRun 5 3 1 target/fuel-others.tsv ^(?!.*/stainless/)"
bench/.venv/bin/python bench/fit-fuel.py target/fuel-stainless.tsv target/fuel-others.tsv
```

[fit-fuel.py](fit-fuel.py) prints how well the costs in the sources predict the CPU time, then the costs a
non-negative least squares fit gives and the files they predict worst. With the current costs, on the files of
at least 20 ms (a 2026 Linux x86-64 cloud machine, JDK 21, 3 threads), the fuel spent is within 2x of
the CPU time over 4 ns for 89% of the Stainless files and 85% of the others, and within 4x for 99% and 97%. The
worst are small files whose time the counts miss, at up to a few hundred times on files of 30 ms. Round the fitted
costs to powers of two or near, and keep the unit at about 4 ns, so that the fuel limits of the tests and the
docs keep their meaning.

## Results

One file per run under `results/<module>/`, named by date and host (plus a tag when a day has several runs), with the
raw JMH JSON next to it; each module's README holds its current results and the list of all runs. The runs of
the evaluation are kept differently, as the CSV files of [results/evaluation](results/evaluation/README.md).
