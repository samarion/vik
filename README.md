# The Verification Intermediate Kit (VIK)

VIK is a minimal but reasonably fast SMT solver for the theories of uninterpreted functions (UF), algebraic data
types (ADTs), linear arithmetic over integers and reals (LIA, LRA), extensional arrays, and the arithmetic
fragment of bit-vectors (BV, lowered to integers), and their combinations. It is designed to be used as a backend for verification tools, and to be easy to understand and to modify.

## Design principle

VIK is meant to be minimal: its codebase is small, modular and easy to understand, with clarity preferred over
performance. It should also be verification-friendly; verifying parts of VIK is future work.

Performance still matters: the target is a factor of one to five of state-of-the-art solvers such as Z3 or cvc5 on
typical instances, and ten or more on pathological ones is acceptable. Every optimization is measured before it is
kept (see the [benchmarks](#benchmarks)), and several measured wins were dropped for readability (the feature
tables of the [documentation site](https://matt.bovel.net/vik/) say which).

## Components

| Package | Description |
|---|---|
| `egraph` | Congruence closure with disequalities, backtracking and explanations. |
| `cdclt` | A CDCL(T) SAT solver parameterized by theory solvers. |
| `lia` | Linear arithmetic by simplex, with bound propagation and branch and bound. |
| `smtlib` | SMT-LIB 2 parser and printer. |
| `vik` | The SMT solver: terms, lowering, simplification, the theory combination, and the session that runs scripts. |
| `playground` | Browser playgrounds for the e-graph and for SMT-LIB scripts. |
| `docsPlayground` | The solver as a WebAssembly module for the documentation site's runnable snippets. |
| `bench` | JMH benchmarks of every module and the comparison with other solvers. |

## Documentation

The [documentation site](https://matt.bovel.net/vik/) has the guide, with SMT-LIB snippets that run in the
browser, a page per theory ([first-order logic](https://matt.bovel.net/vik/theories/first-order-logic.html),
[uninterpreted functions](https://matt.bovel.net/vik/theories/uninterpreted-functions.html),
[integer arithmetic](https://matt.bovel.net/vik/theories/integers.html),
[algebraic datatypes](https://matt.bovel.net/vik/theories/datatypes.html),
[bit-vectors](https://matt.bovel.net/vik/theories/bit-vectors.html)), a page per component with its API
and its feature tables ([the e-graph](https://matt.bovel.net/vik/components/egraph.html),
[the CDCL(T) solver](https://matt.bovel.net/vik/components/cdclt.html),
[the LIA solver](https://matt.bovel.net/vik/components/lia.html),
[the language](https://matt.bovel.net/vik/components/smtlib.html),
[the solver](https://matt.bovel.net/vik/components/vik.html)), the
[evaluation](https://matt.bovel.net/vik/evaluation.html) against z3, cvc5, princess and SMTInterpol, and the
[API documentation](https://matt.bovel.net/vik/api/index.html). Its sources are in [docs/](docs), and
`sbt site` builds it.

For usage, see [Getting started](https://matt.bovel.net/vik/getting-started.html): the command line, the
Scala API, and each module on its own.

## Requirements

- A JDK (17 or later)
- [sbt](https://www.scala-sbt.org/) 2
- [Node.js](https://nodejs.org/) 24 or later, for the Scala.js tests (WebAssembly) and the playground
- [LLVM](https://llvm.org/) with clang, for Scala Native: on the path, or `LLVM_BIN` set to its `bin` directory before starting sbt (an LLVM release unpacked in a user directory works; its clang may need `libtinfo5`, which the Ubuntu archive's package provides in user space with `LD_LIBRARY_PATH`)

## Development

Subprojects: `egraph`, `cdclt`, `lia`, `vik` and `smtlib` on the JVM, the same with a `JS` suffix on Scala.js (same sources, linked to WebAssembly: Scala.js's WebAssembly backend, run by Node.js 24 or later) and with a `Native` suffix on Scala Native (same sources, compiled with clang), `smtlibutils` (the corpus, its importer and its tests, on the JVM), `playground` (the browser playgrounds, WebAssembly too), `docsPlayground` (the solver for the site's snippets), `graal` (the GraalVM native images, below) and `bench` (the benchmarks, below).

```sh
sbt compile     # the five modules on the JVM
sbt test        # their tests
sbt testJVM     # the same, with the corpus tests of smtlibutils
sbt testJS      # the five modules on Scala.js (WebAssembly)
sbt testNative  # and on Scala Native
```

The solver also builds as a GraalVM native image (`graal`, sbt-native-image), and every suite the JVM runs
builds into an image of its own and runs there, the corpus among them — what the binary answers, not only
that it starts. The list of suites is generated from what sbt discovers, so it cannot fall behind:

```sh
bench/graal.sh                                        # target/graal/vik, the solver as a native binary
sbt "graal/nativeImageTest; graal/nativeImageTestRun"  # every suite as a native image, run
```

The SMT-LIB files used by the tests and the benchmarks are the corpus in [corpus/](corpus/README.md), by logic and origin (SMT-LIB releases, the 2026 submission repository, and the regression suites of cvc5, z3 and princess, with their licenses). The JVM test `CorpusTest` registers one test per file: the answers must be the file's statuses within a fuel (work counted, not timed, so the same on every machine), and the model of every `sat` must make the file's assertions true (the session's model-check mode); `corpus/ignore.txt` names the files known to fail, with the reason, and the test asks for a line to be removed when its file passes.

### Benchmarks

[JMH](https://github.com/openjdk/jmh) benchmarks for every module live in the `bench` subproject, with the workloads and results kept per module:

```sh
sbt "bench/Jmh/run -l"                # lists the benchmarks
sbt "bench/Jmh/run .*EGraphBench.*"   # the benchmarks matching a regex
```

See [bench/README.md](bench/README.md) for running and result files, and [bench/results/egraph](bench/results/egraph/README.md),
[cdclt](bench/results/cdclt/README.md), [lia](bench/results/lia/README.md), [sexpr](bench/results/sexpr/README.md),
[smtlib](bench/results/smtlib/README.md) and [smt](bench/results/smt/README.md) (SMT-LIB instances and the comparison with
z3, cvc5, princess and SMTInterpol, in process through their Java bindings and as separate processes) for the workloads and current results.

### Documentation

`sbt site` generates the documentation site in `target/unidoc`: the guide of [docs/_docs](docs/_docs) and the
API documentation of the six modules, as one Scaladoc site. The guide's SMT-LIB snippets run in the reader's
browser: the `docsPlayground` module is linked to WebAssembly (1.2 MB) into `docs/_assets/js/vik/`, and
[docs/_assets/js/snippets.js](docs/_assets/js/snippets.js) gives every `smt2` block a Run button (the snippets
are editable). Serve the output directory to read it — the WebAssembly module is fetched, so `file://` will not
do:

```sh
sbt site
python3 -m http.server --directory target/unidoc 8000
```

CI builds the site on every push, keeps it as the `docs` artifact, and uploads it to the documentation server
(`/vik`, over FTP, with `FTP_HOST`, `FTP_USER` and `FTP_PASS` as repository secrets).

### Playgrounds

Build them, serve the output directory, and open <http://localhost:8000/classes/index.html>: an e-graph playground
(equalities in, the e-graph drawn) and an SMT-LIB playground (a script in, the answers and the lowered script out).
The pages load the solver as a WebAssembly module (Scala.js's WebAssembly backend), which needs a current browser —
Wasm GC and the `exnref` exception handling — and a server: the module fetches `main.wasm`.

```sh
sbt "playground/copyResources; playground/fastLinkJS"
python3 -m http.server --directory target/out/sjs1/scala-3.10.1/playground 8000
```

## References and Inspirations

- Sarek Høverstad Skotåm. [*CreuSAT: Using Rust and Creusot to create the world's fastest deductively verified SAT solver*](https://www.duo.uio.no/handle/10852/96757) (master's thesis, University of Oslo, 2022) and [CreuSAT](https://github.com/sarsko/CreuSAT) (with Robinson, a verified DPLL solver): the trail as a stack with invariants (reason clauses post-unit with the implied literal first, learned clauses as resolvents keeping the database equisatisfiable, SAT as a complete conflict-free assignment), which `cdclt` follows to stay verifiable.
- Bruno Dutertre and Leonardo de Moura. [*A Fast Linear-Arithmetic Solver for DPLL(T)*](https://doi.org/10.1007/11817963_11) (CAV 2006): the simplex of `lia`, with the tableau set up once and bounds as the only backtracked state, and its explanations from the bounds of a violated row.
- Alberto Griggio. [*A Practical Approach to Satisfiability Modulo Linear Integer Arithmetic*](https://doi.org/10.3233/SAT190086) (JSAT 2012): the exact test of the integer equations that `lia` runs before it branches.
- Christos H. Papadimitriou. [*On the Complexity of Integer Programming*](https://doi.org/10.1145/322276.322287) (JACM 1981): the small-model bound whose box makes `lia`'s branch and bound a decision procedure for pure integers, fuel allowing.
- Robert Nieuwenhuis, Albert Oliveras and Cesare Tinelli. [*Solving SAT and SAT Modulo Theories: From an Abstract Davis–Putnam–Logemann–Loveland Procedure to DPLL(T)*](https://doi.org/10.1145/1217856.1217859) (JACM 2006): the CDCL(T) architecture of `cdclt`, whose theory interface follows Z3's `theory` and cvc5's `Theory` (assert literals in trail order, propagate with conflicts and implied literals, explain lazily, push and pop per decision level).
- Robert Nieuwenhuis and Albert Oliveras. [*Proof-Producing Congruence Closure*](https://doi.org/10.1007/978-3-540-32033-3_33) (RTA 2005): explanations of equalities from a proof forest whose edges carry the equated terms and a reason (an input equality or a congruence).
- Simon Guilloud, Sankalp Gambhir and Viktor Kunčak. [`Congruence.scala`](https://github.com/epfl-lara/lisa/blob/58cc866dfb23645e8d40108ed18a8225c8e6424c/lisa-sets/src/main/scala/lisa/automation/Congruence.scala) in [LISA](https://github.com/epfl-lara/lisa): a proof-producing congruence closure that reads explanations off the union tree, splitting at the most recent union on the path to the lowest common ancestor instead of re-rooting a proof forest. `EGraph.explain` does the same.
- George Zakhour, Pascal Weisenburger, Jahrim Gabriele Cesario and Guido Salvaneschi. [*Dis/Equality Graphs*](https://doi.org/10.1145/3704913) (POPL 2025): disequalities as per-class "forbid lists" (after Greg Nelson, *Techniques for Program Verification*, PhD thesis, Stanford, 1980), moved along on merge, a conflict being a class that forbids itself. Used by `EGraph.disequate`.
- Nikolaj Bjørner, Clemens Eisenhofer, Arie Gurfinkel, Nuno P. Lopes, Leonardo de Moura, Lev Nachmanson and Christoph Wintersteiger. [*Z3 Internals (Draft)*](https://z3prover.github.io/papers/z3internals.html).
- Zachary DeVito. [*Intro to EGraphs*](https://colab.research.google.com/drive/1tNOQijJqe5tw-Pk9iqd6HHb2abC5aRid) (`egraphs_example.ipynb`): a Google Colab notebook with an executable Python prototype of the e-graph described in the [egg paper](https://egraphs-good.github.io).
- Sankalp Gambhir. [*smt-lia-pl-seminar*](https://github.com/sankalpgambhir/smt-lia-pl-seminar): building a small SAT solver with theory support from scratch. Talk given at the EPFL graduate PL seminar, 2025-05-13 and 2025-05-20.
- Matthieu Bovel and Solal Pirelli. [*paper-test-implementation*](https://github.com/mbovel/formal-verification-project/tree/main/paper-test-implementation): a toy optimizing DPLL solver in Scala, following Robert Nieuwenhuis and Albert Oliveras' [*On SAT modulo theories and optimization problems*](https://dl.acm.org/doi/10.1007/11814948_18) (SAT 2006). Part of *Minimizing Stainless counter-examples*, CS550 Formal Verification course project, EPFL, Winter 2021–2022.
