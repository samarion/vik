# The corpus of SMT-LIB files

Test inputs and benchmark instances, one directory per logic, the smallest standard logic each file fits (`QF_ABV`,
`QF_ALIA`, `QF_AUFBV`, `QF_AUFBVLIA`, `QF_AUFLIA`, `QF_AX`, `QF_BV`, `QF_BVLRA`, `QF_DT`, `QF_IDL`, `QF_LIA`,
`QF_LIRA`, `QF_LRA`, `QF_RDL`, `QF_UF`, `QF_UFBV`, `QF_UFBVDT`, `QF_UFBVLIA`, `QF_UFDT`, `QF_UFDTLIA`, `QF_UFDTLIRA`, `QF_UFIDL`,
`QF_UFLIA`, `QF_UFLRA`; and, for Stainless's sessions, which SMT-LIB has no logic for, `QF_AUFBVDT`, `QF_AUFBVDTLIA`,
`QF_AUFDTLIA` and `QF_UFBVDTLIA`, named as `QF_UFBVDT` is), then per origin. Every file starts with a comment naming its origin, its original path and its license;
`(set-info :status ...)` before each `check-sat` gives the expected answer (the incremental convention). The JVM
test `CorpusTest` (`smtlibutils/src/test`) registers one test per file it finds here: the answers must be the
statuses, within a fuel per `check-sat` (a number of solver steps — conflicts, pivots, propagations, branches —
so the outcome is the same on every machine), and the model of every `sat` must make the file's assertions true,
as written and as lowered (the session's `checkModels`). `ignore.txt` lists the files the solver is known not to answer
within that fuel, or to answer wrongly, or whose model fails that check (`model:`, with the issue), with the
reason: the test expects those to fail, and when one passes it asks for its line to be removed, so a fixed file
surfaces. The benchmarks (`bench/`) use the subset listed in
their `@Param`s.

`sbt "smtlibutils/runMain io.bovel.smtlib.ignorestamp [regex]"` brings `ignore.txt` up to date after a change to
the solver: it runs the corpus under the test's rules (about seven minutes; a regex restricts it to the paths it
finds) and rewrites the lines whose file changed standing. A listed file that passes loses its line. A file that
now fails gets one, with a generated reason (`timeout (5 s limit)`, `wrong: ...`, `model: ...`) to complete by
hand, with the issue. A listed file that fails in another way than its line says gets the new reason, and one that
fails the same way keeps its line as written. Every change is confirmed by a second run of the file alone, and a
file listed for its time leaves the list only when it passes within half the budget. A `skip` file is probed in a
JVM of its own, with half the tests' heap and killed soon after the budget, so that it cannot take the run down:
one that ends by itself there, without exhausting the heap or the stack, loses its `skip` line or gets the reason
of that run. The test runs the listed files with a small fraction of the fuel and so sees only the ones that became easy;
`ignorestamp` runs them with all of it. Review the diff before committing it.

## Origins and licenses

| Origin | Directory | What | License |
|---|---|---|---|
| SMT-LIB release 2025, non-incremental ([Zenodo 16740866](https://zenodo.org/records/16740866)) | `<logic>/smt-lib/` | a representative sample per logic (see below): up to fourteen files per family spread over the sizes, run under the suite's budget, then about two thirds that VIK answers — the fastest of each family where the files are alike, one slower one for the spread — and one third it does not, on `ignore.txt` with the reason; plus the instances the evaluation uses | CC BY 4.0 for the release; a family may state its own license in its header (Rodin and CLEARSY: CC BY-NC 4.0 — kept out of new imports) |
| SMT-LIB release 2025, incremental ([Zenodo 15493096](https://zenodo.org/records/15493096)) | `<logic>/smt-lib-incremental/` | the same sampling per logic (several `check-sat` per file, `push`/`pop`), plus the evaluation's `kind`, `safari` and `cpachecker` picks, and the first rounds of seven scripts too long for it (`prefix` in their names: `lustre`, `2019-Mann`, `Heizmann`, `UltimateBuchiAutomizer`) | CC BY 4.0 |
| [SMT-LIB benchmark submission](https://github.com/SMT-LIB/benchmark-submission), the staging repository for the 2026 release | `<logic>/submission/` | the files in our fragment (a snapshot: not the final 2026 release) | as stated in each file's `:license` header |
| [cvc5](https://github.com/cvc5/cvc5) regression tests, `test/regress/cli` | `<logic>/cvc5/` | every regression file in our fragment with `; EXPECT:` answers or, where it has no `; EXPECT:` line, a `sat` or `unsat` status before a `check-sat` (the statuses cvc5's runner then checks), and no option in `; COMMAND-LINE:` that could change the answers: 1 096 files, of which 760 were added at commit 0f863c21 on 2026-11-17 (506 of them by their statuses), less five whose `; EXPECT:` lines hold cvc5's own behavior (`print-success`, an error after a `define-fun`, `reset-assertions`, a `Seq` value, a parametric constructor's name) | modified BSD, [LICENSES/cvc5.txt](LICENSES/cvc5.txt) |
| [z3test](https://github.com/Z3Prover/z3test), `regressions/smt2` | `<logic>/z3test/` | every file in our fragment whose `.expected.out` is made of answers | MIT, [LICENSES/z3test.txt](LICENSES/z3test.txt) |
| [cvc5](https://github.com/cvc5/cvc5) documentation examples, `examples/api/smtlib` | `<logic>/cvc5-examples/` | the SMT-LIB examples of the API documentation that are in our fragment, answered by `statusstamp` | modified BSD, [LICENSES/cvc5.txt](LICENSES/cvc5.txt) |
| [z3 guide](https://github.com/microsoft/z3guide), `website/docs-smtlib` | `<logic>/z3guide/` | every `z3` code block of the SMT-LIB guide's pages that is in our fragment, one file per block (`<section>__<page>_<n>`), answered by `statusstamp` | MIT, [LICENSES/z3guide.txt](LICENSES/z3guide.txt) |
| [princess](https://github.com/uuverifiers/princess), `testcases` | `<logic>/princess/` | every file in our fragment with an answer in its directory's `Answers` log | BSD, [LICENSES/princess.txt](LICENSES/princess.txt) |
| [SMTInterpol](https://github.com/ultimate-pa/smtinterpol) tests, `SMTInterpolTest/test` (commit f65e98f0) | `<logic>/smtinterpol/` | every test file in our fragment, less five that `prune alike order` found alike another file: 350 (111 with datatypes; 39 with constant arrays, imported once VIK read them), named `<directory>__[<subdirectory>__]<file>`, so that a family is a directory of `SMTInterpolTest/test` (`proof`, `interpolation`, `lira`, `datatype`, …): with the statuses they state, and for the 183 without (the proof and interpolation tests, mostly) z3's answers, z3 reading them without their `set-option` and `get-` commands (it refuses SMTInterpol's options), or cvc5's for two z3 refuses; `datatype/match_bug1`, which expects an error and states no status, is left out | LGPL-3.0, [LICENSES/smtinterpol.txt](LICENSES/smtinterpol.txt) (one file, `datatype__datatype_5`, states CC BY 4.0 in its header) |
| Scala 3 qualified types ([scala3](https://github.com/scala/scala3), branch `qualifiers-vik`, commit e7c4e412ef) | `<logic>/dotty/` | the implications the qualifier solver checked while compiling its test suite (`-Yqualified-types-smt-dump`), less the ones `prune` removes: `unsat` where its e-graph proved them, z3's answer elsewhere. Preliminary, `alpha-` prefixed: the encoding will change | Apache-2.0 (the scala3 repository) |
| Scala 3 qualified types, bit-vector default (the same branch and commit) | `<logic>/dotty/` | the same implications with `Int` as 32-bit vectors | Apache-2.0 (the scala3 repository) |
| [Stainless](https://github.com/epfl-lara/stainless) verification benchmarks (commit a1a60c98, inox 37db9545) | `<logic>/stainless/` | the solver sessions of `frontends/benchmarks/verification/{valid,invalid}`, dumped with `--solvers=smt-z3 --debug=smt --vc-cache=false --timeout=30`, statuses from z3, imported by `bench/import-stainless.py`: every session up to 100 KB, and those up to 1 MB that take a second or more (5 773 of 6 231, exact duplicates once; the two largest, of 94 MB and 185 MB, are left out though both time out at 20 s), less the ones `prune` removes: 2 190 alike at `order`, then 3 trivial at `trivial 10 5` (steps of the search, as the fuel counted then; 3 580 left). A file is `<valid or invalid>-<benchmark>__<session>`, so a family is one benchmark's sessions | Apache-2.0 (the stainless repository) |
| [Inox](https://github.com/epfl-lara/inox) regression suite (commit b3fb751) | `<logic>/inox/` | the solver sessions of `src/it/resources/regression/{smtlib3,tip}` that use constant arrays or maps of arrays (Inox's sets, bags and maps), dumped with `inox.Main --solvers=smt-z3 --debug=smt --timeout=30`, statuses from z3 4.15.1: 115 of 116, the one z3 does not answer within 30 s left out; none alike another at `order`. A file is `<suite>-<directory>__<test>__<session>` | Apache-2.0 (the inox repository) |
| Other sources, a file or a family each | `<logic>/other/` | benchmarks sent or published outside the collections above, each with its source, original name and license in its header. So far: `QF_AUFBVDT/other/asn1jvm__2899`, the bit stream of the verified ASN.1/ACN serialization work with ESA ([Bucev, Chassot, Felix, Schramka and Kunčak, VMCAI 2025](https://doi.org/10.1007/978-3-031-82703-7_9)), a session Stainless dumped from a cvc5 run, published by Samuel Chassot on [his page](https://samuelchassot.github.io/) (Resources), statuses from cvc5; VIK answers its two checks in about 40 ms warm, cvc5 in 60 s, z3 the first and not the second in ten minutes; and `QF_AUFBVDT/other/stainless-issue-1801__repro`, the reproduction in [Stainless issue 1801](https://github.com/epfl-lara/stainless/issues/1801) of a `get-model` blow-up of z3 5.x on arrays of datatypes that contain arrays, status from z3 4.14, which answers it in 20 ms; z3 5.3.1 does not finish its `get-model` in 40 s and 16 GB; and `QF_UFBVDT/other/sail-x86__<property>`, 61 files: the queries [Sail](https://github.com/rems-project/sail) generated for the `$property` checks of [sail-x86](https://github.com/shina-lab/sail-x86), a Sail specification of x86-64 (`proofs/` at commit 1829cb6e, datatypes of bit-vectors), with a `set-logic` added, all `unsat` by z3 4.14 (three take it one to three minutes); VIK answers 31 within the suite's budget | as stated in each file's header (the ASN.1 session and the issue's reproduction: none stated by the source; sail-x86: MIT, [LICENSES/sail-x86.txt](LICENSES/sail-x86.txt)) |
| VIK (this repository) | `<logic>/vik/` | hand-written tests of the fragment's edges (the `Reals_Ints` casts: `to_real`, `to_int`, `is_int` under both polarities) and one generated script, `QF_DT/vik/bmc__stack_k20.smt2`: bounded model checking of a stack of integers, twenty steps, a postcondition (unsat) and a reachability question (sat) per step under `push`/`pop` — datatypes and integers together, the way a BMC tool drives an incremental solver (`bench/gen-bmc-stack.py`) | the repository's |

Files of logics we do not support (arrays, strings, reals, quantifiers, ...) and files outside the fragment
`smtlib` parses are not imported; the importer reports what it rejected, by error.

## Importing

`sbt "smtlibutils/runMain io.bovel.smtlib.smt2import <origin> <source root> [files per family]"` copies an origin's
files in (the origins' layouts and answer formats are in `Import.scala`): every candidate is parsed, only the
files in the supported fragment are copied, with the header and the statuses, each into the directory of the
smallest standard logic it fits (with its `set-logic` changed if it set another, as `prune logic` does), and the
rejected ones are reported by error. After a change that affects the answers, run `ignorestamp` (above), or the corpus test and edit `ignore.txt` as it asks.

`sbt "smtlibutils/runMain io.bovel.smtlib.prune invalid [--delete] [prefix ...]"` lists the files that neither
VIK's parser nor z3 reads (z3 sees the script without its `check-sat`s, `get-`s and options), and `--delete`
removes them and their `ignore.txt` lines: such a file is no benchmark, its statuses answer a question the script
does not ask. The importer copies only what VIK reads; files added by other means, such as the compiler's dumps,
need it.

`sbt "smtlibutils/runMain io.bovel.smtlib.prune alike <text|names|order|similarity> [--delete] [prefix ...]"` lists
the files alike one it keeps, and `--delete` removes them the same way. The levels are exact, each joining more than
the one before:
`text` (the same S-expressions, comments, layout and `set-info` aside), `names` (the same up to the names of the
script's own symbols and of bound variables), `order` (the same up to the order of declarations, of assertions
between two other commands, of the arguments of commutative operations, and of a `let`'s bindings). A number in place
of the level is a similarity in (0, 1], `prune alike 0.9 QF_UF/stainless` for instance: the files whose weighted
Jaccard index with a kept file is at least that, over the scripts' subtrees cut at depths one to three, names left
out. A file is compared only with files of its logic that have the same statuses and the same standing on
`ignore.txt`, and the files the repository names (benchmark instances, tests, documentation) are always kept. The
summary it printed on 2026-11-07, over the 5 462 files, before the 2 461 files alike at `order` were deleted (3 001
remain):

| Level | Alike a kept file | Of them, Scala 3 dumps |
| --- | --- | --- |
| `text` | 195 | 165 |
| `names` | 2 401 | 2 346 |
| `order` | 2 461 | 2 396 |
| similarity ≥ 0.95 | 2 603 | 2 486 |
| similarity ≥ 0.9 | 2 702 | 2 542 |
| similarity ≥ 0.8 | 2 961 | 2 706 |

The exact levels only join files that are one problem: the canonical form is the file renamed and reordered, z3
answers every form as it does the file (but one, whose `List` datatype z3 takes for its built-in one), and no two
files of one form have contradicting statuses. A similarity
joins variants: at 0.9, two of the synthesis queries of `2017-BuchwaldFried` that differ by one instruction.

`sbt "smtlibutils/runMain io.bovel.smtlib.prune trivial <fuel> <keep> [--delete] prefix ..."` lists, in each family
(a directory and the file name up to `__`, or up to the hash of a Scala 3 dump), the trivial files beyond the
`keep` it keeps. A file is trivial when VIK gives its statuses within `fuel` (units of work, `Session.spent`) and z3 gives them without a
conflict. The files kept are, in turn, the trivial file least like any kept so far (by the similarity above, two
files of different statuses wholly unlike), so a family keeps its sat and unsat variants before a second copy of
anything; its other files and the files the repository names are always kept. The prefixes are required: the
regression tests are small on purpose, and the release samples were chosen for their spread. The Scala 3 dumps
are pruned at `trivial 10 5`, in the fuel's units of the time, when it counted steps of the search: about
`trivial 10000 5` in today's.

`sbt "smtlibutils/runMain io.bovel.smtlib.prune unused <theory> [--delete] prefix ..."` lists the files that apply
no operation of a theory (`bv`, `arith` or `array`): a literal such as `(_ bv5 32)` or a sort is no operation, and
neither is a symbol the script declares. For the bit-vector Scala 3 dumps, such a file asks what its integer twin
asks. The prefixes are required, and the files on `ignore.txt` or named by the repository are kept.

`sbt "smtlibutils/runMain io.bovel.smtlib.prune logic [--move] [prefix ...]"` lists the files whose `set-logic` or
directory is not the smallest standard logic they fit, which the importer files by too. A logic fits when z3 reads
the file under it (z3 holds a script to its logic: `Int` is an unknown sort under `QF_UFDT`, a product of two unknowns
is refused under `QF_LIA`), when VIK's parser still reads it, and when it has `UF` or arrays if the file declares a
sort. Only the logics z3 enforces in full are tried (19 of the 31 standard ones: z3 takes `QF_UFDTLIA`, `QF_LIRA` or
`QF_ALIA` for `ALL`), and for a file that sets a standard logic, only those within it, its own logic being the
answer when none fits. Difference logic (`QF_IDL`, `QF_UFIDL`, `QF_RDL`) is kept for the files that set it: z3 lets
through atoms the standard's definition does not have, such as `(<= x 5)`, and VIK solves it as linear arithmetic.
With `--move`, each file goes to its logic's directory, with its `set-logic` changed and a header line saying so
where it set another; its `ignore.txt` line follows it, and so do the paths the repository cites it by
(`bench/evaluation-instances.txt`, the evaluation page).

## The release samples, per logic

Taken on 2026-09-02 and 2026-09-03 from the release archives (every file up to 200 KB was parsed and lowered;
the fragment line is the lowering's). *Answered*: VIK answers within the suite's budget. *Out of reach*: on
`ignore.txt` as a timeout or a fuel-out, run with a thousand steps so that a solver change that reaches one
shows. *Skipped*: on `ignore.txt` as `skip:`, never run — the encoding exhausts the heap or runs past the
guard, which the fuel does not bound; each is a solver weakness the file documents. Not imported: files that
overflow the parser's stack (deep `let`/`and` nests: `fft`, `bmc-bv`), and `QF_UFLRA`'s
`cpachecker-induction` family, whose lowering takes minutes (one is kept, skipped, as the bug's reproduction).
Mixed logics: `QF_UFBVLIA`, `QF_AUFBVLIA` and `QF_BVLRA` (bit-vectors with integer or real arithmetic) exist
only in the incremental release, from the software verifiers; there is no `QF_AUFLIRA` in SMT-LIB 2025, and
`QF_LIRA` has two files.

The incremental release again (2026-11-11): its bit-vector logics were sampled on 2026-09-03, before the
lowering took the bitwise operations, products, shifts and divisions by unknowns, and not again once it did.
Of the files up to 200 KB that were not here, 525 were run under the suite's budget, taken across the sizes
of each family: 396 answer, 54 lower and do not answer, 44 run past 25 s, 24 overflow the parser's stack and
7 exhaust a 2 GB heap. Added, 37 files: `QF_ABV`, `QF_AUFBV` and `QF_UFBV` get their first incremental files
(`CPAchecker`'s k-induction queries with arrays, `2018-Goel-hwbench` with functions, and the hardware model
checks of `2018-Wolf-fmbench` and `2019-Wolf-fmbench`, none of which answers), and `QF_BV` four families
(`20170501-Heizmann-UltimateAutomizer`, `2019-Mann`, `20210110-Coffin`, `20250315-BMC_WMM`) and nine more
files of `2018-Goel-hwbench`, which had three. Left as they were: the families that had their fourteen,
`CPAchecker` in the three other logics and `20240414-mapf_r`, whose 307 files run all answer.

The sessions with the most `push` and `pop` are over 200 KB and are not here whole: the model checkers'
unrollings (`2018-Mann`, `2019-Mann`, the `unrolled` files of the two `Wolf-fmbench` families,
`kratos_systemC_swmc`), most of `20250315-BMC_WMM`, and twelve of the thirteen sessions of Ultimate
Automizer, of four thousand `check-sat`s each. Of the 121 up to 32 MB, 119 lower; within 20 s VIK answers the
first one to seven rounds of a hardware unrolling of ten to a hundred, and 35 to 550 of Ultimate Automizer's
rounds. Two are here cut to their first rounds, for the evaluation, as the two `lustre` unrollings are:
`2019-Mann__digital-estimation-convergence-inc_fwd_prove_ind.prefix8` and
`20170501-Heizmann-UltimateAutomizer__sum_25x0_false-unreach-call_true-termination.c.prefix300`.

`QF_RDL` and the incremental `QF_ALIA` (2026-11-18), the last two logics of the releases in the fragment that
were absent. `QF_RDL` has 255 files in six families, 147 of them up to 200 KB, all in the fragment; none of
`skdmxa` and `skdmxa2` is under that size. Of the 147, VIK answers 93 within the budget, three of them at its edge, and 51 time out; 3 of
`scheduling` have no status that z3 gives in 30 s. Those six are left out. Forty are here, spread over the sizes of each
family: ten of `SMT-Temporal-Planning-Benchmarks`, which VIK answers whole, the two of `check`, and nine answered
and five timeouts each of `sal` and `scheduling`. The incremental `QF_ALIA` is one family, `UltimateBuchiAutomizer`:
44 scripts of 10 MB to 700 MB, thousands of rounds each over arrays of arrays of integers, none under 200 KB. In
the first rounds of eight of them, VIK stops at a round between the 8th and the 31st and does not pass it in 30 s.
The first 40 rounds of three are here (`prefix40`), all on `ignore.txt` as timeouts: the weakness to document.

`QF_UFBVDT` (2026-11-17), absent until then: its one family, `20230314-Jaroslav-Bendik-Certora` (the Certora
Prover's verification conditions for smart contracts, the bit-vector encoding with datatypes for hashing, CC BY
4.0), has 76 files, 52 up to 200 KB, of which 49 lower within two minutes. z3 answers 11 of them in 20 s and cvc5
8 more; VIK answers one within 12 s. Fourteen are here, spread over the sizes, all with z3's or cvc5's statuses
(three `unsat`): the one VIK answers and thirteen on `ignore.txt`, twelve as timeouts and one skipped, whose
encoding runs past the guard.

Divisions by an unknown divisor (2026-09-04, "Divisions by an unknown divisor") close `QF_BV`: of the five
smallest files per family, 377 of 386 lower — the nine left are five a parser error rejects and four whose
`define-fun` nest the lowering expands past two minutes. They added 26 files, of which 12 answer. One release
file, `2020-Weber__extensions`, went out of reach on 2026-09-05 with the fix of the zero quotient (issue 9):
it had answered while that quotient was wrongly unsatisfiable, which pruned the search.

Shifts by an unknown amount (2026-09-04, "Shifts by an unknown amount, a barrel shifter") added 15 files in
eight families (`float`, `mcm`, `20230224-grsbits-truby`, …), of which one answers: these files shift *and*
multiply or divide by unknowns, so the shift alone rarely decides them.

Products of two unknowns (2026-09-04, "Products of two unknowns, shift-and-add") added 28 files in fourteen
families (`wienand-cav2008`, `brummayerbiere2`, `calypto`, `gulwani-pldi08`, …): 8 answer, 20 do not and are on
`ignore.txt` — a product is the bits of one operand and a partial product per bit, which the simplex carries on
every path, so the multiplier-verification families stay out of reach.

The bitwise operations (2026-09-03 evening, "Bitwise operations, as bits") opened `QF_BV` further: of the five
smallest files per family the old lowering refused, 103 lower now, in twelve new families (`log-slicing`,
`stp_samples`, `brummayerbiere`, `spear`, `uum`, `RWS`, `uclid_contrib_smtcomp09`, …); 38 answer within the budget
and 65 do not — a bit-blaster with a simplex behind it — of which the two smallest per family are kept on
`ignore.txt`. Not imported: `20230221-oisc-gurtner` and most of `20210219-Sydr`, whose nested `define-fun`s the
lowering expands by substitution, exponentially (queued).

| Logic | Origin | Files | Families | Answered | Out of reach | Skipped |
|---|---|---|---|---|---|---|
| `QF_ABV` | smt-lib | 59 | 8 | 26 | 5 | 28 |
| `QF_ABV` | smt-lib-incremental | 13 | 1 | 9 | 4 | 0 |
| `QF_ALIA` | smt-lib | 18 | 6 | 6 | 2 | 10 |
| `QF_ALIA` | smt-lib-incremental | 3 | 1 | 0 | 3 | 0 |
| `QF_AUFBV` | smt-lib | 1 | 1 | 0 | 0 | 1 |
| `QF_AUFBV` | smt-lib-incremental | 4 | 3 | 2 | 0 | 2 |
| `QF_AUFBVLIA` | smt-lib-incremental | 13 | 1 | 0 | 2 | 11 |
| `QF_AUFLIA` | smt-lib | 14 | 6 | 7 | 4 | 3 |
| `QF_AUFLIA` | smt-lib-incremental | 15 | 1 | 12 | 3 | 0 |
| `QF_AX` | smt-lib | 10 | 4 | 6 | 0 | 4 |
| `QF_BV` | smt-lib | 250 | 51 | 139 | 111 | 0 |
| `QF_BV` | smt-lib-incremental | 33 | 6 | 26 | 2 | 5 |
| `QF_BVLRA` | smt-lib-incremental | 14 | 1 | 13 | 1 | 0 |
| `QF_DT` | smt-lib | 21 | 8 | 17 | 4 | 0 |
| `QF_IDL` | smt-lib | 2 | 1 | 2 | 0 | 0 |
| `QF_LIA` | smt-lib | 26 | 20 | 26 | 0 | 0 |
| `QF_LIA` | smt-lib-incremental | 6 | 2 | 4 | 2 | 0 |
| `QF_LIRA` | smt-lib | 2 | 1 | 2 | 0 | 0 |
| `QF_LRA` | smt-lib | 154 | 35 | 138 | 16 | 0 |
| `QF_LRA` | smt-lib-incremental | 1 | 1 | 1 | 0 | 0 |
| `QF_RDL` | smt-lib | 40 | 4 | 30 | 10 | 0 |
| `QF_UF` | smt-lib | 69 | 27 | 67 | 2 | 0 |
| `QF_UF` | smt-lib-incremental | 89 | 2 | 89 | 0 | 0 |
| `QF_UFBV` | smt-lib | 27 | 4 | 3 | 23 | 1 |
| `QF_UFBV` | smt-lib-incremental | 6 | 3 | 2 | 4 | 0 |
| `QF_UFBVDT` | smt-lib | 14 | 1 | 1 | 12 | 1 |
| `QF_UFBVLIA` | smt-lib-incremental | 13 | 1 | 13 | 0 | 0 |
| `QF_UFDT` | smt-lib | 16 | 1 | 0 | 1 | 15 |
| `QF_UFDTLIA` | smt-lib | 16 | 1 | 0 | 7 | 9 |
| `QF_UFDTLIRA` | smt-lib | 13 | 1 | 13 | 0 | 0 |
| `QF_UFIDL` | smt-lib | 82 | 10 | 48 | 29 | 5 |
| `QF_UFLIA` | smt-lib | 72 | 6 | 45 | 18 | 9 |
| `QF_UFLIA` | smt-lib-incremental | 19 | 1 | 18 | 0 | 1 |
| `QF_UFLRA` | smt-lib | 43 | 6 | 31 | 11 | 1 |
| `QF_UFLRA` | smt-lib-incremental | 1 | 1 | 1 | 0 | 0 |

## The SMT-LIB instances of the benchmarks

| File | Family | Status | Workload |
|---|---|---|---|
| `eq_diamond__eq_diamond20.smt2`, `eq_diamond__eq_diamond50.smt2` | eq_diamond | unsat | diamonds of equalities: exponential without learning |
| `NEQ__NEQ004_size4.smt2` | NEQ | unsat | pigeonhole-like disequalities over functions |
| `PEQ__PEQ018_size4.smt2` | PEQ | unsat | permutation equalities |
| `SEQ__SEQ032_size3.smt2`, `SEQ__SEQ009_size10.smt2` | SEQ | unsat | sequence equalities |
| `QG-classification__qg5__iso_brn001.smt2`, `QG-classification__qg5__iso_icl662.smt2` | QG-classification | sat, unsat | quasigroup classification (`let`-heavy, large) |
| `2018-Goel-hwbench__QF_UF_bug-1_ab_reg_max.smt2`, `2018-Goel-hwbench__QF_UF_mcs.1.prop1_ab_cti_max.smt2` | 2018-Goel-hwbench | sat | hardware verification (abstraction with `ite`) |
| `20170829-Rodin__smt3534838651727683253.smt2` | 20170829-Rodin | unsat | Rodin proof obligations |
| `20190906-CLEARSY__0016__00003.smt2` | 20190906-CLEARSY | sat | Atelier B proof obligations |
| `TypeSafe__z3.1184131.smt2` | TypeSafe | unsat | Sledgehammer / Isabelle |

QF_LIA, from `QF_LIA.tar.zst` of the same release, the same way:

| File | Family | Status | Workload |
|---|---|---|---|
| `CAV_2009_benchmarks__20-vars__problem__001.smt2` | CAV_2009_benchmarks | sat | random linear systems (Dillig, Dillig, Aiken 2009) |
| `cut_lemmas__10-vars__cut_lemma_01_001.smt2`, `cut_lemmas__20-vars__cut_lemma_01_001.smt2` | cut_lemmas | unsat | integer infeasibility needing cuts or search (the 20-variable one takes VIK 18 s: comparison only) |
| `pidgeons__pigeon-hole-6.smt2` | pidgeons | unsat | pigeonhole over integers |
| `calypto__problem-005675.cvc.2.smt2` | calypto | sat | hardware verification (Calypto) |
| `dillig__20-4.smt2` | dillig | sat | random systems |
| `mathsat__FISCHER1-1-fair.smt2` | mathsat | sat | bounded model checking of Fischer's protocol |
| `rings__ring_2exp4_3vars_2ite_unsat.smt2` | rings | unsat | modular arithmetic encoded with `ite` |
| `prime-cone__prime_cone_unsat_3.smt2` | prime-cone | unsat | small crafted cones |
| `CIRC__multiplier_prime__MULTIPLIER_PRIME_2.msat.smt2` | CIRC | sat | arithmetic circuits |
| `convert__convert-tiff2jpg-query-1831.smt2` | convert | unsat | program verification queries |
| `fft__Sz64_1160.smt2`, `nec-smt__small__int_from_list__prp-2-17.smt2`, `wisa__wisa1.smt2` | fft, nec-smt, wisa | sat, unsat, sat | larger structured instances (VIK 17 s, timeout, timeout: comparison only) |

QF_BV, from `QF_BV.tar.zst` of the same release, a representative sample rather than every file: the release
has 46 191 QF_BV files, 10 359 of them (up to 200 KB) in the arithmetic fragment that `vik` lowers to integers —
the others use `bvor`, `bvashr`, `bvsdiv`, or `bvmul`/`bvand` of two variables, which would need bit-blasting —
and four families of generated series (`sage`, `Sage2`, `20221012-MCMPC`, `bruttomesso`) make up nine tenths
of those. A hundred were taken (2026-09-02), spread over the seventeen families and the sizes within each, and
where a family's files are alike, the ones VIK answers in tens of milliseconds: 66 that it answers within the
suite's budget, and 34 that it does not — the generated series, `calypto`, `fft`, the SV-COMP `bmc-bv`
scripts — on `ignore.txt` with their reason, so that a change in the solver's reach shows in the suite. The
first rows of the table below are the earlier picks (the three smallest files of each family, 53 of 188 in
the fragment); the sample is on top of them. Nine files of the release overflow the parser's stack (`fft`'s
`Sz512` series, `bmc-bv/ex2_prime`, `bmc-bv/queens`: deep `let` nests) and were left out.

| File | Family | Status | Workload |
|---|---|---|---|
| `sage__app7__bench_8505.smt2`, `sage__app2__bench_512.smt2` | sage | sat, unsat | symbolic execution queries (SAGE); the second, for the evaluation, has 176 operations over 8-bit terms — subtractions, additions and comparison chains |
| `bench_ab__a97test0001.smt2`, `bench_ab__a649test0047.smt2` | bench_ab | sat, sat | crafted arithmetic (Engler's tool via CVC3); the second, for the evaluation, has 116 operations |
| `bmc-bv__adpcm.smt2`, `bmc-bv__Prim_4.smt2` | bmc-bv | sat, unsat | bounded model checking |
| `crafted__bitops7.smt2`, `crafted__bv8.smt2` | crafted | sat, unsat | small crafted instances |
| `2018-Goel-hwbench__QF_BV_bv_bv_swap_two_cc_ref_max.smt2`, `2018-Goel-hwbench__QF_BV_cav14_example_cc_reg_max.smt2` | 2018-Goel-hwbench | sat, unsat | hardware verification |
| `20190311-bv-term-small-rw-Noetzli__bv-term-small-rw_17.smt2` | 20190311-bv-term-small-rw-Noetzli | unsat | rewriting lemmas |
| `pspace__ndist.a.20000.smt2` | pspace | unsat | wide bit-vectors: 0.3 ms in process for VIK, a 20 s timeout for z3, which bit-blasts |
| `bruttomesso__core__ext_con_004_001_0016.smt2`, `fft__Sz128_2823.smt2` | bruttomesso, fft | unsat, unsat | `extract`/`concat` chains and FFT: VIK exceeds 20 s (comparison only) |

QF_DT, from `QF_DT.tar.zst` of the same release (8,700 files in three families; 34 of the 35 small files tried are in
the fragment: monomorphic datatypes without `Int` or `Bool` fields):

| File | Family | Status | Workload |
|---|---|---|---|
| `20172804-Barrett__tests__v1__v1l20086.cvc.smt2`, `20172804-Barrett__tests__v10__v10l20080.cvc.smt2` | 20172804-Barrett | sat, sat | random constraints over lists and trees (jsat) |
| `20172804-Barrett__tests__v10__v10l60049.cvc.smt2`, `20172804-Barrett__typed__v3__typed_v3l30025.cvc.smt2` | 20172804-Barrett | unsat, unsat | idem |
| `20230720-blocksworld__from_0_1_3_to_1_1_2_bmc_0.smt2`, `..._bmc_1.smt2`, `..._bmc_2.smt2` | 20230720-blocksworld | unsat | bounded model checking of blocks-world plans (`ite` chains over datatypes) |
| `20230720-blocksworld__from_0_9_4_to_3_3_7_bmc_5.smt2`, `20230720-blocksworld__from_14_0_3_to_12_4_1_bmc_7.smt2` | 20230720-blocksworld | unsat | deeper bounds: VIK 2 s and 26 s (comparison only) |
| `20210312-Bouvier__vlsat3_b07.smt2` | 20210312-Bouvier | unsat | VIK and z3 both exceed 20 s (comparison only) |

QF_UFLIA, from `QF_UFLIA.tar.zst` of the same release (659 files: mathsat 454, wisas 108, Certora 76, TwoSquares 21),
uninterpreted functions over integers, the theory combination:

| File | Family | Status | Workload |
|---|---|---|---|
| `TwoSquares__smtlib.598294.smt2`, `TwoSquares__smtlib.602033.smt2` | TwoSquares | sat, unsat | Sledgehammer proof obligations (Isabelle) |
| `wisas__xs_5_5.smt2`, `wisas__xs_8_8.smt2`, `wisas__xs_20_20.smt2` | wisas | unsat, sat, sat | Wisconsin Safety Analyzer: format-string safety, counters as functions |
| `wisas__xs_38_38.smt2` | wisas | sat | idem, larger: VIK 50 s (comparison only) |
| `mathsat__Wisa__xs-09-05-2-4-4-5.smt2`, `mathsat__Wisa__xs-07-11-1-1-1-1.smt2` | mathsat/Wisa | sat, unsat | the same family, MathSAT's translation |
| `mathsat__Hash__hash_uns_04_18.smt2` | mathsat/Hash | unsat | hash-table invariants |
| `mathsat__Hash__hash_sat_09_08.smt2`, `mathsat__EufLaArithmetic__hard__hard13.smt2` | mathsat | sat, unsat | VIK exceeds 60 s (comparison only) |
| `20230314-Jaroslav-Bendik-Certora__65782_cd31513fdcd15701933b_6_QF_UFLIA.smt2` | 20230314-Jaroslav-Bendik-Certora | unknown (z3: sat) | smart-contract verification conditions (comparison only) |

QF_LRA, from `QF_LRA.tar.zst` of the same release, linear real arithmetic — strict bounds through
δ-rationals, disequalities branched strictly, rational literals as introduced constants —
157 files from 34 families, 97 sat, 54 unsat, 6 unknown:

- interval-arithmetic chunks bounding elementary functions and circuits (Jovanović, de Moura 2012):
  `atan`, `asin`, `cbrt`, `sqrt`, `log`, `Chua`, `CMOS`, `Arthan`, `bottom-plate-mixer`, `polypaver`;
- SAL model checking (Dutertre, Rushby et al.): `windowreal`, `tgc`, `sc`, `gasburner`, `carpark`, `pursuit`;
- Ultimate LassoRanker termination templates: `2017-Heizmann-UltimateInvariantSynthesis`, `Ultimate`,
  `SV-COMP`, `CooperatingT2`;
- planning: `DTP-Scheduling` (disjunctive temporal), `TM` (temporal metric);
- KeYmaera verification conditions (`keymaera`), MIP relaxations (`miplib`), blending (`blending`),
  tropical matrices (`tropical-matrix`), robotics (`robotics`).

The 18 heaviest — most of `miplib` and `blending`, `TM`, `tropical-matrix`, the Heizmann and
CooperatingT2 templates, the Braverman phase templates — are in `ignore.txt`: the fuel of two million
steps runs out, in minutes of big-rational simplex.

QF_UFLRA, from `QF_UFLRA.tar.zst` of the same release, uninterpreted functions over reals:

| File | Family | Status | Workload |
|---|---|---|---|
| `cpachecker-induction-svcomp14__*` (3) | cpachecker-induction | unsat | CPAchecker k-induction on SV-COMP C programs |
| `cpachecker-bmc-svcomp14__*` (3) | cpachecker-bmc | sat | the same, bounded model checking |
| `FFT__smtlib.620524.smt2`, `FFT__smtlib.626159.smt2`, `FFT__smtlib.626179.smt2` | FFT | sat, unsat, unsat | FFT implementation verification |
| `RandomCoupled__*` (3), `RandomDecoupled__*` (3) | MathSAT random | sat, one unsat | random coupled and decoupled UF+LRA systems |

Licenses, as stated in the files: 2018-Goel-hwbench [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/);
20170829-Rodin and 20190906-CLEARSY [CC BY-NC 4.0](https://creativecommons.org/licenses/by-nc/4.0/); the other
families, including all the QF_LIA, QF_BV and QF_UFLIA ones, state a `:source` only; the QF_DT files and the Certora one state [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/). See each file's `set-info` header for the authors.

## Datatype workloads (`AdtBench`)

Random instances built directly with the `vik` API (no SMT-LIB file), sizes `n` = 10 and 30:

| Benchmark | Workload | Exercises |
|---|---|---|
| `finite` | ten sets of `n` random formulas over `Color` (three constants) and `Pair` (two colors) with `n` pair constants, a mix of satisfiable and unsatisfiable | testers, selectors, injectivity and distinctness on finite sorts, the eager expansion of finite sorts |
| `lists` | ten chains of `n` lists `l_i = cons(a_i, l_{i+1})`, closed by `l_n = nil` or, for half of them, by `l_n = l_0` (unsat by acyclicity), with disjunctions on their heads | injectivity along a chain, the acyclicity check at the final check |

