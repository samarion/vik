# Contributing to VIK

## Guidelines

- KISS: Keep It Short and Simple.
- Commit messages start with an imperative verb. Short and clear. First line less than 60 chars. Markdown welcome. Example: prefer ``Move `Simplifier` to `vik` `` to `The simplifier joins the solver`. See [How to write a git commit message](https://cbea.ms/git-commit/).
- Format the sources and the build before pushing: `sbt formatAll`. CI checks `formatCheckAll`. Both cover the projects outside the root aggregate (`bench`, `smtlibutils`, the playgrounds, `graal`), which `scalafmtAll` alone skips.
- Every fixed bug gets a witness: a corpus file under `corpus/<logic>/vik/` or a unit test, and `Fixes #N` in the commit. `CorpusTest` checks every model of the corpus against its script's assertions (`Session`'s `checkModels`, `(set-option :check-models true)`), and a file whose model fails today has a `model:` line in `corpus/ignore.txt` naming its issue. `smtlibutils/runMain io.bovel.smtlib.ignorestamp` updates that list after a change: it removes the lines of the files that pass now and adds the ones that fail. `bench/runMain io.bovel.bench.evaluation.SolverCheck` and `ModelCheck` check answers and models against other solvers; run `smtlibutils/runMain io.bovel.smtlib.expectstamp` after a change to outputs, and review its diff.

## Fuzzing

[`bench/fuzz.py`](bench/fuzz.py) compares VIK with z3 and cvc5 on random scripts: datatypes, bit-vectors, integers, functions and arrays, push and pop. A finding is a check-sat that VIK answers against both of them, a model that z3 finds contradicts its script, or a crash. Nothing runs it automatically: run it by hand, for instance after a change to datatypes, bit-vectors, arrays or models. It exits with 1 on a finding that is not the shape of a known open issue (`KNOWN` in the script); its report lists the findings, and `target/fuzz/failures/` holds their scripts, each with a minimized copy.

It needs Python 3 alone, z3 and cvc5 (those of `bench/fetch-native.sh`, or else the ones on the `PATH`), and the classpath of the bench project, which it asks sbt for (`--classpath` skips that):

```sh
bench/fuzz.py run --minutes 5                       # today's seed; the report in target/fuzz/report.md
bench/fuzz.py run --seed 20261118 --minutes 20      # the scripts of that seed again
bench/fuzz.py show 20261118 4316                    # one script of that run, by its index
bench/fuzz.py check target/fuzz/failures/*.smt2     # the comparison again, on given scripts
```

A run prints its seed and commit. A script depends on the seed, its index and `bench/fuzz.py` alone, so on that commit `bench/fuzz.py show <seed> <index> > s.smt2` writes it again, and `bench/fuzz.py check s.smt2` runs the comparison on it. `--lift 125` generates and reports the shape of a known issue again, to check its fix. Once the fix is merged, delete the issue's line from `KNOWN` and the code that reads it.

## Releasing

A release is a git tag: `git tag v0.1.0 && git push origin v0.1.0`. The CI's `publish` job then signs
and uploads the six library modules (JVM, Scala.js and Scala Native rows) to Maven Central under
`io.bovel`, with the tag's version (sbt-ci-release; the version between tags is a snapshot and is
never published by the CI).

One-time setup, done once by the owner:

1. A [Central Portal](https://central.sonatype.com) account with the `io.bovel` namespace verified
   (a DNS TXT record on `bovel.io`, the domain the namespace is read from), and a user token
   (Account → Generate User Token).
2. A signing key: `gpg --gen-key`, then publish the public key
   (`gpg --keyserver keyserver.ubuntu.com --send-keys <id>`).
3. The four repository secrets:
   `gh secret set SONATYPE_USERNAME` and `SONATYPE_PASSWORD` (the user token's two halves),
   `gh secret set PGP_SECRET` (the armored key, base64 in one line:
   `gpg --armor --export-secret-keys <id> | base64 -w0`), and `PGP_PASSPHRASE`.
