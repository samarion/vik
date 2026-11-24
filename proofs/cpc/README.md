# CPC proofs

`Cpc.scala` writes a certificate of Vik as a proof in CPC, cvc5's Cooperating
Proof Calculus. `Vik.eo` is the extension of CPC that those proofs need beyond
cvc5's `Cpc.eo`:

- `vik_lower`, from an assertion as written to the formula Vik solves;
- `vik_rup`, a clause of conflict analysis from the clauses that propagate, by
  reverse unit propagation;
- `vik_uf`, a lemma of uninterpreted functions from the steps of its equality
  proof (`vik.refl`, `vik.given`, `vik.symm`, `vik.trans`, `vik.cong`).

A proof is compact by default: it uses `vik_rup` and `vik_uf`, and leaves out
the conclusions Ethos computes from the rules, which keeps it about the size
of the certificate. `Cpc(certificate, compact = false)` (`CpcCorpus … plain`)
writes plain CPC instead, where those two rules become the resolution chains
and the scopes they stand for, for checkers that know only `Cpc.eo`: about four
times larger.

[Ethos](https://github.com/cvc5/ethos), cvc5's checker for CPC, checks the
proofs. It is fast and unverified: it shows that the proofs are valid CPC.

```sh
proofs/cpc/get-ethos.sh /tmp/ethos                # Ethos and Cpc.eo, at pinned commits; prints ETHOS= and CPC=
export ETHOS=/tmp/ethos/ethos/build/src/ethos CPC=/tmp/ethos/cpc/Cpc.eo
sbt "proofs/testOnly io.bovel.vik.proofs.CpcTest" # writes target/cpc-export, checked when ETHOS and CPC are set
proofs/cpc/export.sh proofs/cpc/corpus.txt /tmp/cpc
proofs/cpc/check.sh /tmp/cpc 4                    # fails unless Ethos accepts every proof
```

CI runs these steps in the `cpc` job.

`corpus.txt` lists the QF_UF scripts of the corpus that get a CPC proof. It
leaves out `regress2/instance_1444`, whose 165 MB proof runs Ethos out of
memory: its learned clauses average 2,400 literals.
