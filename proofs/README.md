# Proofs

With proofs on, Vik backs every `unsat` answer with a certificate that an
independent checker can replay from the SMT-LIB script, with no trusted steps.
A checker for a proof assistant needs, once and for all, the lemmas that make
those certificates sound. This folder holds them, one subfolder per checker:

- [`rules.md`](rules.md) lists the lemmas without reference to any checker:
  for each rule of the lowering, the facts it asserts and the values that
  satisfy them, and for each operation, how its lowered term computes the
  value. A checker for another system proves the same list.
- [`lean/`](lean) proves them in Lean 4, with nothing beyond Lean's core
  library and its standard axioms.
- [`src/`](src) is the sbt project `proofs`: it writes a certificate of Vik
  (`Session.proof`) as Lean files for `lean/` to check, and the certificates
  of a corpus (`LeanCorpus`).

## What the lemmas cover

`LoweringCheck` replays the lowering of each command. It checks that every
symbol the lowering introduces comes from a rule, and that every assertion it
adds is that rule's definition of the symbol. A refutation of the lowered script
is then a refutation of the surface script, provided two things hold:

1. **Each rule's facts are satisfiable.** Given values for the rule's
   arguments, within the bounds the replay guarantees, there are values for the
   rule's symbols that satisfy its facts. A model of the surface script then
   extends to a model of the lowered script.
2. **Each lowered term has the right value.** When the symbols take those
   values, each lowered term evaluates to the value of its surface term. For a
   bit-vector, that value is the unsigned one, in `[0, 2^w - 1]`.

The lemmas here are exactly those two kinds.

## Checking the certificates

The Lean folder also holds a checker for whole answers, with its soundness
proved: `Problem.accepts_sound` says that when the checker accepts an answer, no
model satisfies the lowered assertions together with the levels the answer
assumed. The checker runs inside Lean's kernel (`decide +kernel`), so a proof
of a given answer adds no axiom.

The models are those of the lowered problem's laws: datatypes are term
algebras, a store changes its array at one index, and functions are
extensional: two functions that agree on all arguments are equal. The lowering
reads a bit-vector as an integer, and each width of bit-vectors is a sort of
integers that only ranges over `[0, 2^w - 1]` as an argument: a function, a
constructor or a store only has to behave on arguments in range. The theorem
also assumes that every node of a bit-vector sort takes a value in its range,
which the lowering's lemmas give for the nodes of a lowered script. The checker
covers:

- clausal proofs: input, lemma and derived (RUP) steps;
- input clauses: definitions of Tseitin variables, assertions, retired levels,
  datatype exhaustiveness, shared splits, numerals, congruence,
  read-over-write, extensionality and the ranges of bit-vector witnesses;
- equality proofs for uninterpreted functions and datatypes: congruence,
  selectors, testers, injectivity, distinct constructors, expansion and
  acyclicity;
- cutting-planes proofs for linear arithmetic, with rounding and splits.

An extensionality instance, `f = g ∨ f(w) ≠ g(w)`, does not hold in every
model: only in one where the fresh witness `w` is where `f` and `g` differ.
The answer lists its instances in order, and the checker makes sure their
witnesses are fresh: no input, no level, and no symbol of a datatype or a store
depends on a witness, and the functions of an instance only depend on the
witnesses of earlier instances. Any model then extends to one where every
instance holds, giving values to the witnesses one instance after the other
(`Extend.lean`), with the witnesses of bit-vector indices in their range.

The step from the SMT-LIB script to the lowered problem is checked by a trace
(`Lower/Unsat.lean`): the lowered node of each surface node, and the reason of
each minted symbol (the value of a term `ite`, the store of an array sort).
The checker compares each lowered node with the shape the lowering gives its
operation: chains of comparisons as conjunctions of pairs, `distinct` and
strict bounds on integers as `a + 1 ≤ b`, linear arithmetic up to its normal
form. A surface model gives a model of the lowered problem, with one more
object for each store symbol, in which every lowered node takes the value of
its surface node; so `Trace.unsat` turns an accepted answer into the absence
of a surface model. It covers Booleans, linear integer and real arithmetic,
uninterpreted functions, datatypes, arrays and term `ite`, for a script of
assertions without levels.

Not yet covered are bit-vectors, `to_int`, `is_int` and rational constants in
the trace, levels, `check-sat-assuming`, `define-fun` and `let`, and an
exporter that writes Vik's scripts, traces and answers as Lean terms.
