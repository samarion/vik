# Lean proofs

The lemmas of [`../rules.md`](../rules.md), proved in Lean 4 with only Lean's
core library: no Mathlib, no `sorry`, and no axioms beyond Lean's standard
three (`propext`, `Classical.choice`, `Quot.sound`).

```sh
lake build                    # checks every proof
lake env lean Axioms.lean     # lists the theorems and fails on any other axiom
```

`lean-toolchain` pins the Lean version; [elan](https://github.com/leanprover/elan)
installs it on first use.

## Files

- `Vik/Rules.lean`: the rules, each with the values of its symbols and a proof
  that they satisfy its facts.
- `Vik/Values.lean`: the value of a bit-vector (`val`), its sign and its signed
  value.
- `Vik/Arith.lean`: addition, subtraction, negation, complement, products and
  shifts by constants, unsigned and signed division.
- `Vik/Signed.lean`: signed division through magnitudes, by a constant and by
  an unknown divisor.
- `Vik/Bits.lean`: bit decomposition, bitwise operations and masks, products
  of unknowns, `extract`, `concat`, `repeat`, rotations, extensions,
  comparisons and equality.
- `Vik/Shifts.lean`: arithmetic shifts by constants, and the barrel shifter for
  shifts by unknown amounts.
- `Vik/Real.lean`: `floor`, `to_int`, `is_int` and rational constants, over any
  ordered field of characteristic zero, as `grind` describes them (Mathlib's
  `ℝ` is one).

- `Vik/Tab.lean`: tables with logarithmic lookups, which the checkers use in
  the kernel in place of list lookups.
- `Vik/Sexp.lean`: `sexp% "…"`, which reads the data of an exported proof
  from an S-expression; Lean's parser is slow on large literals. The kernel
  checks the terms it builds.
- `Vik/Lowered.lean`: the lowered terms and formulas, one table of nodes, with
  their sorts and their meaning in a model.
- `Vik/Simp.lean`: the check that a simplified formula holds in every model of
  its original, and its soundness.
- `Vik/Cert/Clausal.lean`: clausal proofs, checked by unit propagation.
- `Vik/Cert/RatCast.lean`: rational constants in an ordered field.
- `Vik/Cert/Lia.lean`: cutting-planes certificates.
- `Vik/Cert/Uf.lean`: equality proofs over classes, for uninterpreted
  functions and datatypes.
- `Vik/Cert/Inputs.lean`: input clauses against the lowered formulas.
- `Vik/Cert/Witnesses.lean`: what the checker computes to tell that the
  witnesses of extensionality are fresh (the rank of each symbol, the depth of
  each node), and the application chains of an instance.
- `Vik/Cert/Proof.lean`: the checker of a whole answer and its soundness in a
  model whose witnesses take the right values, `accepts_sound_of_witnesses`.
- `Vik/Cert/Extend.lean`: any model extends to such a model, so the checker
  is sound, `Problem.accepts_sound`.
- `Vik/Cert/Example.lean`: small answers the kernel accepts, one of them with
  an extensionality instance and the range of its witness, and what follows
  from them.
- `Vik/Surface.lean`: the SMT-LIB terms before lowering (Booleans, integer
  and real arithmetic, bit-vectors, uninterpreted functions, arrays) and their
  values in a model, with every node of a well-sorted table taking a value of
  its sort, `val_dom`.
- `Vik/Lower/Shape.lean`: shapes of lowered formulas, `fits` to tell whether
  a lowered node has one, and `fits_sound`.
- `Vik/Lower/Trace.lean`: the trace from a surface script to its lowering, the
  shape the lowering gives each operation (`expect`), and `Trace.check`.
- `Vik/Lower/Model.lean`, `Vik/Lower/Laws.lean`: the lowered model of a
  surface model, and the laws it satisfies.
- `Vik/Lower/Corr.lean`, `Vik/Lower/Unsat.lean`: each lowered node takes the
  value of its surface node (`corr`), and the end-to-end theorem
  `Trace.unsat`.
- `Vik/Lower/Bv.lean`, `Vik/Lower/Facts.lean`: bit-vector values as integers,
  the symbols the lowering mints for its rules (`modulo`, `cases`, `divide`,
  `sdivide`, `int2bv`, `smodz`, `bits`, `udiv`), their values and intervals,
  and the facts each rule asserts.
- `Vik/Lower/BitOps.lean`: operations through bits: bitwise operations,
  bitwise equalities, products of unknowns, and barrel shifters.
- `Vik/Lower/SDiv.lean`: signed division by an unknown, through the `udiv` of
  the magnitudes.
- `Vik/Lower/Defs.lean`: `let` and `define-fun`, which the lowering inlines:
  an inlined body is checked to be an instance of the definition
  (`SDef.instOk`), and takes the value of the call (`defOk_sound`).
- `Vik/Lower/Reals.lean`: rational literals, division by a literal,
  `to_real`, `to_int` and `is_int`, lowered to `rat`, `ratmul` and `floor`
  symbols (`realOk_sound`).
- `Vik/Lower/Ops.lean`: each bit-vector or real operation of a trace takes the
  value of the operation (`bvOk_sound`).
- `Vik/Lower/Example.lean`: a two-line SMT-LIB script, its trace and answer,
  checked by the kernel, and the same script with a `check-sat-assuming`,
  whose assumption Vik asserts under a level, and one with `let` and
  `define-fun`.
- `Vik/Cpc/Check.lean`: a checker for Vik's CPC proofs (`Session.cpcProof`),
  over the script's surface terms: each step names the node it concludes,
  which the checker checks against the step's rule, from cvc5's `Cpc.eo`
  or `../cpc/Vik.eo` (`vik_lower`, `vik_rup`, `vik_uf`).
- `Vik/Cpc/Sound.lean`: its soundness: `Proof.unsat` says no model of the
  script's sorts and definitions satisfies its assertions when the checker
  accepts a proof.

Each checker is a Boolean function that `decide +kernel` evaluates on concrete
certificates, with a theorem that an accepted certificate is sound.

## Exported proofs

Vik gives the proof of an `unsat` as a certificate, one S-expression with no
Lean code (`Session.proof`):

```
(vik-proof 1
  (script sig nodes sortOf asserts datatypes defs)
  (trace node mints inputs levels insts)
  (problem sig nodes sortOf inputs datatypes stores bvIndex)
  (answer meaning trueLit levels assumed ufAtoms trueClass falseClass ufCtors
    ufTesters liaAtoms liaForms steps justs conclusion exts witnesses))
```

Each section holds the fields of `Vik.Lower.SProblem`, `Vik.Lower.Trace`,
`Vik.Low.Problem` and `Vik.Low.Answer`, in order, as `sexp%` reads them. The
driver in `../src` (`io.bovel.vik.proofs.Lean`) writes it as one Lean file in a
namespace of the caller's choice: the four sections as `sexp%` data, then
theorems that the checkers accept them, in slices it computes from the data,
and the theorem that no model satisfies the script. A small
file checks with `lake env lean <file>`. Lean checks the theorems of a file one
after another and keeps the kernel's work for the whole file, so a large proof
is split into modules, one per slice, and checked in parallel processes:
`./check-modules.sh <dir> [jobs]`.

The kernel takes minutes to an hour on the largest proofs. The driver also
writes each proof for `native_decide` (`native/` of the exports), which runs the
same checkers as compiled code, in seconds to a few minutes, but trusts Lean's
compiler (the axiom `Lean.ofReduceBool`): `./check-native.sh <file>`. The
library is then compiled to a shared object (`precompileModules`), `sexp%`
splits large lists into compiled definitions (`vik.sexp.chunk`), and compiled
code looks up `Tab.at` in the list, by a `csimp` lemma, rather than build the
tree at each lookup.

`e2e.txt` lists 29 scripts of the corpus that together cover its logics, the
kinds of justifications and input reasons (simplified inputs among them), the
lowering rules and the surface operators, and check in the kernel in about two minutes; `check-exports.sh`
checks a directory of exports in the kernel or with `native_decide`, and
`export.sh` writes the exports of a list. CI checks the set in the kernel and
`corpus.txt`, the 263 scripts of the corpus sample that export, with
`native_decide`.

Vik simplifies its assertions before solving them, eliminating a constant
`c` from a conjunction `c = t ∧ φ` in a positive position. A simplified input
has the reason `.simp o w H`: its original `o` holds by `w`, and
`Low.simplifies` checks that it holds in every model of `o`, given the
positions `H` of the equalities each conjunction lost (`Vik/Simp.lean`).

## CPC proofs

The same scripts have proofs in CPC, the proof format of cvc5, which Ethos
checks (`../cpc`). `Vik/Cpc/Check.lean` checks them in Lean, over the
script's surface terms rather than the lowered problem: the lowering is one
step of the proof, `vik_lower`, and the checker relates the terms on both
sides of it, and those of each `assume` and of each use of a definition, by
equivalences that the proof lists and the checker checks child by child.

A compact proof gives no conclusions; the driver `io.bovel.vik.proofs.CpcLean`
in `../src` computes each as Ethos does and writes the proof as one Lean file:
the script and the proof as `sexp%` data, `checked`, that `Proof.check`
accepts the proof, by `decide +kernel` (or `native_decide` in `native/`), and
`no_model`. For a corpus that `CpcCorpus` wrote with `CPC_CERTS` set:
`proofs/runMain io.bovel.vik.proofs.CpcLean <dir> <out>`. The CPC checker
covers Booleans and uninterpreted functions and sorts, as the CPC proofs do.

Bit-vector semantics are Lean's `BitVec`, whose SMT-LIB operations are
`smtUDiv`, `smtSDiv`, `srem`, `smod`, `sshiftRight'` and the rest under their
usual names.
