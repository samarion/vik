---
title: The LIA solver
extraJS:
  - js/snippets.js
extraCSS:
  - css/site.css
---

# The LIA solver

A simplex over the integers: `io.bovel.lia`. It decides systems of bounds on linear combinations, and is
what answers the [arithmetic](../theories/integers.md) atoms.

## Using it

```scala
import io.bovel.lia.Solver

val solver = Solver()
val x = solver.newVar()
val y = solver.newVar()
val sum = solver.newSlack(List((BigInt(2), x), (BigInt(3), y))) // 2x + 3y

solver.assertUpper(sum, 10, reason = 1) // 2x + 3y <= 10
solver.assertLower(x, 1, reason = 2)    // x >= 1
solver.check()                          // Sat, Unsat(reasons) or Unknown
solver.value(x)                         // a solution, after Sat
```

`assertDistinct(x, c, reason)` says `x ≠ c`, decided by branching; `push()` and `pop()` frame the bounds of a
decision level (the tableau is built once and never undone); `keepGoing` bounds the work. Every `Unsat`
carries the reasons of the bounds that are inconsistent, which is the explanation the theory hands back.

## What is in it

| Feature | | Notes |
|---|---|---|
| Dutertre–de Moura simplex: tableau built once, bounds as the only backtracked state, Bland's rule | ✓ | |
| Integers and reals: bounds tightened by the gcd of an integer row, δ-rationals for strict real bounds | ✓ | |
| Branch and bound, iterative, explanations combined across branches | ✓ | |
| Exact test of the integer equations (the rows over fixed variables) once a check branches twice on a variable, after Griggio | ✓ | refutes `2x = 2y + 1`, which branch and bound slides along |
| Bounds moved onto the lattice the solved equations leave of an unknown (`x ≡ c` modulo `g`), the tightening of the same paper | ✓ | `x ≥ 1` with `x ≡ 0 (mod 4)` is `x ≥ 4`: two residues of one number modulo `2ⁿ` are equal without a walk over the quotients, which is what `extract`, `concat` and `int_to_bv` lower to |
| Disequalities `x ≠ c`, decided at the final check by branching `x ≤ c − 1 ∨ x ≥ c + 1` | ✓ | for the equality atoms of shared terms |
| Bound propagation, incremental over the tightened variables | ✓ | [2–4× slower on random systems, decisive on SMT-LIB instances](https://github.com/mbovel/vik/blob/main/bench/results/lia/2026-08-29-laraserver4-propagation.md) |
| `Long` fast path for rationals | ✓ | [1.4–1.6×](https://github.com/mbovel/vik/blob/main/bench/results/lia/2026-08-29-laraserver4-experiments.md) |
| Branching on the most fractional unknown | ✗ | [mixed](https://github.com/mbovel/vik/blob/main/bench/results/lia/2026-08-29-laraserver4-experiments.md) |
| Cuts | ✗ | not yet (`cut_lemmas`, `wisa`) |
| Theory propagation of bounds as literals | ✓ | [1.4–1.7× on the instances of the combination](https://github.com/mbovel/vik/blob/main/bench/results/smt/2026-08-31-laraserver4-bound-propagation.md); implying the equalities of the arrangement as well was measured and rejected |
| Combination with `egraph` | ✓ | arrangement by SAT: an equality atom per pair of shared integer terms, watched by both theories (a merge or a disequality for UF, two bounds for LIA, and when false a clause between the two sides as bound atoms), in `vik`'s encoder; the solvers stay independent |

Results: [lia benchmarks](https://github.com/mbovel/vik/tree/main/bench/results/lia).
