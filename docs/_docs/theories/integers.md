---
title: Integer arithmetic
extraJS:
  - js/snippets.js
extraCSS:
  - css/site.css
---

# Integer arithmetic

Linear arithmetic over the integers: sums with integer coefficients, compared with `<=`, `<`, `>=`, `>`, `=`
and `distinct`.

**Decision procedure: yes, fuel allowing.** Branch and bound explores inside an a-priori box: if a
pure-integer system has a solution at all, it has one of bounded size (Papadimitriou 1981), so a branch
past the bound is pruned — no solution lives there — and exhausting the box is a sound `unsat`. The
bound is astronomical, so an instance that used to run forever still answers `unknown` within any real
fuel: termination in principle, fuel in practice. Bounded variables — the lowered
[bit-vectors](bit-vectors.md), for instance — are decided promptly either way, and an integer
combination that real constraints confine to a fractional window is cut directly, reals eliminated and
the remainder rounded. The corpus still shows a practical boundary: the `cut_lemmas` instances —
integer-infeasible systems whose rational relaxation is satisfiable, built to need cutting planes —
take the search seconds at ten variables and grow out of any budget as they widen, where a solver with
Gomory-style cuts answers at once.

## What you can write

```smt2
(declare-const x Int)
(declare-const y Int)
(assert (<= (+ (* 2 x) (* 3 y)) 10))
(assert (>= (+ x y) 4))
(assert (>= x 0))
(assert (>= y 0))
(check-sat)
```

Integrality is decided, not approximated — this system has rational solutions (anything strictly
between ½ and 1) and no integer one:

```smt2
(declare-const x Int)
(assert (< (* 2 x) 2))
(assert (> (* 2 x) 1))
(check-sat)
```

Multiplication of two unknowns is refused (this is linear arithmetic), as are reals; `div` and `mod` are not
supported yet.

Functions over integers mix the two theories, and the equalities travel both ways: arithmetic tells the
e-graph that two terms are equal, congruence tells arithmetic that two applications are:

```smt2
(declare-fun f (Int) Int)
(declare-const x Int)
(declare-const y Int)
(assert (= (+ x 1) y))
(assert (not (= (f (+ x 1)) (f y))))
(check-sat)
```

## Internals

Atoms are bounds. A formula `Σ aᵢ·xᵢ ⋈ c` becomes a bound on a slack variable of the
[simplex](../components/lia.md), which is Dutertre and de Moura's: the tableau is built once and never
changes, the bounds are the only state that a decision level pushes and pops, and a conflict is the row whose
bounds cannot be satisfied — a small, natural explanation to hand back to the SAT solver.

Integrality is branch and bound, iterative, over an explicit stack of branches, with the explanations of two
failed sides combined into one that does not mention the branch. Bounds are tightened by the gcd of their
row, and propagated between rows: from `x = Σ aᵢ·yᵢ`, the bounds of the `yᵢ` bound `x`, and the bound of `x`
with the others bounds each `yᵢ`. That propagation costs a factor of two to four on dense random systems and
is decisive on the instances of the library — `fft` goes from seventeen seconds to under one, `nec-smt` from
a timeout to under two.

The [combination with uninterpreted functions](uninterpreted-functions.md) is model-based (de Moura and
Bjørner, 2008). When the search finds a candidate, a final check reads the candidate's model: every e-class
of numbers must have one value in the simplex, and every function must give one result for equal argument
values. Where the model disagrees, the check adds the equality atom between two shared terms that would
settle it, and the search goes on. The same check covers the arrays and the datatype values, which are
compared by their values in the model. An equality atom between numbers is an atom of both theories. It is
a merge or a disequality for the e-graph. For the simplex it is two bounds when true, and when false a
clause between the two sides, `a ≤ b − 1` or `a ≥ b + 1`, each a bound atom the SAT solver decides. Its
first decision is the side the relaxation already satisfies, so it moves nothing, and the simplex branching
on the disequality itself, without learning, was three times slower on `wisas`. Before the final check,
every pair of shared terms that congruence could relate had its equality atom from the start (Nelson and
Oppen), which made the atoms quadratic in the shared terms.
