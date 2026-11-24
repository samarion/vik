---
title: Getting started
extraJS:
  - js/snippets.js
extraCSS:
  - css/site.css
---

# Getting started

## SMT-LIB scripts

VIK reads [SMT-LIB 2](https://smt-lib.org) scripts and answers the `check-sat` commands, one line each:

```sh
sbt "vik/run problem.smt2"
```

The same on a script you write here — press the play button in its corner:

```smt2
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-const x Int)
(declare-const y Int)
(assert (<= x y))
(assert (<= y x))
(assert (not (= (f x) (f y))))
(check-sat)
```

The front end supports what the theories below support: `declare-sort`, `declare-sort-parameter`,
`define-sort`, `declare-fun`, `declare-const`, `define-fun`, `declare-datatype(s)` (`par` included), `match`,
`as`, `assert` (with `:named`), `check-sat`, `check-sat-assuming`, `push`,
`pop`, `get-model`, `get-value`, `get-unsat-core`, `get-assertions`, `reset-assertions`, `reset`,
`set-logic`, `set-info`, `set-option` and `get-info`. Sorts of theories that are
not supported (strings, sets, floating point) are refused rather than read as uninterpreted
sorts, so a script is never answered on a meaning VIK does not implement. `Real` literals — decimals and
quotients like `(/ 1 3)` — become fresh constants defined by an integer equation (`3 k = 1`), so the
solver still computes over integers; only a division or multiplication that is not linear is refused.

Two options bound the search, and are answered honestly when they stop it:

```smt2
(set-option :rlimit 1)
(declare-fun f (Int) Int)
(declare-const x Int)
(declare-const y Int)
(assert (or (= (f x) 1) (= (f y) 2)))
(assert (< x y))
(check-sat)
(get-info :reason-unknown)
```

`:rlimit` is an amount of work, counted rather than timed — the steps of the search and, by their cost, what
happens between them: Boolean propagation, congruence closure, explanations, arithmetic past 64 bits — in
units of about 4 ns on the JVM, so the same script gives the same answer on every machine;
`:timeout` is milliseconds, for interactive use. Both answer `unknown`, with `resourceout` or `timeout` as
the reason. A third option, `:check-models`, checks the model of every `sat` against the assertions (see
[the tour](guide.md#models-and-cores)).

To run the solver as a native binary or on Node.js, see [the evaluation](evaluation.md), which measures all
three.

## The Scala API

The solver is a library first. Terms and formulas are built directly, and the answers come back as values:

```scala
import io.bovel.vik.*
import io.bovel.vik.Formula.*
import io.bovel.vik.Term.*

val solver = Solver()
solver.declare("f", List(Sort.Int), Sort.Int)
solver.declare("x", Nil, Sort.Int)
solver.declare("y", Nil, Sort.Int)

val (x, y) = (Const("x"), Const("y"))
def f(t: Term) = App(Const("f"), List(t))

solver.assert(x <= y)
solver.assert(y <= x)
solver.assert(f(x) !== f(y))
solver.solve() // Unsat
```

`push()` and `pop()` frame the assertions that change between two questions, which is what a verifier does
with a path condition:

```scala
solver.push()
solver.assert(x < y)
solver.solve() // decided with the assertions of both levels
solver.pop()   // back to what was asserted before the push
```

`solve(fuel)` bounds the work in the same units (`spent` says how much was done) and answers
`Result.Unknown(Reason.Fuel)` beyond it;
`solve(keepGoing)` takes the decision itself, so a deadline or a cancellation is a function you write.

The same with the language attached — a `Session` reads SMT-LIB text or `io.bovel.smtlib` trees piece by
piece, each in the scope the earlier pieces declared, and keeps the solver across them:

```scala
val s = Session()
s.run("(declare-fun f (Int) Int) (declare-const x Int) (declare-const y Int)")
s.assert("(and (<= x y) (<= y x))")
s.assert("(not (= (f x) (f y)))")
s.checkSat() // Some(false)
```

Sorts are values of `Sort`: `Sort.Int`, `Sort.Bool`, `Sort.Named("U")` for an uninterpreted sort or a
datatype you declared, `Sort.IntRange(0, 255)` for the integers of a range. `Formula` has `Eq`, `Le`, `Pred`, the connectives and `Ite`;
the companion adds `Lt`, `Ge`, `Gt`, `IntEq`, `Distinct`; the operators `===`, `!==`, `<=`, `<`, `>=`, `>`,
`+`, `-`, `*` build terms and formulas as they read.

VIK is modular, and each layer is usable without the ones above it — the
[e-graph](components/egraph.md) for congruence closure, the [CDCL(T) solver](components/cdclt.md) for a SAT
problem with a theory of your own, the [LIA solver](components/lia.md) for a system of integer constraints,
[the language](components/smtlib.md) to read and print SMT-LIB. Each of those pages shows its API, and
the [API documentation](api/index.html) has the details.
