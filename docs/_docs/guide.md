---
title: A tour of the solver
extraJS:
  - js/snippets.js
extraCSS:
  - css/site.css
---

# A tour of the solver

Every script below runs in your browser: press the play button in the corner of a block. They are editable,
so change one and run it again.

## Uninterpreted functions

Congruence: equal arguments give equal results, and that is all the solver assumes about `f`.

```smt2
(declare-sort U 0)
(declare-fun f (U U) U)
(declare-const a U)
(declare-const b U)
(assert (= a b))
(assert (not (= (f a b) (f b a))))
(check-sat)
```

## Linear integer arithmetic

Bounds on linear combinations, decided by a simplex over the integers with branch and bound.

```smt2
(declare-const x Int)
(declare-const y Int)
(assert (<= (+ (* 2 x) (* 3 y)) 10))
(assert (>= (+ x y) 4))
(assert (>= x 0))
(assert (>= y 0))
(check-sat)
```

Integrality matters: the same system over the rationals has a solution, over the integers it does not.

```smt2
(declare-const x Int)
(assert (< (* 2 x) 3))
(assert (> (* 2 x) 1))
(check-sat)
```

## Functions over integers

The two theories exchange what they know about the terms they share: here `x = y` follows from arithmetic, and
congruence then equates the two applications.

```smt2
(declare-fun f (Int) Int)
(declare-const x Int)
(declare-const y Int)
(assert (<= x y))
(assert (<= y x))
(assert (not (= (f x) (f y))))
(check-sat)
```

## Algebraic datatypes

Constructors are injective and distinct, selectors and testers follow them, and no value contains itself.

```smt2
(declare-datatype List ((nil) (cons (head Int) (tail List))))
(declare-const l List)
(assert (= l (cons 1 (cons 2 nil))))
(assert (= (head (tail l)) 3))
(check-sat)
```

```smt2
(declare-datatype List ((nil) (cons (head Int) (tail List))))
(declare-const l List)
(assert (= l (cons 1 l)))
(check-sat)
```

## Reals

`Real` is the same simplex without the integrality; `to_real`, `to_int` and `is_int` cross between the two.

```smt2
(declare-const x Real)
(assert (< (* 2 x) 3))
(assert (> (* 2 x) 1))
(check-sat)
(get-value (x))
```

## Arrays

`select` and `store` follow the read-over-write axioms, and two arrays that differ differ at some index.

```smt2
(declare-const a (Array Int Int))
(declare-const i Int)
(declare-const j Int)
(assert (= (select (store a i 1) j) 2))
(assert (= i j))
(check-sat)
```

## Bit-vectors, as integers

`QF_BV` is lowered to integers: additions modulo, comparisons, masks, `extract`, `concat`, extensions as
arithmetic, where wide vectors cost no more than narrow ones, and the bit-level operations — `bvand`,
`bvor`, `bvxor`, a product or a shift or a division by an unknown — as the bits of their operands, Booleans
the SAT solver decides.

```smt2
(set-logic QF_BV)
(declare-const a (_ BitVec 64))
(declare-const b (_ BitVec 64))
(assert (bvult a b))
(assert (bvult b a))
(check-sat)
```

## Incremental use

`push` and `pop` keep the work done so far; each `check-sat` answers the assertions of the levels below it.

```smt2
(declare-const x Int)
(assert (> x 0))
(check-sat)
(push 1)
(assert (< x 0))
(check-sat)
(pop 1)
(check-sat)
```

## Models and cores

After `sat`, `get-model` and `get-value` say how; after `unsat`, `get-unsat-core` says why, naming the
`:named` assertions the proof used (what a model holds, and what it does not, is on
[the solver's page](components/vik.md)).

```smt2
(declare-datatype List ((nil) (cons (head Int) (tail List))))
(declare-fun f (Int) Int)
(declare-const l List)
(assert (= (head l) (f 3)))
(assert (> (f 3) 4))
(check-sat)
(get-model)
(get-value ((f 3) (f 4)))
```

```smt2
(declare-const x Int)
(declare-const y Int)
(assert (! (<= x 2) :named low))
(assert (! (<= 4 x) :named high))
(assert (! (<= 4 y) :named other))
(check-sat)
(get-unsat-core)
```

`(set-option :check-models true)`, cvc5's name for it, checks every `sat` before it is answered. VIK builds the model
and evaluates the assertions in force, and the assumptions of a `check-sat-assuming`, twice: as VIK lowered them
for its solver, and as the script wrote them, the way `get-value` evaluates a term. When an assertion is not true
at either level, VIK cannot back its `sat` with a model, and answers `unknown` instead, followed by
`(error "model check: ...")`, which names the assertion and its value. `(get-info :reason-unknown)` gives the same
text, and there is no model to get. Such an error is a bug of VIK, never of the script: please report it. One that
names a `lowered assertion` comes from the search or the model, and one that names an `assertion` from the
lowering. The check is off by default, since it builds a model at every `sat`. From Scala,
`Session(checkModels = true)` turns it on (and `Solver.checkModels` for the solver alone, where a failed check is
an `Unknown` with the reason `Model`), and the corpus test runs with it.

```smt2
(set-option :check-models true)
(declare-const x Int)
(declare-const y Int)
(assert (< x y (+ x 2)))
(check-sat)
```

## Budgets

A `check-sat` answers `unknown` when it runs out of fuel — an amount of work counted, not timed, so the answer is
the same on every machine — and `(get-info :reason-unknown)` says why.

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
