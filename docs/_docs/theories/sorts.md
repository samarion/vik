---
title: Sorts
extraJS:
  - js/snippets.js
extraCSS:
  - css/site.css
---

# Sorts

The sorts of a script beyond the theories' own: the uninterpreted sorts of `declare-sort` (decided by
[congruence closure](uninterpreted-functions.md)), the algebraic datatypes of `declare-datatype` —
constructors, selectors, testers and `match`, with fields of any supported sort — and the sort parameters
of SMT-LIB 2.7, which make datatypes and functions polymorphic and are compiled away. Datatypes are a
construct of the language rather than a theory of the library; the decision procedure for them is the
theory of this page.

**Decision procedure: yes.** Injectivity, distinctness, exhaustiveness and acyclicity together decide
`QF_DT`; a sort parameter is decided as the monomorphic theory of each of its instances.

## Algebraic datatypes

```smt2
(declare-datatype List ((nil) (cons (head Int) (tail List))))
(declare-const l List)
(assert (= l (cons 1 (cons 2 nil))))
(assert (= (head (tail l)) 3))
(check-sat)
```

Constructors are injective and distinct, and no value contains itself:

```smt2
(declare-datatype List ((nil) (cons (head Int) (tail List))))
(declare-const l List)
(assert (= l (cons 1 l)))
(check-sat)
```

Testers are `((_ is cons) l)`, and every value is built by one of the constructors — which is what makes a
finite datatype finite:

```smt2
(declare-datatype Color ((red) (green) (blue)))
(declare-const a Color)
(declare-const b Color)
(declare-const c Color)
(declare-const d Color)
(assert (distinct a b c d))
(check-sat)
```

`match` is read as testers and selectors: the scrutinee is bound once, each case becomes an `ite` on the
constructor's tester with the pattern's variables bound to the selectors, the last case is the default, and
a variable pattern catches everything after it.

```smt2
(declare-datatype Shape ((circle (radius Int)) (rect (w Int) (h Int)) (point)))
(define-fun area ((x Shape)) Int (match x ((point 0) ((circle r) (* 3 r)) ((rect a b) (+ a b)))))
(declare-const s Shape)
(assert (= (area s) 7))
(assert (match s ((point false) (other (> (area other) 6)))))
(check-sat)
```

A datatype must be well-founded, as the standard asks: one of its constructors takes only fields that have
values without it. `(declare-datatype T ((c (next T))))` has no value and is refused, as is a group of
datatypes that only have values through one another. An array field counts for its indices and its
elements, and a parametric datatype is judged at each instance. The solver relies on it: the default values
of a model, for a datatype term that nothing constrains, are built from a constructor whose fields all have
values, and every datatype has one. A datatype given to `io.bovel.vik.Solver` directly, without the parser,
is not checked and must be well-founded too.

A name is declared once. A command that names a sort like one the script has already — a sort of
`declare-sort`, an abbreviation of `define-sort` or a datatype — is refused, as z3 and cvc5 refuse it, and so
are two datatypes of one name in a `declare-datatypes`. A `pop` frees the names of its level.

Function symbols follow the same rule, which is SMT-LIB's: `declare-fun` and `define-fun` refuse a symbol the
script has already, and a datatype refuses a constructor or a selector named like one, another datatype's
included. z3 and cvc5 accept a constructor or a selector that two datatypes share and tell its uses apart by
their sorts. VIK does not, and refuses the second declaration. A datatype given to `io.bovel.vik.Solver`
directly is not checked here either.

A parametric datatype — `(declare-datatype List (par (T) ...))` — is a datatype per instance, `(List Int)`,
`(List Bool)`: see [sort parameters](#sort-parameters) below.

### Internals

The theory is a set of rules of the [e-graph](../components/egraph.md), which calls them when a node is added
and when two classes are merged, and which lets them derive equalities with the premises they hold — so an
equality the rules derive explains itself like any other.

- **Injectivity and distinctness**: a class that gains a second constructor node either merges the arguments
  pairwise (same constructor) or is a conflict (different ones), explained by the two constructor terms.
- **Selectors**: `sel_i(t)` where the class of `t` holds `C(a₁ … aₙ)` is `aᵢ`.
- **Testers**: `is_C(t)` true where the class holds a constructor is decided by comparing the two; where it
  holds none, the true tester expands the term into `C(sel_1(t) … sel_n(t))`.
- **Exhaustiveness**: for every term of a datatype sort, a clause saying that one of its testers holds; for a
  finite sort, the selector terms are expanded first, so that the search is complete on it.
- **Acyclicity**: at the final check, a depth-first search over the constructor nodes of the classes; a cycle
  is a conflict, explained by the constructor equalities along it.

The scheme is the one of Barrett, Shikanian and Tinelli. Fields of sort `Int` or `Bool` work because those
theories exchange equalities with the e-graph, which is the same mechanism as the
[integer combination](integers.md).

## Sort parameters

The polymorphism of SMT-LIB 2.7: `declare-sort-parameter`, parametric datatypes (`par`), `define-sort`,
sort constructors of any arity, and `(as f τ)`. It is compiled away by the parser, before any theory sees
a term: every use of a polymorphic symbol is a use of a monomorphic instance, and every instance of a
parametric datatype is a datatype of its own.

A sort parameter makes a rank polymorphic; the parameter is bound by the arguments' sorts at each use, and
the instances are unrelated functions:

```smt2
(declare-sort-parameter X)
(declare-fun f (X) X)
(declare-const x Int)
(assert (= (f x) 5))
(assert (= (f true) false))
(assert (= (f (f x)) 7))
(check-sat)
```

A parametric datatype is instantiated sort by sort — `(List Int)` and `(List Bool)` are two datatypes — and
a constructor whose sort the arguments do not determine, such as `nil`, is named with `as`:

```smt2
(declare-datatype List (par (T) ((nil) (cons (head T) (tail (List T))))))
(declare-const l (List Int))
(declare-const m (List Bool))
(assert (= l (cons 1 (cons 2 (as nil (List Int))))))
(assert (= m (cons true (as nil (List Bool)))))
(assert (= (head (tail l)) 2))
(assert (match m ((nil false) ((cons h _) h))))
(check-sat)
```

`define-sort` abbreviates a sort, with parameters of its own; `declare-sort` with an arity declares a sort
constructor, each instance of which is an uninterpreted sort; and a `define-fun` whose rank has a
parameter is read again at each instance:

```smt2
(declare-sort-parameter X)
(declare-sort Box 1)
(define-sort Pairs (A) (Box (Box A)))
(declare-fun unbox ((Box X)) X)
(define-fun same ((a X) (b X)) Bool (= a b))
(declare-const s (Box Int))
(declare-const w (Pairs Bool))
(assert (= (unbox s) 1))
(assert (same (unbox (unbox w)) true))
(assert (not (same (unbox s) 1)))
(check-sat)
```

### What it means, and what it does not

An instance of `f` at `Int` is the monomorphic symbol `f@Int`, declared the first time it is used; an
instance of `List` at `Int` is the datatype `(List Int)` with constructors `nil@Int` and `cons@Int`. That is
what models and `get-value` print, and what the [lowered script](../components/vik.md) contains: the
solver never sees a sort parameter.

A parameter is a name of its declaration only. It may be the name of a sort of the script, `T` in
`(par (T) ...)` beside `(declare-sort T 0)`: in the declaration `T` is then the parameter, and the datatype
is instantiated at the sort `T` like at any other.

A use must determine its instance: `(f x)` binds `X` to the sort of `x`, `(as nil (List Int))` names it,
and a use that does neither — a constant of sort `X` on its own — is refused with a message asking for
`as`. The standard reads an assertion that still mentions a sort parameter as one assertion per
monomorphic sort in the context; VIK does not, since the instances of a quantifier-free assertion would
have nothing to say about one another, and there may be infinitely many.

A parametric datatype must be regular. One whose instance needs an instance of itself at a larger sort,
such as a `(N T)` with a field of sort `(N (Pair T T))`, has an instance per such sort, without end: it is
refused where it is first instantiated. Such datatypes are the nested datatypes of Bird and Meertens
([Nested Datatypes](https://doi.org/10.1007/BFb0054285), MPC 1998). The check is the one the .NET runtime
makes on generic types: ECMA-335, Partition II, section 9.2, "Generics and recursive inheritance graphs",
where the instances are finite exactly when a graph of the parameters has no cycle with an expanding edge.
