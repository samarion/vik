---
title: Bit-vectors
extraJS:
  - js/snippets.js
extraCSS:
  - css/site.css
---

# Bit-vectors

A bit-vector is an integer in `[0, 2ⁿ)`: the operations that are arithmetic modulo `2ⁿ` are lowered to linear
integer arithmetic, where the width costs nothing, and the bitwise ones to the bits of their operands, each a
Boolean the SAT solver decides, tied to the integer by one equation.

**Decision procedure: yes.** The lowered problem has bounded variables, which the integer solver decides;
what the bit-level operations cost is search, not completeness.

## What you can write

```smt2
(set-logic QF_BV)
(declare-const a (_ BitVec 64))
(declare-const b (_ BitVec 64))
(assert (bvult a b))
(assert (bvult b a))
(check-sat)
```

Supported: `bvadd`, `bvsub`, `bvneg`, `bvnot`, `bvmul`,
`bvshl`, `bvlshr`, `bvashr`, `bvudiv`, `bvurem`, `bvsdiv`, `bvsrem`, `bvsmod`, `bvand`, `bvor`, `bvxor`, `bvnand`, `bvnor`, `bvxnor` and
`bvcomp` of anything, `concat`, `extract`, `zero_extend`, `sign_extend`, `repeat`, `rotate_left`, `rotate_right`, the
unsigned and the signed comparisons, equality, the literals `#b…`, `#x…`, `(_ bvN w)`, and the integer
conversions of SMT-LIB 2.7 — `ubv_to_int`, `sbv_to_int`, `(_ int_to_bv n)`, with the pre-renaming spellings
`bv2nat`, `bv2int` and `(_ int2bv n)` accepted.

`bv2int` is signed, the same as `sbv_to_int`, following the definition in the SMT-LIB theory. z3 reads it as
unsigned, the same as `bv2nat`, so the two answer differently when the top bit is set: `(bv2int #xFF)` is -1 here
and 255 in z3.

```smt2
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (= ((_ extract 3 0) x) #x5))
(assert (bvuge x #xf0))
(assert (distinct x #xf5))
(check-sat)
```

Nothing of the theory is refused any more: every operation of `FixedSizeBitVectors` is lowered, and what
the fragment costs is time, not an error.

Every small file of `QF_BV` in the library now lowers; about a third are arithmetic alone, and the rest pay
for their bits. Where the arithmetic applies, the width is free: `pspace/ndist.a.20000`
is decided in milliseconds here and times out for a bit-blasting solver ([evaluation](../evaluation.md)).
Where bits are needed, VIK is a bit-blaster with a small SAT solver behind a simplex, and slow next to one.

## Internals

Every bit-vector term becomes an integer, and every operation becomes its arithmetic image
(`io.bovel.vik.Lowering`). A sort `(_ BitVec n)` becomes the sort of the integers from `0` to `2ⁿ − 1`
(`Sort.IntRange` in the solver, which knows the range and nothing of the operations), and the solver
gives that range to every term of the sort — a constant at its declaration, an
application, a field or a read of an array when it first meets the term, the terms it makes itself among
them (the reads at the index where two arrays differ, the fields of a datatype value). The range is what
the sort says, not an assertion: no `pop` takes it back. The operations get fresh bounded constants where
the modulus or a division needs them — each fresh constant is declared and defined by one linear
equation before the assertion that uses it, and once per distinct operation at a level: the second
`bvmul 4 (bvadd 1 x)` of a script reuses the constants of the first (two chains of constants for one
term are equal only by an integer argument over `2ⁿ`, which branch and bound walked for minutes on
`x0 = 4(x+1) ∧ x0 ≠ 4(x+1)`). Constant arguments fold in the lowering. For an `n`-bit term, `2ⁿ` is written
`m` below:

| Operation | Integer image | Fresh constants and their defining equation |
|---|---|---|
| a declared `(_ BitVec n)` constant `a` | `a` | none; `0 ≤ a ≤ m − 1` asserted |
| an application of sort `(_ BitVec n)` — a function, a selector, a `select` | the application | none; `0 ≤ t ≤ m − 1` asserted at its first use (once per term and level) |
| `bvadd a b` | `r` | `r ∈ [0, m)`: `a + b = r` or `a + b = r + m` — the overflow is a choice the SAT solver makes, not an unknown with `m` as its coefficient |
| `bvsub a b` | `r` | `r ∈ [0, m)`: `a − b = r` or `a − b = r − m` |
| `bvneg a` | `r` | `r ∈ [0, m)`: `−a = r` or `−a = r − m` |
| `bvnot a` | `m − 1 − a` | none |
| `bvmul a c`, `c` a constant | `r` | `r ∈ [0, m)`: `c·a = r + m·k` for one of `k ∈ [0, c − 1]`, a choice up to four counts, else `k` an unknown in that range |
| `bvmul a b`, neither a constant | `r` | shift-and-add over the bits of `b`: a partial product `pᵢ ∈ [0, 2ⁱ(m−1)]` per bit, `pᵢ = 2ⁱ·a` when bit `i` is set and `0` otherwise, then `Σ pᵢ` reduced modulo `m`; the operand whose bits are already known is the one blasted |
| `bvshl a c` | as `bvmul a 2ᶜ`; `0` when `c ≥ n` | as `bvmul` |
| `bvshl a s`, `bvlshr a s`, `bvashr a s`, `s` unknown | `r` | a barrel shifter over the bits of `s`: stage `j` shifts by `2ʲ` or not, on bit `j` — `⌈log₂ n⌉ ` cases, each the constant shift above — and `0` (the sign, for `bvashr`) when a bit of `s` at or above the width is set |
| `bvlshr a c` | `q` | `q ∈ [0, m/2ᶜ)`, `r ∈ [0, 2ᶜ)`: `a = 2ᶜ·q + r`; `0` when `c ≥ n` |
| `bvudiv a c` | `q` | `q ∈ [0, (m−1)/c]`, `r ∈ [0, c)`: `a = c·q + r`; `m − 1` when `c = 0` |
| `bvurem a c` | `r` | the same division; `a` when `c = 0` |
| `bvsdiv a c`, `c` of signed value `T ≠ 0` | `±q` mod `m` | `q`, `r ∈ (−|T|, |T|)`: `v = |T|·q + r` for the signed value `v` of `a`, `r ≤ 0` when `a ≥ m/2` and `r ≥ 0` otherwise — the truncating division, the remainder of the sign of the dividend; negated when `T < 0`; `1` when `a ≥ m/2` and `m − 1` otherwise when `c = 0` |
| `bvsrem a c` | `r` mod `m` | the same division; `a` when `c = 0` |
| `bvsmod a c` | `r + T·z` mod `m` | the same division; `z ∈ {0, 1}`, one exactly when the signs differ and `r ≠ 0`: the remainder of the sign of the divisor; `a` when `c = 0` |
| `bvashr a c` | `q` mod `m` | `q`, `r ∈ [0, 2ᶜ)`: `v = 2ᶜ·q + r` for the signed value `v` — the floor of it over `2ᶜ`; all ones or zero by the sign when `c ≥ n` |
| `bvudiv a b`, `bvurem a b`, `b` unknown | `q`, `r` | `q`, `r ∈ [0, m)`: `a = b·q + r` and `r < b` — the product exact, not modulo, so `q` is the quotient and not a wrapped one; `m − 1` and `a` when `b = 0` |
| `bvsdiv a b`, `bvsrem a b`, `bvsmod a b`, `b` unknown | `±q`, `±r` mod `m` | the same division of the magnitudes, each a case on a sign bit; the quotient negated when the signs differ, the remainder of the dividend's sign (`bvsrem`) or of the divisor's (`bvsmod`) |
| `bvand a c`, `c = 2ᵏ − 1` | `r` | `q, r` of `a = 2ᵏ·q + r`: the low bits are the remainder |
| `bvand a c`, `c = m − 2ᵏ` | `a − r` | the same division: the high bits are what remains |
| `bvor a c`, `bvxor a c`, `c` such a run of bits | `a − r + c`, `a − r + (c − r)` (low run); `r + c`, `r + (c − a + r)` (high run) | the same division |
| `bvand a b`, `bvor a b`, `bvxor a b` | `Σ 2ⁱ·rᵢ` | the bits of `a` and `b`, once per term: `aᵢ ∈ {0, 1}` with `a = Σ 2ⁱ·aᵢ`, bit `i` the atom `aᵢ ≥ 1`; each result bit `rᵢ ∈ {0, 1}` a case on the formula `aᵢ ∧ bᵢ`, `aᵢ ∨ bᵢ`, `aᵢ ⊕ bᵢ` — a literal bit of an operand folds, a constant operand costs no result bit |
| `bvnand`, `bvnor`, `bvxnor` | `m − 1 − r` | as the operation, complemented; the bits of a complement are the negated bits |
| `bvcomp a b` | `k` | `k ∈ {0, 1}`: `k = 1` when `a = b`, `k = 0` otherwise — an equality of two terms with known bits is bit by bit, a conjunction of `aᵢ ↔ bᵢ`, and so is `distinct` |
| `repeat k a` | `Σⱼ 2^(j·n)·a` | none |
| `rotate_left k a` (`k` taken mod `n`) | `2ᵏ·r + q` | `a = 2^(n−k)·q + r`; `rotate_right k` is `rotate_left (n − k)` |
| `extract i j a` | `r₂` | `a = 2ʲ·q₁ + r₁`, then `q₁ = 2^(i−j+1)·q₂ + r₂` |
| `concat a b`, `b` of width `k` | `2ᵏ·a + b` | none |
| `zero_extend k a` | `a` | none |
| `sign_extend k a` | `e` | `e = a + (2^(n+k) − m)` when `a ≥ m/2`, `e = a` otherwise: the sign of `a` is the atom `a ≥ m/2`, never an unknown |
| `bvult`, `bvule`, `bvugt`, `bvuge` | `<`, `≤`, `>`, `≥` directly | none |
| `bvslt a b` (and `sle`, `sgt`, `sge`) | `(a ≥ m/2 ∧ b < m/2) ∨ ((a ≥ m/2 ↔ b ≥ m/2) ∧ a < b)` | none: Boolean structure over the two top bits and the unsigned comparison |
| `ubv_to_int a` | `a` | none: the lowered bit-vector is its unsigned value |
| `sbv_to_int a` | `v` | `v = a − m` when `a ≥ m/2`, `v = a` otherwise |
| `(_ int_to_bv n) t` | `r` | `r ∈ [0, m)`, `k` unbounded: `t = r + m·k` |

The parser reads bit-vector terms as they are written — the tree has them (`Term.BvApp`, `Term.Bits`) —
and the lowering is one function of the solver, `io.bovel.vik.Lowering`: it takes a script and returns
the lowered script, declaring the constants each assertion needs and asserting their definitions before
it, so the assertions that VIK plays are linear integer arithmetic. The player applies it before playing.
Two ways to see it: `(get-assertions)` in a script answers with the lowered assertion stack, and
`sbt "vik/runMain io.bovel.vik.lower file.smt2"` prints a whole file as VIK will play it. One thing there
is not SMT-LIB's, which has no sort for a range of the integers: a bit-vector constant is declared at
`(_ IntRange 0 255)`, say, the range the solver holds it to.

```smt2
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(assert (bvult x y))
(check-sat)
(get-assertions)
```

The answer is the comparison, lowered — `bvult` is `<` on the values, written `x + 1 ≤ y`. The ranges of
`x` and `y` are their sort's, and no assertion:

```
sat
((<= (+ x 1) y))
```
