# The lowering's lemmas

This is the list a proof checker proves once, written without reference to any
checker. The rule names and the facts are those of
`vik/src/main/scala/io/bovel/vik/LoweringCheck.scala` (`check` for the rules,
`replay` and the helpers below it for the operations). The last column names
the Lean theorem in [`lean/`](lean).

## Notation

- A bit-vector `x` of width `w` lowers to its unsigned value `⟦x⟧ ∈ [0, m - 1]`,
  where `m = 2^w` and `half = 2^(w-1)`. All widths are positive.
- `neg(t)` is `t ≥ half`, the sign of a value.
- `s(x)` is the signed value: `⟦x⟧ - m` if `neg(⟦x⟧)`, else `⟦x⟧`.
- `a div d` and `a mod d` are floor division and its remainder for `d > 0`.
  `tdiv`, `tmod` truncate toward zero. `fmod` takes the sign of the divisor.
- `[lo, hi]` after a symbol is the pair of facts `lo ≤ k` and `k ≤ hi`.

## Rules

Each rule introduces fresh symbols. For each rule, the table gives the facts it
asserts, the values of the symbols, and the bounds on the arguments under which
those values satisfy the facts. Every place the lowering applies a rule
guarantees those bounds; the operation lemmas below discharge them.

| Rule | Facts | Values | Bounds | Lean |
|---|---|---|---|---|
| `range(t, w)` | `t ∈ [0, m - 1]` | (no symbol) | `t = ⟦x⟧` | `range_toNat` |
| `ite(c, t, e)` | `c → k = t`, `¬c → k = e`; for a bit-vector also `k ∈ [0, m - 1]` | `k = if c then t else e` | `t`, `e` in range | `ite_facts`, `ite_range` |
| `cases(tag, c, t, e, lo, hi)` | `k ∈ [lo, hi]`, `c → k = t`, `¬c → k = e` | `k = if c then t else e` | the chosen branch in `[lo, hi]` | `cases_facts` |
| `modulo(v, w, lo, hi)` | `r ∈ [0, m - 1]`, `q ∈ [lo, hi]`, `v = r + q·m`; with fewer than 4 quotients, `∨ₖ v = r + k·m` instead of `q` | `r = v mod m`, `q = v div m` | `lo·m ≤ v < (hi + 1)·m` | `modulo_facts`, `modulo_facts_small` |
| `divide(v, d, qmax)` | `q ∈ [0, qmax]`, `r ∈ [0, d - 1]`, `v = q·d + r` | `q = v div d`, `r = v mod d` | `0 ≤ v ≤ qmax·d + d - 1`, `d > 0` | `divide_facts` |
| `udiv(a, b, w)` | `q, r ∈ [0, m - 1]`; `b = 0 → q = m - 1 ∧ r = a`; `b ≠ 0 → a = Σ partials(b, q) + r ∧ r < b` | `q`, `r` as `bvudiv`, `bvurem` | `a`, `b` in range | `udiv_facts`, `exactProduct_eq` |
| `sdivide(t, w, d, floor)` | `q ∈ [-(half div d) - 1, (half - 1) div d]`, `s(t) = q·d + r`; floor: `r ∈ [0, d - 1]`; truncating: `r ∈ [-(d - 1), d - 1]`, `neg(t) → r ≤ 0`, `¬neg(t) → r ≥ 0` | floor: `q = s div d`, `r = s mod d`; truncating: `tdiv`, `tmod` | `s ∈ [-half, half - 1]`, `d > 0` | `sdivide_floor_facts`, `sdivide_trunc_facts` |
| `bits(t, w)` | `bᵢ ∈ [0, 1]`, `t = Σ 2^i·bᵢ` | `bᵢ` the `i`-th bit of `t` | `t` in range | `bits_facts` |
| `int2bv(t, w)` | `k₀ ∈ [0, m - 1]`, `t = k₀ + k₁·m` | `k₀ = t mod m`, `k₁ = t div m` | none | `int2bv_facts` |
| `smodz(a, c, w)` | `z ∈ [0, 1]`; `¬differ → z = 0`; `r = 0 → z = 0`; `differ ∧ r ≠ 0 → z = 1` | `z = 1` iff `differ ∧ r ≠ 0` | none | `smodz_facts` |
| `store(sort)` | (a function symbol, no facts) | the update of a function at one index | none | `store_same`, `store_other` |
| `floor(r)` | `k ≤ r`, `r < k + 1` | `k = ⌊r⌋` | none | `Real.IsFloor`, `Real.floor_unique` |
| `rat(p, q)` | `q·k = p` | `k = p / q` | `q ≠ 0` | `Real.rat_facts` |
| `ratmul(p, q, t)` | `q·k = p·t` | `k = (p / q)·t` | `q ≠ 0` | `Real.ratmul_facts` |

## Operations

For each operation, the lowered term, with the rule symbols at their values,
equals the value of the result. "Bounds" is what the lemma also proves about the
arguments of the rules the term uses.

| Operation | Lowered term | Lean |
|---|---|---|
| `bvadd` | `modulo(a + b, w, 0, 1)` | `add_val` |
| `bvsub` | `modulo(a - b, w, -1, 0)` | `sub_val` |
| `bvneg` | `modulo(-a, w, -1, 0)` | `neg_val` |
| `bvnot` | `m - 1 - a` | `not_val` |
| `bvmul` by a constant `c` | `modulo(a·(c mod m), w, 0, (c mod m) - 1)` | `mul_const_val`, `times_val` |
| `bvmul` | `modulo(Σᵢ part_i, w, 0, m - 2)`, `part_i = cases(bᵢ, a·2^i, 0)` | `mul_val`, `partials_eq`, `partial_bounds` |
| `bvshl` by `c` | `0` if `c ≥ w`, else `times(a, 2^c)` | `shl_const_val`, `shl_eq_times` |
| `bvlshr` by `c` | `0` if `c ≥ w`, else the quotient of `divide(a, 2^c, m / 2^c - 1)` | `lshr_const_val`, `lshr_const_far` |
| `bvashr` by `c` | `c ≥ w`: `modulo(cases(neg(a), -1, 0))`; else `modulo(q, w, -1, 0)`, `q` from floor `sdivide(a, w, 2^c)` | `ashr_const_val`, `ashr_const_bounds`, `ashr_far_val` |
| `bvshl`, `bvlshr`, `bvashr` by `b` | stage `j < n` shifts by `2^j` when bit `j` of `b` is set; `far` (a bit at or above `n`, or `b ≥ w` when `w ≠ 2^n`) gives the value past the width | `stages_eq`, `far_iff`, `shl_lowering`, `lshr_lowering`, `ashr_lowering` |
| `bvudiv`, `bvurem` by a constant `c` | `c = 0`: `m - 1` and `a`; else `divide(a, c, (m - 1) div c)` | `udiv_val`, `urem_val`, `udiv_const_bounds` |
| `bvudiv`, `bvurem` | the symbols of `udiv(a, b, w)` | `udiv_val`, `urem_val`, `udiv_facts` |
| `bvsdiv`, `bvsrem`, `bvsmod` by a constant `c ≠ 0` (signed `t`) | `modulo(±q)`, `modulo(r)`, `modulo(r + z·t)`, from truncating `sdivide(a, w, abs(t))` and `smodz` | `sdiv_const_lowering`, `srem_const_lowering`, `smod_const_lowering`, `signed_const_bounds`, `sdiv_val`, `srem_val`, `smod_val` |
| `bvsdiv` by zero | `cases(neg(a), 1, m - 1)` | `sdiv_zero_val` |
| `bvsdiv`, `bvsrem`, `bvsmod` | `udiv` of the magnitudes (`cases` tagged `abs`), signs restored by `sdivq`, `sremr`, `smodr`, zero divisor by `sdiv0`, `srem0` | `abs_lowering`, `sdiv_lowering`, `srem_lowering`, `smod_lowering` |
| `bvand`, `bvor`, `bvxor` | the sum of the gates of the bits, each `bitConstant` a `cases(f, 1, 0)` | `and_val`, `or_val`, `xor_val`, `bit_val`, `bitValue_not` |
| the same with a mask `2^k - 1` or `m - 2^k` | from `low = a mod 2^k` and `high = a - low` | `masked_low`, `masked_high` |
| `bvnand`, `bvnor`, `bvxnor` | `bvnot` of the above | `not_val` with the above |
| known bits | `bᵢ ≥ 1` for `bits`; negated bits for `bvnot`; the gates for a bitwise result | `bit_atom`, `not_bits` |
| `extract(i, j)` | the quotient of `divide(a, 2^j, ...)`, then below the top bit the remainder of `divide(q, 2^(i-j+1), ...)` | `extract_val` |
| `concat` | `hi·2^wl + lo` | `concat_val` |
| `repeat(k)` | `Σⱼ 2^(j·w)·a` | `repeat_val` |
| `rotate_left(k)`, `rotate_right(k)` | `2^s·r + q` from `divide(a, 2^(w-s), 2^s - 1)`, `s = k mod w`; right as left by `w - k mod w` | `rotateLeft_val`, `rotateRight_val` |
| `zero_extend(k)` | `a` | `zeroExtend_val` |
| `sign_extend(k)` | `cases(neg(a), a + 2^(w+k) - m, a)` | `signExtend_val` |
| `bv2nat`/`ubv_to_int` | `a` | `val` |
| `sbv_to_int` | `cases(neg(a), a - m, a)` | `toInt_eq`, `toInt_range` |
| `int2bv`/`int_to_bv` | `k₀` of `int2bv` | `val_ofInt` |
| `bvult`, `bvule` (and flipped) | `a < b`, `a ≤ b` | `ult_iff`, `ule_iff` |
| `bvslt`, `bvsle` (and flipped) | `(neg(a) ∧ ¬neg(b)) ∨ ((neg(a) ↔ neg(b)) ∧ a < b)` (or `≤`) | `slt_iff`, `sle_iff` |
| `=` on bit-vectors | `a = b`, or bit by bit once both sides are decomposed | `eq_iff`, `eq_iff_bits` |
| `bvcomp` | `cases(a = b, 1, 0)` | `comp_val` |
| `to_int`, `is_int` | `floor(r)`, `r = floor(r)` | `Real.floor_unique`, `Real.isInt_iff` |
| `select`/`store` | application of the array function, `store!` | `store_same`, `store_other` |

Linear integer and real arithmetic, Booleans, uninterpreted functions and
datatypes lower to themselves, so they need no lemma here.
