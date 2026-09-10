# Cannonball problem (when a square pyramid is a square) — formalize-only

**id:** `cannonball-square-pyramid`
**ticket:** OPE-1310 Scout leftover slot #2 (parent OPE-1309;
post frucht-graph-aut #150 + proth-primality #151)
**expected:** known-classical (Lucas 1875 / Watson 1918: the only
positive integers `n` for which the square-pyramidal number
`n(n+1)(2n+1)/6` is a square are `n = 1` and `n = 24`) —
**no novelty claim**

## Why not classical / why formalize-only

Settled elementary Diophantine arithmetic: the square-pyramidal
number `P(n) = n(n+1)(2n+1)/6` is itself a square if and only if
`n = 1` (`P(1) = 1 = 1²`) or `n = 24` (`P(24) = 4900 = 70²`).
Completely classical (Lucas 1875 conjecture; Watson 1918).

Not an open problem. Not a novelty claim. Not live cash.

**Not** Faulhaber's formula / `sum_range_pow` (Bernoulli.lean L280
already-in; sum of `p`-th powers over `ℚ` is a **different**
generating-function identity — **USE** the elementary closed form
`n(n+1)(2n+1)/6` as Nat arithmetic, do **not** re-prove Faulhaber,
do **not** cite as cannonball). **Not** `sum_range_id`
(Intervals.lean L249 already-in triangular numbers; different
degree). **Not** Lagrange four-squares (`Nat.sum_four_squares`
already-in; sums of four squares ≠ one pyramidal square). **Not**
cannonball *as* Lucas–Lehmer / Mersenne (already
`lucas_lehmer_sufficiency` L476; different Lucas; do **not** cite
cannonball as Lucas–Lehmer). **Not** Proth primality (consumed
#151; form+witness ≠ pyramidal squares; do **not** revive Pépin /
Pocklington / Euler criterion as namesake). **Not** Zeckendorf /
Binet / Cassini / `fib_gcd` (consumed lame residual / already-in).
**Not** Alcuin integer triangles (prime of this shortlist). **Not**
Frucht graph Aut (consumed #150).

Mathlib v4.10.0 already has the **Nat arithmetic infra this
theorem needs**:

- `Nat` multiplication / division / `n * n`
- `sum_range_id` (Intervals.lean L249) — **not** namesake
- `sum_range_pow` (Bernoulli.lean L280) — **different** Faulhaber
  over `ℚ`; do **not** re-prove, do **not** cite as cannonball
- `Nat.sum_four_squares` — **different** four-square theorem

There is **no** named cannonball / square-pyramid-is-square
theorem, **no** `cannonball` / `Cannonball` / `squarePyramid` /
`SquarePyramidal` / `pyramidalSquare` anywhere under `Mathlib/` or
`Archive/` or `ProofLab/` (this run → ZERO on those names). Do
**not** import `Archive.*`.

OPE-1294 shortlist is **CONSUMED** (#150+#151). This is a
**fresh** catalog-audit leftover id, **not** a Proth leftover
continuation, **not** a Lucas–Lehmer leftover, **not** a
Faulhaber leftover, **not** a four-squares leftover, **not** a
prize leftover, **not** a Formalist Level B revival, **not** a
third slot.

Mill NOW: finite pyramidal-square witnesses leftover beside
Alcuin triangle counts. `Nat` mul/div are waiting the same way
`ZMod` waited for Proth. **Not a rubber-stamp of Faulhaber.**
**Not a rubber-stamp of Lucas–Lehmer.**

Do **not** describe an attack as discovering Watson's theorem.
Do **not** expand into cannonball *uniqueness for all n* as a
sorry, Pell / square-triangular extras, or Lucas–Lehmer as
namesake (uniqueness is leftover-risk of *this* id; Lucas–Lehmer
is already-in different).

## Pinned convention (exact)

**v1 Level A is the square-pyramidal closed form on named
integers: `P(1) = 1²` and `P(24) = 70²`, not labelled
cannonball / Lucas.** The formula `n(n+1)(2n+1)/6` and `k*k`
are load-bearing.

Suggested pin:

```text
-- Level A (not labelled cannonball / Lucas):
-- 1 and 24 are pyramidal squares.

def squarePyramid (n : ℕ) : ℕ :=
  n * (n + 1) * (2 * n + 1) / 6

theorem cannonball_one :
    squarePyramid 1 = 1 * 1

theorem cannonball_twenty_four :
    squarePyramid 24 = 70 * 70

-- optional extra: squarePyramid 2 = 5 is not a square
-- (∃ k, k*k = 5 is false)

-- Level B namesake (only 1 and 24; residual OK)
theorem cannonball_square_pyramid {n k : ℕ}
    (h : 0 < n) (hk : squarePyramid n = k * k) :
    n = 1 ∨ n = 24
```

Named pyramidal numbers are load-bearing.
`squarePyramid` arithmetic is load-bearing.
`k * k` is load-bearing.

**Level A may land only** `P(1) = 1²` / `P(24) = 70²`
(optional extra: `P(2) = 5` is not a square), **not** labelled
cannonball / Lucas. Reuse Mathlib `Nat` arithmetic — **do not
re-prove** Faulhaber / `sum_range_pow` / four-squares /
Lucas–Lehmer.

**Level B** is the namesake: the only positive `n` with `P(n)`
square are `1` and `24`. Do not sorry the namesake; honest
partial is allowed (comment residual, not `sorry`). Pell /
square-triangular / cannonball-on-other-lattices are residual.

## Landmines

1. **Do not re-prove** `Nat` mul/div / `sum_range_id` /
   `sum_range_pow` / `Nat.sum_four_squares` /
   `lucas_lehmer_sufficiency`.
   Already Mathlib. Use elementary Nat arithmetic.
2. **This is not** Faulhaber / `sum_range_pow`. Generating
   function over `ℚ` ≠ pyramidal-is-square. Do not cite as
   cannonball.
3. **This is not** Lucas–Lehmer / Mersenne. Already-in different
   Lucas. Do not cite as cannonball. Do not label theorems
   `lucas_*`.
4. **This is not** Proth / Pépin / Pocklington / Euler criterion
   (consumed #151 leftover-revivals).
5. **This is not** four-squares / two-squares (already-in).
6. **This is not** Zeckendorf / Binet / Cassini / `fib_gcd`
   (lame residual / already-in).
7. **This is not** `alcuin-integer-triangles` (OPE-1310 prime).
   Do not prove Alcuin here.
8. **This is not** frucht-graph-aut (consumed #150) / Cayley-graph
   / GRR.
9. **Do not** re-prime the consumed mill list.
10. **Leave OPE-403 alone.** Leave OPE-1195 leftover status
    alone.
11. **Do not import `Archive.*`.**
12. Default no claim. No novelty claim.

## Out of v1

- Cannonball namesake (only `n = 1` and `n = 24`)
- Square-triangular numbers / Pell
- Lucas–Lehmer as namesake
- Prize claims / Millennium / Beal
