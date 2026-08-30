# Euler's pentagonal number theorem — partition recurrence (formalize-only)

**id:** `pentagonal-number-theorem`
**ticket:** OPE-735 Scout leftover slot #2 (support OPE-734; post sunflower #70 + combinatorial Nullstellensatz #71)
**expected:** known-classical (Euler 1750 / Franklin 1881) — **no novelty claim**

## Why not classical / why formalize-only

Settled partition identity: writing `p(n) = Fintype.card (Nat.Partition n)`
(with `p(0) = 1`), the pentagonal recurrence

```text
p(n) = ∑_{k≠0} (−1)^{k−1} p(n − ω(k))
```

holds for `n > 0`, where `ω(k) = k(3k−1)/2` runs over the generalized
pentagonal numbers and `p(m) = 0` for `m < 0` (i.e. omit those k).
Not an open problem.

Mathlib v4.10.0 already has the **algebra this theorem needs**:

- `Nat.Partition` with `Fintype` instance (`Combinatorics/Enumerative/Partition.lean`)
  — file header even lists Euler's partition theorem as motivation
- `odds` / `distincts` Finsets (used by ProofLab Euler / Schur)
- `PowerSeries` (`RingTheory/PowerSeries`) — **not required for v1**

There is **no** pentagonal-number / Franklin-involution ident
anywhere under `Mathlib/` or `Archive/` (word-regexp this run → ZERO).
Archive `Wiedijk100Theorems/Partition.lean` is Euler's **odd = distinct**
theorem (generating-function proof) — **different** theorem, already
consumed in ProofLab as `euler_odd_eq_distinct` (Glaisher bijection,
PR #43). Schur partition / Glaisher (PR #36-era / `SchurGlaisher.lean`)
is a **different** congruence identity. This is **not** a re-prime of
`euler-odd-distinct` or `schur-partition`.

Do **not** describe an attack as discovering the pentagonal number
theorem. Do **not** expand into Rogers–Ramanujan, Jacobi triple
product, or the PowerSeries generating-function form as a second id.

## Pinned convention (exact)

**Partition pin:** `partitionFunction n := Fintype.card (Nat.Partition n)`.
`Partition 0` is unique, so `p(0) = 1`. Stay on `ℕ`; encode “p(negative)=0”
by omitting terms with `ω(k) > n`.

**Pentagonal pin:** for `k ≥ 1`,

```text
ω(k)  = k * (3 * k - 1) / 2    -- 1, 5, 12, 22, …   (k)
ω'(k) = k * (3 * k + 1) / 2    -- 2, 7, 15, 26, …   (−k)
```

Both are integers (`k(3k±1)` is always even). Prove exactness as
Level A glue, **not** labelled pentagonal.

**Sign pin (ℕ equation, no `ℤ` sum):** k and −k have the same sign
`(−1)^{k−1}`. Move even-k terms to the left:

```text
theorem pentagonal_number {n : ℕ} (hn : 0 < n) :
    partitionFunction n
      + (∑ k ∈ Finset.range (n + 1),
          if 0 < k ∧ Even k ∧ pentagonal k ≤ n then
            partitionFunction (n - pentagonal k) else 0)
      + (∑ k ∈ Finset.range (n + 1),
          if 0 < k ∧ Even k ∧ pentagonal' k ≤ n then
            partitionFunction (n - pentagonal' k) else 0)
    =
        (∑ k ∈ Finset.range (n + 1),
          if 0 < k ∧ Odd k ∧ pentagonal k ≤ n then
            partitionFunction (n - pentagonal k) else 0)
      + (∑ k ∈ Finset.range (n + 1),
          if 0 < k ∧ Odd k ∧ pentagonal' k ≤ n then
            partitionFunction (n - pentagonal' k) else 0)
```

`Finset.range (n+1)` is load-bearing: `ℕ` is not a Fintype.
`0 < k` excludes the k = 0 term (that term *is* `p(n)`).

**v1 is the finite recurrence via Franklin's involution.** The
PowerSeries identity `∏ (1 − q^n) = ∑_{k∈ℤ} (−1)^k q^{ω(k)}` is a
stretch **out of v1**, not a leftover re-prime.

## Landmines

1. **This is not `euler-odd-distinct`.** ProofLab already has
   `euler_odd_eq_distinct` (Glaisher). Odd-parts = distinct-parts is
   a *different* Euler theorem. Do **not** re-prime that id.
2. **This is not `schur-partition` / Glaisher congruence.** Parts
   ≡ ±1 mod 6 vs distinct ≡ 1,2 mod 3 is consumed. Different identity.
3. **This is not Archive `Theorems100.partition_theorem`.** That
   file is odd=distinct via generating functions. Do **not** import
   `Archive.*`. Do **not** relabel it as pentagonal.
4. **`ℕ` division.** `k * (3 * k - 1) / 2` is exact for `k ≥ 1`;
   prove it. `3 * k - 1` needs `1 ≤ k` so there is no underflow.
5. **Signs live in the equation shape**, not in a `ℤ`-valued `p`.
   Do not make `partitionFunction` return `ℤ`.
6. **Do not prove Rogers–Ramanujan / Jacobi triple product /
   generating-function `PowerSeries` form in this id.**
7. **Do not re-prime** sunflower-erdos-rado / combinatorial-nullstellensatz
   / kruskal-katona / oddtown / euler-odd-distinct / schur-partition /
   cayley-trees / mycielski / Dilworth / Eulerian / König / Dirac.
8. **No `Archive.*` import.**
9. **Leave OPE-403 alone.**

## Proof sketch (classical, Franklin 1881)

Level A: `pentagonal` / `pentagonal'` exact division for `k ≥ 1`;
`p(0) = 1`; `p(1) = 1` (matches `+p(0)` from `ω(1)=1`); recurrence
spot-checks `n ≤ 10` via `native_decide` on `Fintype.card (Partition n)`,
**not** labelled pentagonal number theorem.

Level B: namesake `pentagonal_number`. Franklin's sign-reversing
involution on `Nat.Partition n`: compare the smallest part against
the longest consecutive “staircase” of distinct parts at the top;
move one onto the other. The involution is fixed-point-free except
on the two pentagonal staircase shapes of n (when n itself is
generalized pentagonal), which contribute the leftover `±1` that
the recurrence accounts for via `p(0)`.

Partial: **Level A** formula glue + small-n guard, zero sorry, not
labelled pentagonal. **Level B** namesake recurrence. Cap two levels.
No PowerSeries, no Rogers–Ramanujan, no Glaisher.

## Lean gate (when attacked)

- Target module: `proofs/lean-project/ProofLab/Pentagonal.lean`
- Reuse Mathlib `Nat.Partition` / `Fintype` instance. Do **not**
  re-prove `euler_odd_eq_distinct` / `schur_partition`. Do **not**
  import `Archive.Wiedijk100Theorems.Partition`.
- Zero `sorry`; `lake env lean` exit 0
- Default **no claim**
- Do not import `Archive.*`

## Canonical source

L. Euler, *Demonstratio theorematis circa ordinem in summis divisorum*,
Novi Commentarii academiae scientiarum Petropolitanae 5 (1760, presented
1750) 75–83 (pentagonal number theorem). Combinatorial engine:
F. Franklin, *Sur le développement du produit infini `(1−x)(1−x²)(1−x³)…`*,
Comptes Rendus 92 (1881) 448–450. Textbook pin: Andrews, *The Theory of
Partitions*, pentagonal number theorem / Franklin involution; Hardy–Wright,
*An Introduction to the Theory of Numbers*, §19.11. Type pin: Mathlib
`Nat.Partition` + `Fintype.card` + the ℕ recurrence above. Euler
odd=distinct, Schur partition, and Archive Theorems100 partition are
**different** statements, not this claim.
