# Stirling numbers of the second kind — set-partition count (formalize-only)

**id:** `stirling-second-kind`
**ticket:** OPE-754 Scout leftover slot #2 (support OPE-753; post KST #73 + pentagonal #74)
**expected:** known-classical (Stirling / set partitions) — **no novelty claim**

## Why not classical / why formalize-only

Settled enumerative identity: writing `S(n,k)` for the number of
partitions of an `n`-element set into exactly `k` nonempty unlabeled
blocks, the recurrence

```text
S(0,0) = 1,     S(n,0) = 0 (n > 0),     S(0,k) = 0 (k > 0),
S(n+1, k+1) = (k+1) · S(n, k+1) + S(n, k)
```

holds, and `S(n,k)` equals the number of `Finpartition`s of
`univ : Finset (Fin n)` with `parts.card = k`. Not an open problem.

Mathlib v4.10.0 already has the **algebra this theorem needs**:

- `Finpartition` (`Order/Partition/Finpartition.lean`) — finite
  partitions of a lattice element; on `Finset α` these *are* set
  partitions (parts nonempty, pairwise disjoint, sup = univ)
- `Setoid.IsPartition` (`Data/Setoid/Partition.lean`)
- `Nat.choose` / `Nat.factorial`
- **Catalan numbers** (`Combinatorics/Enumerative/Catalan.lean`) —
  **different** enumerative sequence, **already upstream**. Never
  cite Catalan as this gap (same class as the OPE-25 Catalan demotion).
- **Stirling's formula for `n!`**
  (`Analysis/SpecialFunctions/Stirling.lean`, `stirlingSeq`) —
  **different** theorem (analytic approximation). **Never cite
  Stirling's formula as this gap.** Name collision only.

There is **no** Stirling-second-kind / `S(n,k)` / set-partition
count ident anywhere under `Mathlib/` or `Archive/` (word-regexp
`stirlingSecond` / `stirling_second` / `Nat.bell` over `Mathlib/`
this run → ZERO combinatorics hits; the only `Stirling` file is
the `n!` approximation). Integer partitions `Nat.Partition` exist
and are consumed in ProofLab as Euler odd=distinct, Schur, and
pentagonal — **different** (compositions of an integer, not
partitions of a set). This is **not** a re-prime of
`pentagonal-number-theorem` / `euler-odd-distinct` / `schur-partition`
/ `catalan-recurrence`.

Do **not** describe an attack as discovering Stirling numbers.
Do **not** expand into Stirling first kind (cycle numbers), Bell
generating functions as a second id, or Stirling's `n!` formula.

## Pinned convention (exact)

**Numeric pin:** a recursive `ℕ` function, **not** labelled as the
counting theorem:

```text
def stirlingSecond : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, k + 1 => 0
  | n + 1, 0 => 0
  | n + 1, k + 1 =>
      (k + 1) * stirlingSecond n (k + 1) + stirlingSecond n k
```

**Counting pin:** `Finpartition` of `univ : Finset (Fin n)`.

```text
abbrev StirlingPartition (n k : ℕ) :=
  { P : Finpartition (univ : Finset (Fin n)) // P.parts.card = k }

theorem stirling_second {n k : ℕ} [Fintype (StirlingPartition n k)] :
    Fintype.card (StirlingPartition n k) = stirlingSecond n k
```

**v1 is the counting interpretation of the recurrence.** The
inclusion-exclusion formula

```text
S(n,k) = (1/k!) Σ_{j=0}^k (-1)^{k-j} binom(k,j) j^n
```

is a convexity / `ℕ`-division stretch — **out of v1**, not a leftover
re-prime. Bell numbers `B_n = Σ_k S(n,k)` are an optional cheap
sum corollary, **not** labelled Stirling.

Level A may land the recursive `def` plus `S(n,1) = 1` (`n ≥ 1`),
`S(n,n) = 1`, `S(n,2) = 2^{n-1} - 1` (`n ≥ 1`), and the recurrence
as a `rfl`/`Nat` computation, **not** labelled `stirling_second`.

## Landmines

1. **This is not Stirling's formula for `n!`.** Already in
   `Analysis/SpecialFunctions/Stirling.lean`. Never cite it as
   this gap (name collision only; same class as group Cayley vs
   labelled trees, Hilbert NS vs combinatorial NS).
2. **This is not Catalan.** Already in
   `Combinatorics/Enumerative/Catalan.lean` (OPE-25 demotion).
   Never cite Catalan as a gap.
3. **This is not integer partitions.** `Nat.Partition` /
   pentagonal / Euler odd=distinct / Schur are consumed or
   Archive-wrong-theorem. Set partitions ≠ summands of `n`.
4. **This is not Szemerédi regularity.** Mathlib uses
   `Finpartition` as the *carrier* of regularity partitions.
   Counting `parts.card = k` is the gap, not the regularity lemma
   (already upstream).
5. **This is not Stirling first kind** (signed cycle numbers).
   Out of v1.
6. **`Fintype (StirlingPartition n k)` may need to be built.**
   Do not sorry it; Level A can stay on the recursive `ℕ`
   function until the instance exists.
7. **Do not prove inclusion-exclusion / Bell EGF / first kind
   in this id.**
8. **Do not re-prime** pentagonal-number-theorem /
   euler-odd-distinct / schur-partition / catalan-recurrence /
   kovari-sos-turan / sunflower / combinatorial-nullstellensatz.
9. **No `Archive.*` import.**
10. **Leave OPE-403 alone.**

## Proof sketch (classical, Stanley EC1 §1.4)

Level A: recursive `stirlingSecond`; `S(n,0)` / `S(0,k)` landmines;
`S(n,1) = 1` (`n ≥ 1`); `S(n,n) = 1`; `S(n,2) = 2^{n-1}-1`
(`n ≥ 1`, the distinguished-block / complement split). **Not**
labelled Stirling.

Level B: namesake `stirling_second`. Bijection: given a partition
of `Fin (n+1)`, isolate the block containing `n`. If that block is
a singleton, the remainder is a `k`-block partition of `Fin n`
after relabelling (the `S(n,k)` term, shifted). If not, delete `n`
from its block and get a `(k+1)`-block partition of `Fin n`, with
`k+1` choices for which block received `n`. Cap two levels.

## Canonical source (pin in this STATEMENT)

Richard P. Stanley, *Enumerative Combinatorics*, Volume 1, 2nd ed.,
Cambridge University Press, 2011, §1.4 (Stirling numbers of the
second kind). Also Graham–Knuth–Patashnik, *Concrete Mathematics*.
Type pin: recursive `stirlingSecond : ℕ → ℕ → ℕ` +
`Finpartition (univ : Finset (Fin n))`. Stirling's `n!` formula,
Catalan, `Nat.Partition`, Bell EGF, and first-kind cycle numbers
are different statements, not this claim.

## Out of scope

- Stirling's approximation `n! ~ √(2πn) (n/e)^n` (already Mathlib)
- Catalan (already Mathlib)
- Integer partitions / pentagonal / Glaisher / Schur
- Stirling first kind; Bell generating function as a second id
- Inclusion-exclusion closed form (stretch)
- Szemerédi regularity (already Mathlib)
- Re-primes listed above
- Novelty / external claim
