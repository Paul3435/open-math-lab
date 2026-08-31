# Euclid–Euler even perfect numbers (formalize-only)

**id:** `euclid-euler-perfect`
**ticket:** OPE-770 Scout leftover slot #2 (support OPE-769; post Moore #76 + Stirling #77)
**expected:** known-classical (Euclid IX.36 / Euler) — **no novelty claim**

## Why not classical / why formalize-only

Settled number-theory characterization: an even natural number
`n` is perfect (the sum of its proper divisors equals `n`) if
and only if

```text
n = 2 ^ k * mersenne (k + 1)
```

for some `k ≥ 1` with `Nat.Prime (mersenne (k + 1))`
(i.e. `2^{k+1} − 1` is a Mersenne prime). Not an open problem.

Mathlib v4.10.0 already has the **arithmetic this theorem needs**:

- `Nat.Perfect` (`NumberTheory/Divisors.lean`) — `∑ properDivisors = n ∧ 0 < n`,
  plus `perfect_iff_sum_divisors_eq_two_mul`
- `mersenne p := 2 ^ p - 1` (`NumberTheory/LucasLehmer.lean`)
- `σ 1` / `isMultiplicative_sigma` / `sigma_one_apply`
  (`NumberTheory/ArithmeticFunction.lean`)
- Lucas–Lehmer primality test for Mersenne numbers — **already
  upstream**, **not** this theorem. Do **not** re-prove it.
- `Nat.Prime` / geometric sums / multiplicity of `2`

There is **no** Euclid–Euler / even-perfect characterization
anywhere under `Mathlib/` (word-regexp `even_perfect` /
`perfect_two_pow` / `euclid_euler` this run → ZERO files). The
theorem **is** in `Archive/Wiedijk100Theorems/PerfectNumbers.lean`
(`Theorems100.Nat.perfect_two_pow_mul_mersenne_of_prime` and
`eq_two_pow_mul_prime_mersenne_of_even_perfect`). **Do not
import `Archive.*`.** Re-prove in ProofLab. Archive existence
is feasibility evidence, not a citation of a Mathlib theorem.

Odd perfect numbers are **open** and **out of v1**. Do not
attack them; do not describe this id as settling the odd-perfect
problem.

This is **not** a re-prime of `frobenius-coin-problem` (already
in Mathlib as `frobeniusNumber_pair`), **not** Catalan /
derangement / Stirling `n!` (already Mathlib), **not**
Lucas–Lehmer, **not** a leftover of `stirling-second-kind` /
`pentagonal-number-theorem` / `euler-odd-distinct`.

## Pinned convention (exact)

**Encoding pin:** Mathlib `mersenne` and `Nat.Perfect`, matching
the Archive statement (without importing it):

```text
theorem euclid_perfect
    (k : ℕ) (h : Nat.Prime (mersenne (k + 1))) :
    Nat.Perfect (2 ^ k * mersenne (k + 1))

theorem euler_even_perfect {n : ℕ}
    (hev : Even n) (hp : Nat.Perfect n) :
    ∃ k : ℕ, Nat.Prime (mersenne (k + 1)) ∧
      n = 2 ^ k * mersenne (k + 1)
```

**v1 is the even characterization.** The namesake may be the
conjunction (even + perfect ↔ Euclid form). Level A may land
only `euclid_perfect` (Mersenne prime ⇒ perfect), **not**
labelled the full namesake.

`k ≠ 0` is load-bearing for evenness (`mersenne 1 = 1` is not
prime, so the prime hypothesis already excludes `k = 0`).

## Landmines

1. **Do not import `Archive.Wiedijk100Theorems.PerfectNumbers`.**
   Standing ProofLab rule. Transcribe the classical argument;
   do not `import Archive.*`.
2. **Do not re-prove Lucas–Lehmer.** Already in
   `NumberTheory/LucasLehmer.lean`. The Mersenne-prime hypothesis
   is an *input*, not a goal.
3. **Odd perfect numbers are OPEN.** Out of v1. The theorem is
   an *even* characterization. Dropping `Even n` makes Euler's
   converse false-or-open.
4. **This is not Frobenius.** `frobeniusNumber_pair` is already
   Mathlib (OPE-25 demotion). Never cite Frobenius as this gap.
5. **This is not Catalan / derangement / Stirling `n!`.** Already
   Mathlib. Name collision only with Euler-the-person vs
   Euler-odd-distinct / Eulerian-hierholzer (consumed combinatorics
   ids).
6. **`σ` multiplicativity is already Mathlib.** Use
   `isMultiplicative_sigma`; do not re-prove it as this namesake.
7. **Do not re-prime** stirling-second-kind / pentagonal /
   euler-odd-distinct / schur-partition / frobenius / catalan /
   moore-degree-girth / kovari-sos-turan.
8. **No `Archive.*` import.**
9. **Leave OPE-403 alone.**

## Proof sketch (classical, Euclid + Euler)

Level A: Euclid direction. If `q = mersenne (k + 1)` is prime,
then `2^k` and `q` are coprime, `σ` is multiplicative,
`σ(2^k) = mersenne (k + 1) = q`, `σ(q) = q + 1 = 2^{k+1}`,
hence `σ(2^k * q) = q * 2^{k+1} = 2 · (2^k * q)`. Translate
via `perfect_iff_sum_divisors_eq_two_mul`. **Not** labelled
the full namesake.

Level B: Euler converse. Write even `n = 2^k * m` with `m` odd,
`k ≥ 1`. Perfect ⇒ `σ(n) = 2n`. Multiplicativity + the formula
for `σ(2^k)` forces `σ(m) = m + 1` (hence `m` prime) and
`m = mersenne (k + 1)`. Cap two levels. No odd-perfect, no
Lucas–Lehmer, no abundance / deficiency theory.

## Canonical source (pin in this STATEMENT)

Euclid, *Elements*, Book IX, Proposition 36 (Mersenne primes
produce even perfect numbers). Leonhard Euler, *De numeris
amicabilibus* / posthumous even-perfect converse (the form
quoted in every NT textbook). Type pin: `Nat.Perfect` +
`mersenne`. Wiedijk 100 Theorem 70 is the *same* statement
(Archive-only at this pin) — do not import it. Odd perfect
numbers, Lucas–Lehmer, Frobenius, and Catalan are different
statements, not this claim.

## Out of scope

- Odd perfect numbers (open)
- Lucas–Lehmer primality (already Mathlib)
- Multiply perfect / amicable / sociable numbers
- Frobenius / Catalan / derangement / Stirling `n!` (already Mathlib)
- Archive import
- Re-primes listed above
- Novelty / external claim
