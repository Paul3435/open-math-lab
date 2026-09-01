# Zsigmondy's theorem, Bang case (formalize-only)

**id:** `zsigmondy-theorem`
**ticket:** OPE-853 Scout leftover slot #2 (Director OPE-852; post Descartes #91 + e-irrational #92)
**expected:** known-classical (Bang 1886 / Zsigmondy 1892, `b = 1` case) — **no novelty claim**

## Why not classical / why formalize-only

Settled elementary NT: if `a ≥ 2` and `n ≥ 3`, then `a^n − 1`
has a *primitive prime divisor* — a prime `p` such that the
multiplicative order of `a` modulo `p` is exactly `n` —
except the single case `(a, n) = (2, 6)`.

That is **Bang's theorem**, the `b = 1` case of Zsigmondy
1892 (`a^n − b^n`). Completely classical. **v1 is Bang.**
Full `a^n − b^n` with `b > 1` is **out of v1** (same mill,
not required for the namesake).

Not an open problem. Not a novelty claim. **Not**
`infinite_setOf_prime_modEq_one` (infinitely many primes
`≡ 1 (mod k)` — **already Mathlib**,
`NumberTheory/PrimesCongruentOne.lean`; a primitive prime
divisor of `a^n − 1` is *some* prime `≡ 1 (mod n)` that
divides *this* `a^n − 1` with exact order `n` — a
**different** statement). **Not** infinitude of primes
`≡ 3 (mod 4)` (Cassini-class Euclid; **not** this leftover).
**Not** Wolstenholme (consumed #89 honest Level A). **Not**
Korselt / Carmichael-infinitude / `λ(n)` / odd-perfect.

Mathlib v4.10.0 already has the **cyclotomic arithmetic
this theorem needs**:

- `Polynomial.cyclotomic` / `cyclotomic.eval`
  (`RingTheory/Polynomial/Cyclotomic/{Basic,Eval}.lean`)
- `sub_one_lt_natAbs_cyclotomic_eval` /
  `sub_one_pow_totient_lt_natAbs_cyclotomic_eval`
  (size of `Φ_n(q)` — **use**, do not re-prove)
- `orderOf` on `ZMod p` / `(ZMod p)ˣ`
- `IsCyclic (ZMod p)ˣ` (finite-field units)
- `Nat.Prime` / `Nat.ModEq`
- `infinite_setOf_prime_modEq_one` —
  **already upstream. Different theorem. Never cite as
  this gap.**
- Wilson / Lucas binomial / `harmonic_not_int` /
  Fermat–Euler `pow_totient` / Bertrand / Zeckendorf /
  quadratic reciprocity — **already upstream. Different.**

There is **no** Zsigmondy, **no** Bang theorem, **no**
`primitive prime divisor`, and **no** named
`orderOf (a : ZMod p) = n` existence for `a^n − 1` anywhere
under `Mathlib/` or `Archive/` (word-regexp `zsigmondy` /
`bang.?theorem` / `primitivePrime` this run → ZERO). Do
**not** import `Archive.*`.

OPE-838 considered-not-slotted listed Dirichlet AP (analytic
sink) and infinitely many primes `≡ 3 (mod 4)` (Cassini-class),
not Bang/Zsigmondy. Descartes #91 + e-irrational #92 are now
**CONSUMED**. This is a **fresh** NT leftover after a
combinatorics prime, **not** a Wolstenholme leftover, **not**
a Korselt leftover, **not** a third slot.

Mill NOW: elementary NT with cyclotomic eval waiting, after
a probabilistic-combinatorics prime (`erdos-ramsey-lower`).
Analogous to Wolstenholme after PIE, and to e-irrational
after Descartes. **Not a second combinatorics leftover.**

Do **not** describe an attack as discovering primitive
prime divisors. Do **not** expand into full `a^n − b^n`,
Aurifeuillean factorizations, or Artin's primitive-root
conjecture.

## Pinned convention (exact)

**v1 is Bang** (`b = 1`). Encoding: Mathlib `orderOf` on
`(a : ZMod p)` (or on `(a : (ZMod p)ˣ)` after proving
`p ∤ a`).

Suggested pin:

```text
-- p is a primitive prime divisor of a^n − 1
def IsPrimitivePrimeDivisor (p a n : ℕ) : Prop :=
  p.Prime ∧ ¬ p ∣ a ∧ orderOf (a : ZMod p) = n

-- Level A (not labelled Bang/Zsigmondy): Φ_n(a) has a
-- prime factor, for 2 ≤ a and 3 ≤ n except (2,6).
-- (cyclotomic.eval (a : ℤ) n).natAbs ≥ 2  … or ∃ p, p.Prime ∧ p ∣ Φ_n(a)

-- Level B namesake
theorem bang (a n : ℕ) (ha : 2 ≤ a) (hn : 3 ≤ n)
    (hex : ¬ (a = 2 ∧ n = 6)) :
    ∃ p, IsPrimitivePrimeDivisor p a n
```

The exception `(2, 6)` is load-bearing:
`2^6 − 1 = 63 = 7 · 9` and `7` already divides `2^3 − 1`.

`n = 1` and `n = 2` are **out of v1** (Bang classically
starts at `n ≥ 3`; the `n = 2` Zsigmondy exception
`a + 1` a power of two is not this pin).

**Level A may land only that `Φ_n(a)` is `> 1` in absolute
value** (so some prime divides it), not labelled Bang.
Use `sub_one_lt_natAbs_cyclotomic_eval` — **do not re-prove
the size bound**. **Level B** is the namesake: a prime
factor of `Φ_n(a)` does not divide `a^d − 1` for `d < n`,
hence has order `n`. The `(2, 6)` case is the only
exclusion.

## Landmines

1. **Do not re-prove** `cyclotomic` / `cyclotomic.eval` /
   `sub_one_lt_natAbs_cyclotomic_eval` /
   `IsCyclic (ZMod p)ˣ` / `pow_totient` / Wilson / Lucas /
   `infinite_setOf_prime_modEq_one`. Already Mathlib. Use
   them.
2. **This is not** infinitude of primes `≡ 1 (mod k)`.
   Already `PrimesCongruentOne.lean`. Different theorem
   (uses the same cyclotomic size bound as *engine*).
3. **This is not** infinitude of primes `≡ 3 (mod 4)`.
   Cassini-class Euclid. OPE-838 skipped it. Not this
   leftover.
4. **This is not** Dirichlet primes in AP. Analytic sink.
5. **This is not** Wolstenholme / Korselt / Euclid–Euler /
   Carmichael-infinitude / `λ(n)` / odd-perfect / aliquot.
   Consumed or banned leftovers.
6. **This is not** full Zsigmondy `a^n − b^n` for `b > 1`.
   Out of v1.
7. **This is not** Artin's primitive-root conjecture
   (open). Out of v1.
8. **This is not** `erdos-ramsey-lower` (the prime). Do
   **not** assign first unless Director swaps.
9. **Do not re-prime** n-fold-inclusion-exclusion /
   wolstenholme-theorem / lovasz-local-lemma /
   korselt-carmichael / vosper / heron / euclid-euler /
   bipartite / moore / stirling / kst / pentagonal /
   sunflower / combinatorial-nullstellensatz /
   kruskal-katona / oddtown / cayley / mycielski /
   friendship / havel / menger / greedy / Brooks /
   Dilworth / Eulerian / König / Dirac / EKR /
   descartes-rule-of-signs / e-irrational.
10. **No `Archive.*` import.**
11. **Leave OPE-403 alone.**

## Proof sketch (classical, Bang)

Level A: `a^n − 1 = ∏_{d ∣ n} Φ_d(a)`. For `n ≥ 3`, `a ≥ 2`,
`(a, n) ≠ (2, 6)`, the integer `|Φ_n(a)|` is `> 1` (Mathlib
size bound). So some prime `p` divides `Φ_n(a)`. **Not**
labelled Bang.

Level B: if `p ∣ Φ_n(a)` then `p ∣ a^n − 1` and `p` does not
divide `a^d − 1` for proper `d ∣ n`. Hence the order of `a`
mod `p` is exactly `n`. The `(2, 6)` exclusion is the
classical unique failure (`Φ_6(2) = 3` already divides
`2^2 − 1` after the usual identification — pin the
literature identity carefully; do not sorry it). Cap two
levels. No `b > 1`, no Artin.

## Canonical source (pin in this STATEMENT)

Zsigmondy, *Zur Theorie der Potenzreste*, Monatsh. Math. 3
(1892). Bang, *Taltheoretiske Undersøgelser*, Tidsskrift for
Math. (1886) for `b = 1`. Compact form: Wikipedia
*Zsigmondy's theorem* — primitive prime divisors of
`a^n − b^n`; **v1 pins Bang `b = 1`, `n ≥ 3`, exception
`(2, 6)` only.** Type pin: `orderOf (a : ZMod p) = n`.
`infinite_setOf_prime_modEq_one` / Wolstenholme / Korselt /
Wilson are **different** statements, not this claim.

## Out of scope

- Full Zsigmondy `a^n − b^n` for `b > 1`
- `n = 1` / `n = 2` exceptions (`a + b` a power of two)
- Artin's primitive-root conjecture
- Infinitude of primes `≡ 1 (mod k)` (already Mathlib)
- Infinitude of primes `≡ 3 (mod 4)` (Cassini-class)
- Dirichlet AP / PNT
- Wolstenholme-B / Carmichael-infinitude / `λ(n)`
- Re-primes listed above
- Novelty / external claim
