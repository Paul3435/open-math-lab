# Wolstenholme's theorem (formalize-only)

**id:** `wolstenholme-theorem`
**ticket:** OPE-821 Scout leftover slot #2 (support OPE-820; post LLL #85 + Korselt #86)
**expected:** known-classical (Wolstenholme 1862) — **no novelty claim**

## Why not classical / why formalize-only

Settled elementary-NT congruence: for a prime `p ≥ 5`,

```text
(2p − 1).choose (p − 1) ≡ 1 (mod p³)
```

Equivalent classical forms (corollaries, not required for the
namesake): `(2p).choose p ≡ 2 (mod p³)`, and the numerator of
the harmonic number `H_{p−1}` is divisible by `p²`. Not an open
problem.

Mathlib v4.10.0 already has the **arithmetic this theorem
needs**:

- `Nat.choose` (`Data/Nat/Choose/Basic.lean`)
- `Nat.ModEq` / `ZMod`
- `harmonic : ℕ → ℚ` (`NumberTheory/Harmonic/Defs.lean`) —
  **definition only**. `harmonic_not_int` (H_n is not an integer
  for `n ≥ 2`) is a **different** theorem. Divergence of the
  harmonic series is Wiedijk #34
  (`Real.tendsto_sum_range_one_div_nat_succ_atTop`) — **already
  upstream. Never cite as this gap.**
- Lucas binomial (`Data/Nat/Choose/Lucas.lean`) — **already
  upstream. Never re-prove. Never cite as this gap.**
- Wilson (`NumberTheory/Wilson.lean`, `wilsons_lemma`) —
  **already upstream.**
- Fermat–Euler `pow_totient` / Euler criterion / quadratic
  reciprocity — **already upstream.**

There is **no** Wolstenholme theorem, **no** `p^3` binomial
congruence, and **no** `H_{p-1} ≡ 0 (mod p²)` identity anywhere
under `Mathlib/` or `Archive/` (word-regexp `wolstenholme` this
run → ZERO; `harmonic` hits are Defs/Bounds/Int/EulerMascheroni
only). ProofLab has Korselt (`theorem korselt`) — **different**
theorem (consumed #86). This is **not** a re-prime of Korselt,
**not** Carmichael-infinitude / `λ(n)` / odd-perfect.

OPE-804 considered this id and **benched it** only as an NT
mill-duplicate of then-unassigned Korselt (leftover cap).
Korselt is now **CONSUMED** (#86). This is a **fresh**
candidate, **not** a Korselt leftover.

Mill: elementary NT congruence leftover after a combinatorial
prime — same 2-slot pattern as Korselt after LLL, **not** a
second NT prime after Korselt.

Do **not** describe an attack as discovering Wolstenholme. Do
**not** expand into Bernoulli numbers, p-adic zeta, irregular
primes, or **Wolstenholme primes** (the `mod p^4` strengthening;
open-ended / computational — **out of v1**).

## Pinned convention (exact)

**v1 is the binomial `p³` congruence**, not harmonic-in-ℚ, not
Bernoulli. `5 ≤ p` is load-bearing (`p = 2, 3` fail `mod p³`).

Suggested pin:

```text
theorem wolstenholme {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]
```

`p.Prime` and `5 ≤ p` are load-bearing. Encoding is `Nat.ModEq`
on `Nat.choose`, not a `ZMod (p^3)` coercion (either is fine if
the namesake is this congruence).

**Level A may land only the `p²` (weak) form**, not labelled
Wolstenholme:

```text
p.Prime → 3 ≤ p → (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 2]
```

(`p = 3` holds mod 9, fails mod 27). Optional glue: the same
congruence mod `p` (true for every prime; too cheap to be Level
A by itself). **Level B** is the `p³` namesake
`wolstenholme`.

Harmonic form `p^2 ∣ (harmonic (p-1)).num` (after writing
`H_{p-1}` in lowest terms, or an equivalent `ℚ` statement) may
land as a **corollary**, not the namesake, and only if it does
not pull Bernoulli / `ℚ` denominator fights into the critical
path. Prefer staying on `ℕ`.

## Landmines

1. **Do not prove Wolstenholme primes / `mod p^4`.** Out of v1.
2. **Do not use Bernoulli numbers / p-adic zeta / irregular
   primes.** Elementary binomial / harmonic pairing only.
3. **This is not Wilson.** `wilsons_lemma` is already Mathlib.
4. **This is not Lucas binomial.** Already
   `Data/Nat/Choose/Lucas.lean`. Use it if needed; do not
   re-prove it.
5. **This is not `harmonic_not_int` / harmonic-series
   divergence.** Already Mathlib (different statements).
6. **This is not Korselt / Carmichael.** Consumed PR **#86**.
   Do not re-prime. Not infinitude, not `λ(n)`, not odd-perfect.
7. **This is not Euclid–Euler.** Consumed #80.
8. **This is not FLT n=3/4 / totient / Euler criterion /
   quadratic reciprocity.** Already Mathlib.
9. **Do not re-prime** lovasz-local-lemma / korselt-carmichael /
   vosper / heron / euclid-euler / bipartite / moore / stirling /
   kst / pentagonal / sunflower / combinatorial-nullstellensatz /
   kruskal-katona / oddtown / cayley / mycielski / friendship /
   havel / menger / greedy / Brooks / Dilworth / Eulerian /
   König / Dirac / EKR.
10. **No `Archive.*` import.**
11. **Leave OPE-403 alone.**

## Proof sketch (classical, Wolstenholme)

Level A (`mod p²`, `p ≥ 3`): pair `k` with `p−k` in
`H_{p−1}` or expand `(2p−1).choose (p−1)` as a product of `p`
consecutive numerators over `(p−1)!`; the `p¹` factor is
obvious and the next `p` comes from a symmetric sum of
reciprocals. **Not** labelled Wolstenholme.

Level B (`mod p³`, `p ≥ 5`): lift the same expansion one more
`p` (the extra vanishing uses `p ≥ 5` so that `2, 3` in
denominators stay coprime to `p` and the cubic terms survive).
Cap two levels. No Bernoulli, no `mod p^4`.

## Canonical source (pin in this STATEMENT)

J. Wolstenholme, *On certain properties of prime numbers*,
Quarterly Journal of Pure and Applied Mathematics **5** (1862),
35–39. Type pin: `Nat.choose` + `Nat.ModEq` + `p.Prime` +
`5 ≤ p`. Wilson, Lucas binomial, `harmonic_not_int`, harmonic
divergence, Korselt, Euclid–Euler, FLT, and totient are
**different** statements, not this claim.

## Out of scope

- Wolstenholme primes / congruence mod `p^4`
- Bernoulli / p-adic zeta / irregular primes
- Re-proving Wilson / Lucas / harmonic_not_int / totient / FLT
- Korselt / Carmichael infinitude / `λ(n)` / odd-perfect
- Re-primes listed above
- Novelty / external claim
