# Irrationality of e (formalize-only)

**id:** `e-irrational`
**ticket:** OPE-848 Formalist Level A+B (Scout OPE-838 leftover slot #2; Director OPE-847; support OPE-837; post Descartes #91)
**expected:** known-classical (Euler / Fourier series remainder) — **no novelty claim**

## Why not classical / why formalize-only

Settled analysis/NT fact: `Real.exp 1` is irrational.

Not an open problem. **Not** the Hermite–Lindemann /
Wiedijk 67 *transcendence* of e (external Lean only — a
**different, harder** theorem; **out of v1**).

Mathlib v4.10.0 already has the **series this theorem needs**:

- `Real.exp` / `NormedSpace.exp`
- `exp_eq_tsum_div` :
  `exp 𝕂 = fun x => ∑' n, x^n / n!`
  (`Analysis/NormedSpace/Exponential.lean`)
- `Irrational` predicate
  (`Data/Real/Irrational.lean`) including
  `irrational_sqrt_two`, `Transcendental.irrational`
- `Nat.factorial`
- Liouville numbers `Liouville.transcendental` (Wiedijk #18)
  — **already upstream, and e is not Liouville.** Never cite
  Liouville as this gap.
- `harmonic_not_int` / harmonic-series divergence —
  **already upstream. Different theorems.**

There is **no** `Irrational (Real.exp 1)`, **no**
`irrational_exp_one`, and **no** named irrationality of e
anywhere under `Mathlib/` or `Archive/` (word-regexp this run:
`Irrational` in `Exp.lean` / `Exponential.lean` /
`Data/Complex/Exponential.lean` → ZERO theorems about `exp 1`;
Archive transcendental/e-irrational → ZERO). Wiedijk 100.yaml
#67 is **"e is Transcendental"** with only an **external**
github link — **no Mathlib decl**, and that is **not** this
claim. Do **not** treat that external file as upstream. Do
**not** import `Archive.*`.

OPE-821 considered-not-slotted listed harmonic / Wilson /
Lucas as already-in, not e-irrational. This is a **fresh**
analysis leftover after an algebra prime, **not** a
Wolstenholme leftover, **not** a PIE leftover, **not** a
third slot.

Mill: analysis/NT leftover after a polynomial-algebra prime
(Descartes) — diversification off the just-consumed
enumerative+NT mill (PIE #88 + Wolstenholme #89). **Not** a
second NT congruence leftover. **Not** π-irrational (genuine
gap this run; Niven *integral* is an analysis-API sink —
benched, leftover cap goes here because `exp_eq_tsum_div` is
waiting).

Do **not** describe an attack as discovering that e is
irrational. Do **not** expand into transcendence of e or π
(Wiedijk 67/53 sinks). Do **not** prove π irrational (Niven
1947 integral; different theorem).

## Pinned convention (exact)

**v1 is `Irrational (Real.exp 1)`**, not transcendence, not
`exp q` for rational `q ≠ 0`, not π.

Suggested pin:

```text
theorem irrational_exp_one : Irrational (Real.exp 1)
```

Encoding is Mathlib `Irrational` (`¬ ∃ q : ℚ, ↑q = Real.exp 1`).
`Real.exp_eq_exp_ℝ` / `exp_eq_tsum_div` are **to be used, not
re-proved**.

**Level A may land only the remainder bound**, not labelled
irrational:

```text
-- s n = ∑ k ∈ range (n+1), (1 : ℝ) / k!
-- 0 < Real.exp 1 - s n
-- Real.exp 1 - s n < 2 / (n+1)!     -- or any 0 < rem < 1/n! bound
```

via the tail of `exp_eq_tsum_div` at `x = 1`. **Level B** is
the namesake: if `exp 1 = p / q`, take `n ≥ q`, multiply the
remainder by `n!`, and derive a positive integer `< 1`.

## Landmines

1. **Do not re-prove `exp_eq_tsum_div` / `Real.exp`.** Already
   Mathlib. Use them.
2. **This is not transcendence of e.** Wiedijk #67 external
   only. Out of v1. `Transcendental.irrational` would make
   this theorem a corollary *if* transcendence landed — it has
   **not**. Do not take that path.
3. **This is not π irrational.** Genuine gap this run; Niven
   integral is a sink. Not this leftover. Not a third slot.
4. **This is not Liouville.** Already Mathlib; e is not a
   Liouville number.
5. **This is not `harmonic_not_int` / harmonic-series
   divergence / Wilson / Lucas / Wolstenholme.** Different
   theorems. Wolstenholme consumed #89 honest partial.
6. **This is not Descartes.** The recommended prime, different
   domain. Do not assign this first unless Director swaps.
7. **Do not re-prime** n-fold-inclusion-exclusion /
   wolstenholme-theorem / lovasz-local-lemma / korselt-carmichael /
   vosper / heron / euclid-euler / bipartite / moore / stirling /
   kst / pentagonal / sunflower / combinatorial-nullstellensatz /
   kruskal-katona / oddtown / cayley / mycielski / friendship /
   havel / menger / greedy / Brooks / Dilworth / Eulerian /
   König / Dirac / EKR.
8. **No `Archive.*` import.**
9. **Leave OPE-403 alone.**

## Proof sketch (classical, series remainder)

Level A: write `Real.exp 1 = ∑' 1/n!`. Partial sum `s n`.
Tail `∑_{k≥n+1} 1/k!` is positive and
`< 1/(n+1)! · (1 + 1/(n+2) + 1/(n+2)^2 + ⋯) ≤ 2/(n+1)!`
for `n ≥ 1`. **Not** labelled `irrational_exp_one`.

Level B: suppose `exp 1 = p / q` with `q > 0`. Choose
`n ≥ max q 1`. Then `n! * (exp 1 - s n)` is a positive
rational whose denominator divides nothing past `n` — actually
an integer (because `n! s n ∈ ℤ` and `n! p / q ∈ ℤ`) that is
strictly between 0 and 1. Contradiction. Cap two levels. No
transcendence, no π.

## Canonical source (pin in this STATEMENT)

Standard series proof (Fourier 1815 / textbook analysis:
Rudin *Principles* ch. 1 / Hardy). Compact form: Wikipedia
*e (mathematical constant)* — "e is irrational" via the
factorial remainder. Type pin: `Irrational (Real.exp 1)` using
`exp_eq_tsum_div`. Wiedijk #67 (e transcendental, external
Lean) is a **different** statement. Liouville, `harmonic_not_int`,
π irrational, Descartes, n-fold PIE, and Wolstenholme are
**different** statements, not this claim.

## Out of scope

- Transcendence of e or π (Wiedijk 67/53)
- π irrational (Niven integral sink)
- Niven cosine
- Liouville numbers (already Mathlib)
- Re-proving the exponential series
- Re-primes listed above
- Novelty / external claim
