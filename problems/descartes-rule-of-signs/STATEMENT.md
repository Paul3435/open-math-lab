# Descartes' rule of signs (formalize-only)

**id:** `descartes-rule-of-signs`
**ticket:** OPE-838 Scout RECOMMENDED PRIME (support OPE-837; post n-fold PIE #88 + Wolstenholme #89)
**expected:** known-classical (Descartes 1637; Wiedijk 100 #100) — **no novelty claim**

## Why not classical / why formalize-only

Settled real-polynomial root bound: the number of positive
real roots of a real polynomial is at most the number of
sign changes in its coefficient sequence (zeros skipped).

Not an open problem. Not a novelty claim.

Mathlib v4.10.0 already has the **algebra this theorem needs**:

- `Polynomial` / `coeff` / `natDegree` / `eval` / `IsRoot`
  (`Algebra/Polynomial/Basic.lean`, `Roots.lean`)
- `Polynomial.roots` as a `Multiset` (with multiplicity)
- `Real.sign` (`Data/Real/Sign.lean`)
- binomial theorem `add_pow`, Vandermonde, Cramer's rule —
  **already upstream. Never cite as this gap.**
- Rational root theorem
  (`RingTheory/Polynomial/RationalRoot.lean`) — **already
  upstream. Different theorem.**
- Eisenstein criterion
  (`RingTheory/EisensteinCriterion.lean`) — **already
  upstream. Different theorem.**
- Gauss's lemma (`RingTheory/Polynomial/GaussLemma.lean`) —
  **already upstream.**
- Cyclotomic irreducibility (`cyclotomic.irreducible`) —
  **already upstream.**
- FTA `Complex.exists_root` — **already upstream.**
- Rolle / MVT `exists_deriv_eq_slope` — **already upstream.**
- Chebyshev polynomials `Polynomial.Chebyshev.T` +
  `T_real_cos` (`eval (cos θ) = cos (n*θ)`) — **defs +
  multiple-angle identity, not Descartes.**

There is **no** Descartes rule of signs, **no**
`signChanges`, and **no** named positive-root / coefficient-sign
bound anywhere under `Mathlib/` or `Archive/` (word-regexp
`descartes` / `rule_of_signs` / `signChange` / `sign_changes`
this run → ZERO in `Mathlib/` + `Archive/`). Wiedijk 100.yaml
#100 lists only an **external** github link (Timeroot
`lean-descartes-signs`) — **not** a Mathlib `decl`. Do **not**
treat that external file as upstream. Do **not** import
`Archive.*`.

OPE-821 considered-not-slotted did **not** slot this id (the
funded pair was n-fold PIE + Wolstenholme). Both of those are
now **CONSUMED** (#88 namesake landed; #89 honest Level A
partial). This is a **fresh** candidate, **not** a PIE leftover,
**not** a Wolstenholme leftover, **not** a third slot.

Mill NOW: real-polynomial algebra after an enumerative-combinatorics
prime (n-fold PIE, **CONSUMED** #88) and an NT leftover
(Wolstenholme, **CONSUMED** #89). Same Wiedijk-100-with-no-Mathlib-decl
pattern as PIE #96 → Descartes #100. **Not a rubber-stamp.**

Do **not** describe an attack as discovering Descartes. Do
**not** expand into Budan–Fourier / Sturm sequences /
Eneström–Kakeya / Gauss–Lucas (same mill, out of v1). Do
**not** prove Niven cosine (Chebyshev mill-duplicate). Do
**not** prove e / π transcendental (Wiedijk 67/53 sinks).

## Pinned convention (exact)

**v1 is the inequality** (positive real roots, counted with
multiplicity via `Polynomial.roots`, bounded by the number of
coefficient sign changes). The even-difference strengthening
is **not** required for the namesake.

Zeros in the coefficient list are **skipped** (classical:
only consecutive *nonzero* coefficients contribute a change).
Leading/trailing zeros do not count. The zero polynomial is
excluded (`p ≠ 0`).

Suggested pin:

```text
/-- Number of sign changes in nonzero coefficients of `p`,
from degree 0 up, zeros skipped. -/
def signChanges (p : ℝ[X]) : ℕ := ...

theorem descartes_rule_of_signs {p : ℝ[X]} (hp : p ≠ 0) :
    ((p.roots.filter (fun x => 0 < x)).card) ≤ signChanges p
```

`Polynomial.roots` is a `Multiset`, so the left side counts
**with multiplicity**. That is load-bearing for the classical
statement. An equivalent distinct-root inequality (toFinset)
is **weaker** and may land as glue, **not** labelled Descartes.

**Level A may land only the zero-change vanishing**, not
labelled Descartes:

```text
-- all nonzero coefficients have the same sign
(∀ i j, p.coeff i ≠ 0 → p.coeff j ≠ 0 → 0 ≤ p.coeff i * p.coeff j)
→ ∀ x, 0 < x → ¬ p.IsRoot x
```

via `eval` positivity on `(0, ∞)` (or the all-nonpositive
case). **Level B** is the namesake `descartes_rule_of_signs`
by grouping / Rolle / factoring out a positive root and
inducting on `natDegree`.

Negative roots of `p` are positive roots of `p.comp (-X)` —
a corollary, not a second namesake.

## Landmines

1. **Do not re-prove FTA / Rolle / MVT / binomial /
   Vandermonde / rational-root / Eisenstein / Gauss lemma /
   cyclotomic irreducibility.** Already Mathlib. Use them.
2. **This is not Chebyshev `T_n(cos θ) = cos(nθ)`.** Defs +
   identity already upstream. Niven cosine is a different
   theorem (not this leftover).
3. **This is not Budan–Fourier / Sturm / Eneström–Kakeya /
   Gauss–Lucas.** Out of v1.
4. **This is not n-fold PIE / Bonferroni.** Consumed #88.
   Different domain.
5. **This is not Wolstenholme / Wilson / Lucas.** Consumed #89
   honest partial / already Mathlib. Different domain.
6. **Do not prove e / π transcendental.** Wiedijk 67 is
   external Lean; Wiedijk 53 has no decl. Sinks. The leftover
   slot is `e-irrational` (irrational, **not** transcendental).
7. **Do not re-prime** n-fold-inclusion-exclusion /
   wolstenholme-theorem / lovasz-local-lemma / korselt-carmichael /
   vosper / heron / euclid-euler / bipartite / moore / stirling /
   kst / pentagonal / sunflower / combinatorial-nullstellensatz /
   kruskal-katona / oddtown / cayley / mycielski / friendship /
   havel / menger / greedy / Brooks / Dilworth / Eulerian /
   König / Dirac / EKR.
8. **No `Archive.*` import.**
9. **Leave OPE-403 alone.**

## Proof sketch (classical, Descartes)

Level A: if every nonzero coefficient is ≥ 0, then for `x > 0`
every term `coeff i * x^i` is ≥ 0 and the leading term is > 0,
so `eval x p > 0`. Dual for all ≤ 0. **Not** labelled Descartes.

Level B: write `p(x) = (x − a) q(x)` for a positive root `a`
(or induct after stripping one positive root). Sign changes of
`p` are at least one more than those of `q` (Descartes'
grouping / continuous variation). Cap two levels. No Sturm
chain, no Budan–Fourier.

## Canonical source (pin in this STATEMENT)

Wiedijk 100 theorems, #100 "Descartes Rule of Signs". Compact
form: Wikipedia *Descartes' rule of signs* — the number of
positive real roots, counted with multiplicity, is at most the
number of sign changes in the coefficient list (zeros skipped),
and the difference is even. **v1 pins the inequality only.**
Type pin: `ℝ[X]`, `Polynomial.roots` filter `0 < ·`, `signChanges`
on nonzero `coeff`. Rational-root / Eisenstein / Gauss lemma /
FTA / Rolle / Chebyshev `T_n` / n-fold PIE / Wolstenholme are
**different** statements, not this claim. Timeroot's external
Lean file is **not** Mathlib.

## Out of scope

- Budan–Fourier / Sturm sequences / Eneström–Kakeya / Gauss–Lucas
- Niven cosine / π-irrational Niven integral
- e / π transcendental
- Re-proving FTA / Rolle / rational-root / Eisenstein
- Re-primes listed above
- Novelty / external claim
