# Combinatorial Nullstellensatz — Alon non-vanishing (formalize-only)

**id:** `combinatorial-nullstellensatz`
**ticket:** OPE-717 Scout leftover slot #2 (support OPE-716; post kruskal-katona #67 + oddtown #68)
**expected:** known-classical (Alon 1999) — **no novelty claim**

## Why not classical / why formalize-only

Settled polynomial-method lemma: if `f ∈ F[x₁,…,xₙ]` has
`deg_{xᵢ} f ≤ tᵢ` and the coefficient of `∏ xᵢ^{tᵢ}` is nonzero,
then `f` does not vanish on any box `S₁ × ⋯ × Sₙ` with `|Sᵢ| > tᵢ`.
Not an open problem.

Mathlib v4.10.0 already has the **algebra this theorem needs**:

- `MvPolynomial` (`Algebra/MvPolynomial/Basic.lean`) — `coeff`, `eval`
- `degreeOf` (`Algebra/MvPolynomial/Degrees.lean`)
- Hilbert Nullstellensatz (`RingTheory/Nullstellensatz.lean`) —
  **different** theorem (algebraic geometry / radical ideals)
- Chevalley–Warning (`FieldTheory/ChevalleyWarning.lean`) —
  **different** theorem (already upstream; finite-field *counting*)
- EGZ (`Combinatorics/Additive/ErdosGinzburgZiv.lean`) uses
  Chevalley–Warning, **not** this lemma

There is **no** combinatorial Nullstellensatz / Alon-CNS ident
anywhere under `Mathlib/` or `Archive/` (word-regexp this run → ZERO).
OPE-702 Scout **benched** this id because Kruskal–Katona had ready
Colex/Shadow/UV scaffolding. That competitor is now **consumed**
(PR #67). Univariate `n = 1` is Mathlib `Polynomial` root bounds
(Level A glue, **not** labelled CNS). This is **not** a re-prime of
Chevalley–Warning, EGZ, Oddtown, or Kruskal–Katona.

Do **not** describe an attack as discovering combinatorial Nullstellensatz.
Do **not** expand into Alon–Füredi, cap sets, or Chevalley–Warning
as a second id.

## Pinned convention (exact)

**Field pin:** `F` a field (Mathlib `Field`). Variables `Fin n`.
Polynomial `f : MvPolynomial (Fin n) F`. Degrees `t : Fin n → ℕ`.
Boxes `S : Fin n → Finset F`.

**Monomial pin:** the exponent vector is `t` viewed as
`Fin n →₀ ℕ` via `Finsupp.equivFunOnFinite.symm`. Do **not**
use `totalDegree` as a substitute for per-variable `degreeOf`.

```text
theorem combinatorial_nullstellensatz
    {F : Type*} [Field F] {n : ℕ}
    (f : MvPolynomial (Fin n) F) (t : Fin n → ℕ)
    (S : Fin n → Finset F)
    (hdeg : ∀ i, f.degreeOf i ≤ t i)
    (hcard : ∀ i, t i < (S i).card)
    (hcoeff : f.coeff (Finsupp.equivFunOnFinite.symm t) ≠ 0) :
    ∃ x : Fin n → F, (∀ i, x i ∈ S i) ∧ MvPolynomial.eval x f ≠ 0
```

**v1 is the non-vanishing form (Alon 1999, Theorem 1.2).** The
“combinatorial Nullstellensatz II” / explicit combinatorial
counting corollaries are stretches **out of v1**, not leftover
re-primes.

## Landmines

1. **This is not Hilbert’s Nullstellensatz.** Hilbert NS is
   already in `RingTheory/Nullstellensatz.lean`. Never cite it
   as this gap (OPE-25 hard stop).
2. **This is not Chevalley–Warning.** CW is already upstream
   (`char_dvd_card_solutions_of_sum_lt`). EGZ is a CW corollary.
   Do not relabel CW as combinatorial Nullstellensatz.
3. **Per-variable `degreeOf`, not `totalDegree`.** The monomial
   `∏ xᵢ^{tᵢ}` hypothesis is load-bearing.
4. **Univariate `n = 1` is not the namesake.** Mathlib
   `Polynomial` root-cardinality bounds may be *used* as Level A
   glue; do not call them combinatorial Nullstellensatz.
5. **Finite boxes in a field.** Not complex analysis, not
   `ℝ`-polynomials-as-functions without a field instance.
6. **Do not prove Alon–Füredi / cap-set / Chevalley–Warning
   in this id.**
7. **Do not re-prime** kruskal-katona / oddtown / sunflower-erdos-rado
   / cayley-trees / mycielski-triangle-free / havel-hakimi /
   menger-vertex / greedy / Brooks / Dilworth / Eulerian / König /
   Dirac.
8. **No `Archive.*` import.**
9. **Leave OPE-403 alone.**

## Proof sketch (classical, Alon 1999)

Level A: `n = 0` (nonzero constant); `n = 1` univariate — a
polynomial of degree `≤ t` with `coeff t ≠ 0` has at most `t`
roots, so misses `S` when `|S| > t`; `f = C c` constants.
Not labelled combinatorial Nullstellensatz.

Level B: namesake. Induction on `n`. Write `f` as a polynomial
in `xₙ` of degree `≤ tₙ` with MvPolynomial coefficients; reduce
modulo `∏_{a ∈ S n} (xₙ - a)` (degree `|S n| > tₙ` so the
remainder preserves the leading `xₙ^{tₙ}` coefficient); evaluate
in `xₙ` and apply IH in `n-1` variables.

Partial: **Level A** `n ≤ 1` + constants, zero sorry, not labelled
CNS. **Level B** namesake non-vanishing. Cap two levels. No
Chevalley–Warning, no Alon–Füredi.

## Lean gate (when attacked)

- Target module: `proofs/lean-project/ProofLab/CombinatorialNullstellensatz.lean`
- Reuse Mathlib `MvPolynomial.coeff` / `degreeOf` / `eval`.
  Do **not** re-prove Hilbert NS / Chevalley–Warning / EGZ.
- Zero `sorry`; `lake env lean` exit 0
- Default **no claim**
- Do not import `Archive.*`

## Canonical source

N. Alon, *Combinatorial Nullstellensatz*, Combinatorics, Probability
and Computing 8 (1999) 7–29, Theorem 1.2 (non-vanishing form).
Textbook pin: Alon–Spencer, *The Probabilistic Method*, polynomial
method / Nullstellensatz appendix. Type pin: Mathlib
`MvPolynomial (Fin n) F` + `degreeOf` + `coeff`. Hilbert NS,
Chevalley–Warning, and EGZ are **different** theorems, not this claim.
