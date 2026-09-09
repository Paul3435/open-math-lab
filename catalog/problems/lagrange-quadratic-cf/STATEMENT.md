# Lagrange theorem on continued fractions of quadratics — formalize-only

**id:** `lagrange-quadratic-cf`
**ticket:** OPE-1228 Formalist Level A (Scout OPE-1216 leftover slot #2; Director OPE-1227; parent OPE-1215)
**expected:** known-classical (Lagrange 1770: real quadratic irrationals have eventually periodic CF) — **no novelty claim**

## Why not classical / why formalize-only

Settled elementary continued-fraction
theory: a real number has an eventually
periodic simple continued fraction if and
only if it is a quadratic irrational
(root of an irreducible quadratic over
`ℚ`). Completely classical (Lagrange 1770;
Galois later characterised purely periodic
ones).

Not an open problem. Not a novelty claim.

**Not** `GenContFract.terminates_iff_rat`
(already TerminatesIffRat.lean L321;
rationals terminate — USE, do **not**
re-prove; do **not** cite as Lagrange).
**Not** Dirichlet approximation /
Legendre's theorem on convergents
(already DiophantineApproximation.lean
`exists_rat_abs_sub_le_and_den_le` /
`exists_rat_eq_convergent` — DIFFERENT
theorems; do **not** revive). **Not**
Beatty / Rayleigh (already Rayleigh.lean).
**Not** Pell / `QuadraticMap` / two-square
(already-in; residual-risk of *this* id).
**Not** Wantzel / `IsConstructible` /
cube-doubling (consumed #133; quadratic
*towers* are a different theorem; do
**not** revive Level B Wantzel). **Not**
quadratic reciprocity / Euler criterion
(already-in). **Not** Farey / Stern–Brocot
(consumed leftover).

Mathlib v4.10.0 already has the **continued
fraction / golden-ratio infra this theorem
needs**:

- `GenContFract` (`Algebra/ContinuedFractions/Basic.lean` L107;
  `h` head; `partDens` L129; `TerminatedAt` L133;
  `Terminates` L143)
- `GenContFract.of` (`Computation/Basic.lean` L182;
  `[⌊v⌋; b₀, b₁, …]` via `IntFractPair.seq1`)
- `of_partNum_eq_one` (Approximations.lean L158) —
  simple CF, **not** namesake
- `terminates_iff_rat` (TerminatesIffRat.lean L321) —
  **USE, not re-proved**
- `FloorRing ℝ` (`Data/Real/Archimedean.lean` L27)
- `goldenRatio` / `φ` (`GoldenRatio.lean` L30);
  `gold_sq` (`φ² = φ + 1` L79);
  `one_lt_gold` L96 / `gold_lt_two` L100
  (so `⌊φ⌋ = 1`)

There is **no** named Lagrange CF-periodicity
theorem, **no** `lagrange_quadratic` /
`eventuallyPeriodic` / `IsPeriodicCF` /
`quadratic_iff_periodic` anywhere under
`Mathlib/Algebra/ContinuedFractions`,
`Mathlib/NumberTheory`, `Archive/`, or
`ProofLab/` (this run → ZERO on those
names; `Function.Periodic` hits are Jacobi
theta / Hurwitz zeta, **wrong** periodicity).
Do **not** import `Archive.*`.

OPE-1200 shortlist is **CONSUMED** (#132+#133).
This is a **fresh** catalog-audit leftover
id, **not** a Wantzel leftover continuation,
**not** a circulant-det leftover, **not** a
Dirichlet/Legendre revival, **not** a prize
leftover, **not** a Formalist Level B
revival, **not** a third slot.

Mill NOW: finite Lagrange leftover beside
Petersen 1-factor (cubic bridgeless matching).
`GenContFract.of` + `φ` are waiting the same
way `minpoly` waited for Wantzel Level A.
**Not a rubber-stamp of `terminates_iff_rat`.**
**Not a rubber-stamp of Wantzel.**

Do **not** describe an attack as discovering
Lagrange's theorem. Do **not** expand into
Pell units / quadratic fields / Galois purely
periodic characterisation / Hurwitz
approximation as extra namesakes
(leftover-risk of *this* id).

## Pinned convention (exact)

**v1 Level A is the golden-ratio simple CF
on `ℝ`: head `⌊φ⌋ = 1` and the first two
partial denominators equal `1`, not labelled
Lagrange.** Count in `ℕ`. Optional extra:
`√2` head `1` and first partial denominator
`2`.

Suggested pin:

```text
-- Level A (not labelled Lagrange / Pell):
-- golden ratio CF head and first partDens.
-- Not labelled Lagrange.

open Real goldenRatio
open GenContFract

theorem goldenRatio_of_h :
    (of (φ : ℝ)).h = 1

theorem goldenRatio_partDen_zero :
    (of (φ : ℝ)).partDens.get? 0 = some 1

theorem goldenRatio_partDen_one :
    (of (φ : ℝ)).partDens.get? 1 = some 1

-- optional extra:
theorem sqrt_two_of_h :
    (of (√2 : ℝ)).h = 1

theorem sqrt_two_partDen_zero :
    (of (√2 : ℝ)).partDens.get? 0 = some 2

-- Level B namesake (quadratic ⇔ eventually periodic; residual OK)
def EventuallyPeriodic {α} (s : Stream'.Seq α) : Prop :=
  ∃ k p, 0 < p ∧ ∀ n, s.get? (k + n + p) = s.get? (k + n)

theorem lagrange_quadratic_cf (x : ℝ) (hx : Irrational x)
    {a b c : ℤ} (ha : a ≠ 0)
    (hquad : (a : ℝ) * x ^ 2 + b * x + c = 0) :
    EventuallyPeriodic (of x).partDens
```

`FloorRing ℝ` / `of` / `partDens` are
load-bearing. `gold_sq` (`φ² = φ+1`) is
load-bearing for the `φ` engine (do **not**
re-prove). `1 < φ < 2` is load-bearing for
the head.

**Level A may land only** `φ` head + first
partDens (optional `√2` extra), **not**
labelled Lagrange. Reuse Mathlib
`GenContFract.of` / `partDens` / `goldenRatio`
/ `gold_sq` / `terminates_iff_rat` —
**do not re-prove** termination-for-rationals
or Dirichlet/Legendre.

**Level B** is the namesake: irrational
quadratic ⇒ eventually periodic `partDens`
(converse residual OK). Do not sorry the
namesake; honest partial is allowed
(comment residual, not `sorry`). Pell units /
Galois purely-periodic / Hurwitz are residual.

## Landmines

1. **Do not re-prove** `terminates_iff_rat` /
   `GenContFract.of` / `gold_sq` /
   `one_lt_gold` / `FloorRing ℝ` /
   Dirichlet / Legendre convergents.
   Already Mathlib. Use them.
2. **This is not** Wantzel / `IsConstructible`
   (consumed #133). Quadratic *degree* vs
   quadratic *periodicity* are different.
   Do not revive Level B Wantzel.
3. **This is not** Beatty / Rayleigh /
   Farey / Stern–Brocot.
4. **This is not** `circulant-det` (#132) /
   `det_circulant` / DFT.
5. **This is not** `petersen-1-factor`
   (OPE-1216 prime) / Tutte / Hall.
6. **Do not** prove Pell / two-square /
   quadratic reciprocity as namesake.
7. **Do not** re-prime the consumed mill list.
8. **Leave OPE-403 alone.** Leave OPE-1195
   leftover status alone.
9. **Do not import `Archive.*`.**
10. Default no claim. No novelty claim.

## Out of v1

- Full Lagrange namesake (all real quadratics)
- Galois characterisation of purely periodic CF
- Pell fundamental unit / continued-fraction
  solution of `x² − dy² = ±1`
- Hurwitz `|α − p/q| < 1/(√5 q²)`
- Prize claims / Millennium / Beal
