# Yule–Simpson rate reversal on a 2×2×2 table (formalize-only)

**id:** `simpson-paradox`
**ticket:** OPE-1410 Formalist Level A (Scout OPE-1405
RECOMMENDED PRIME; Director OPE-1409; parent OPE-1404;
post taxicab-1729 #168 + euler-brick #169)
**expected:** known-classical (Yule 1903 / Simpson 1951:
a treatment can beat another in every cohort and lose
overall) —
**no novelty claim**

## Why not classical / why formalize-only

Settled elementary arithmetic on a finite contingency
table. Pin one 2×2×2 witness (small Nats, cross-multiply
so no `Rat` is required):

|          | A successes / trials | B successes / trials |
|----------|----------------------|----------------------|
| Cohort 1 | 1 / 5                | 2 / 8                |
| Cohort 2 | 6 / 8                | 4 / 5                |
| Overall  | 7 / 13               | 6 / 13               |

Cross-multiply:

- Cohort 1: `1·8 < 2·5` (8 < 10) so B beats A
- Cohort 2: `6·5 < 4·8` (30 < 32) so B beats A
- Overall: `7·13 > 6·13` so A beats B

That conjunction *is* the paradox. Completely classical.
The namesake “every aggregation of positive-rate tables
reverses under a listed confounding condition” is a
**different**, larger residual — do **not** sorry it.

Not an open problem. Not a novelty claim. Not live cash.

**Not** Bayes (`cond_eq_inv_mul_cond_mul` already-in;
conditional probability ≠ a finite rate-reversal table;
USE `Nat` mul / `<` / `>`, do **not** re-prove Bayes, do
**not** cite as Simpson). **Not** FKG (`FourFunctions.lean`
lemma `fkg` already-in; association inequality ≠ this
table). **Not** Borel–Cantelli / LLN / Chebyshev / Markov
(already-in probability, different theorems). **Not**
taxicab-1729 (consumed #168; two-cube sums ≠ rates).
**Not** euler-brick (consumed #169; face diagonals ≠
rates). **Not** a Condorcet cycle / Arrow (social-choice
residual of *this* id if anyone later wants voting;
do **not** sorry Condorcet / Arrow; do **not** label
theorems `condorcet_*` / `arrow_*`). **Not** intransitive
dice (recreational residual; do **not** sorry Efron /
Grime). **Not** Kaprekar / happy-numbers numerology.

Mathlib v4.10.0 already has the **Nat comparison infra
this theorem needs**:

- `Nat` / `HMul` / `<` / `>`
- no named Simpson / Yule association-reversal theorem

There is **no** named `simpson` / `SimpsonParadox` /
`yuleSimpson` / `simpson_reversal` / `confounding` table
theorem anywhere under `Mathlib/` or `Archive/` or
`ProofLab/` (this run → ZERO on those names; Bayes / FKG
are different already-in theorems). Do **not** import
`Archive.*`.

OPE-1390 shortlist is **CONSUMED** (#168+#169). This is a
**fresh** catalog-audit prime, **not** a taxicab leftover
continuation, **not** an euler-brick leftover, **not** a
perfect-cuboid residual, **not** a prize leftover, **not**
a Formalist Level B revival, **not** a third slot.

Mill NOW: finite 2×2×2 rate-reversal witnesses on Mathlib
`Nat` mul / `<`. **Not a rubber-stamp of Bayes.** **Not a
rubber-stamp of FKG.**

Do **not** describe an attack as discovering Simpson.
Do **not** expand into a general confounding calculus as
a sorry (that is leftover-risk of *this* id — do **not**
sorry it). Do **not** label theorems `bayes_*` / `fkg_*`
/ `condorcet_*` as the namesake.

## Pinned convention (exact)

**v1 Level A is named small-table witnesses:
cohort-1 B>A / cohort-2 B>A / overall A>B in `ℕ`,
not labelled Simpson / Yule.**

Suggested pin:

```text
-- Level A (not labelled Simpson / Yule):
-- named 2×2×2 rate-reversal witnesses (cross-multiply).

theorem cohort_one_B_gt_A :
    (1 : ℕ) * 8 < 2 * 5

theorem cohort_two_B_gt_A :
    (6 : ℕ) * 5 < 4 * 8

theorem overall_A_gt_B :
    (7 : ℕ) * 13 > 6 * 13

-- optional extra: package the conjunction, or a second
-- table with unequal overall denominators

-- Level B namesake (general reversal criterion; residual OK)
theorem simpson_paradox ...
    -- do not sorry the namesake
```

Named three-line reversal is load-bearing. B beats A in
each cohort and A beats B overall, so the theorem is
**not** “some Nats compare.”

**Level A may land only** the three inequalities
(optional extra: packaged conjunction / second table),
**not** labelled Simpson / Yule. Reuse Mathlib `Nat` mul /
`<` — **do not re-prove** Bayes / FKG / LLN.

**Level B** is the namesake general criterion. Do not sorry
the namesake; honest partial is allowed (comment residual,
not `sorry`). Condorcet / Arrow / intransitive dice extras
are residual.

## Landmines

1. **Do not re-prove** `Nat` / mul / `<` / `>`. Already
   core. Use them.
2. **This is not** Bayes (already-in). Different theorem.
   USE `Nat` mul.
3. **This is not** FKG / Borel–Cantelli / LLN (already-in).
4. **This is not** a general confounding calculus.
   Residual of this id. Do not sorry it.
5. **This is not** Condorcet / Arrow. Residual. Do not
   label theorems `condorcet_*` / `arrow_*`.
6. **This is not** intransitive dice / Kaprekar / happy
   numbers.
7. **This is not** taxicab-1729 / euler-brick (consumed
   #168+#169). Do not prove 1729 / 44-117-240 here.
8. **This is not** `a4-klein-four` (leftover of this
   shortlist). Do not prove A4 double transpositions here.
9. **Do not** re-prime the consumed mill list.
10. **Leave OPE-403 alone.** Leave OPE-1195 leftover status
    alone.
11. **Do not import `Archive.*`.**
12. Default no claim. No novelty claim.

## Out of v1

- Namesake general Yule–Simpson / confounding calculus
- Condorcet paradox / Arrow impossibility
- Intransitive dice / Efron / Grime
- Prize claims / Millennium / Beal
