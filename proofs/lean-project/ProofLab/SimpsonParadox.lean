/-
Named 2×2×2 rate-reversal witnesses — Level A only
(`1·8 < 2·5` / `6·5 < 4·8` / `7·13 > 6·13`).
**Not labelled Simpson / Yule.**

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 pin `a719ba5c3115` has `Nat` / `HMul` / `<` / `>`
as **infra**. ZERO named `simpson` / `SimpsonParadox` /
`yuleSimpson` / `simpson_reversal` / Yule–Simpson theorem
under `Mathlib/` or `Archive/` or `ProofLab/` (this run).
Completing the Level A named three-line reversal is the gap
this ticket lands. The Level B namesake `simpson_paradox`
(general confounding / reversal criterion) is **out of this
ticket** and is **not** sorry-ed. Condorcet / Arrow /
intransitive dice extras are residual of this id — **out of
v1**, not sorry-ed. Do **not** label theorems `simpson_paradox`
/ `yule_*` / `bayes_*` / `fkg_*` / `condorcet_*` / `arrow_*`
as the namesake. Do **not** define the namesake via a general
confounding calculus.

Pin: `catalog/problems/simpson-paradox/STATEMENT.md`
(OPE-1410; Scout OPE-1405 RECOMMENDED PRIME; Director OPE-1409).
Encoding: named cross-multiply witnesses via Mathlib `Nat` mul /
`<` / `>`. Zero `sorry`. Do not import `Archive.*`.

This is **not** `Nat` / `HMul` / `<` / `>` — already Mathlib.
**USE, do not re-prove; do not cite as this table.**
This is **not** `cond_eq_inv_mul_cond_mul`
(`Probability/ConditionalProbability.lean` L192) — already-in
Bayes; different identity. USE `Nat` mul / `<`; do **not**
re-prove; do **not** cite as this table.
This is **not** lemma `fkg`
(`Combinatorics/SetFamily/FourFunctions.lean` L336) —
already-in association inequality; different theorem.
This is **not** Borel–Cantelli / LLN / Chebyshev / Markov
(already-in probability, different theorems).
This is **not** taxicab-1729 (`ProofLab/Taxicab1729.lean`,
consumed #168). Cubes ≠ rates.
This is **not** euler-brick (`ProofLab/EulerBrick.lean`,
consumed #169). Face diagonals ≠ rates.
This is **not** D8 ≇ Q8 (`ProofLab/D8NeQ8.lean`, consumed #166).
This is **not** ℤ[√-5] not UFD (`ProofLab/Zsqrt5NotUfd.lean`,
consumed #165).
This is **not** a4-klein-four (leftover of this shortlist,
unassigned this tick). Do **not** prove A4 double
transpositions here.
Do not re-prime the consumed mill. Leave OPE-403 alone.
Leave OPE-1195 alone.

v1 is named three-line reversal: B beats A in each cohort
and A beats B overall, **not labelled Simpson / Yule**.
Named three-line reversal is load-bearing (so Level A is
**not** “some Nats compare”).

Level A: `cohort_one_B_gt_A` / `cohort_two_B_gt_A` /
`overall_A_gt_B`. Optional extra: packaged conjunction.
**Not** labelled Simpson / Yule.

Transcribed classical argument (Yule 1903 / Simpson 1951
2×2×2 table: rates 1/5 vs 2/8 and 6/8 vs 4/5 reverse
overall 7/13 vs 6/13). Compact form: Wikipedia *Simpson's
paradox*. Type pin: `Nat` mul / `<` / `>`. Bayes / FKG
are different already-in theorems. Taxicab-1729 /
euler-brick are different consumed mills. No novelty claim.
Default no claim.

Level B namesake OUT of this ticket (do not sorry):
-- theorem simpson_paradox ...
--     -- do not sorry the namesake
-/
import Mathlib.Tactic

namespace ProofLab.SimpsonParadox

/-! ## Level A: 1·8<2·5 / 6·5<4·8 / 7·13>6·13
(not labelled Simpson / Yule) -/

/-- Cohort 1: `1/5` vs `2/8`. Cross-multiply `1·8 < 2·5`
so B beats A. Glue: Mathlib `Nat` mul / `<`.
Not labelled Simpson / Yule.
Load-bearing named cohort of the same 2×2×2 table. -/
theorem cohort_one_B_gt_A : (1 : ℕ) * 8 < 2 * 5 := by
  decide

/-- Cohort 2: `6/8` vs `4/5`. Cross-multiply `6·5 < 4·8`
so B beats A. Glue: Mathlib `Nat` mul / `<`.
Not labelled Simpson / Yule.
Load-bearing named cohort of the same 2×2×2 table. -/
theorem cohort_two_B_gt_A : (6 : ℕ) * 5 < 4 * 8 := by
  decide

/-- Overall: `7/13` vs `6/13`. Cross-multiply `7·13 > 6·13`
so A beats B. Glue: Mathlib `Nat` mul / `>`.
Not labelled Simpson / Yule.
Load-bearing named overall of the same 2×2×2 table. -/
theorem overall_A_gt_B : (7 : ℕ) * 13 > 6 * 13 := by
  decide

/-- Optional extra: package the conjunction.
B beats A in each cohort and A beats B overall.
Glue; **not** labelled Simpson / Yule.
Does **not** sorry a general confounding criterion
(Level B residual, out of this ticket). -/
theorem rate_reversal :
    (1 : ℕ) * 8 < 2 * 5 ∧ (6 : ℕ) * 5 < 4 * 8 ∧ (7 : ℕ) * 13 > 6 * 13 :=
  ⟨cohort_one_B_gt_A, cohort_two_B_gt_A, overall_A_gt_B⟩

/-
Residual (Level B, **out of this ticket**, not sorry-ed):
`simpson_paradox` — general Yule–Simpson / confounding
reversal criterion. Do **not** sorry the namesake.
Condorcet / Arrow / intransitive dice (Efron / Grime) are
residual of this id, **out of v1**; do **not** sorry them.
Do **not** prove `simpson_paradox` as namesake / general
confounding calculus / Bayes as namesake / FKG as namesake
/ `condorcet_*` / `arrow_*` / intransitive dice / Efron /
Grime / a4-klein-four / `Equiv.swap 0 1 * swap 2 3` even in
A4 / `V ⊴ A₄` / A4 no subgroup order 6 / `isSimpleGroup_five`
as namesake / `IsKleinFour` as namesake / taxicab-1729 /
`1³+12³=1729` / euler-brick / 44-117-240 brick / perfect
cuboid / zsqrt5-not-ufd leftover-revivals /
UniqueFactorizationMonoid / d8-ne-q8 leftover-revivals /
`DihedralGroup 4 ≃* QuaternionGroup 2` / myhill-nerode /
Kleene leftover-revivals / gray-code / hypercube Hamiltonian
/ krenn-gu / hou-zeng-pfc / sun-135.
Leave OPE-403 alone. Leave OPE-1195 alone.
Do **not** label theorems `simpson_paradox` / `yule_*` /
`bayes_*` / `fkg_*` / `condorcet_*` / `arrow_*`.
-/

end ProofLab.SimpsonParadox
