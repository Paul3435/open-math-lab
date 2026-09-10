/-
Square-pyramidal numbers on named integers — Level A only
(`P(1) = 1²` / `P(24) = 70²`).
**Not labelled cannonball / Lucas.**

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 pin `a719ba5c3115` has `Nat` mul/div / `n * n` as
**infra**. ZERO named cannonball / `Cannonball` / `squarePyramid` /
`SquarePyramid` / `SquarePyramidal` / `pyramidalSquare` /
`square_pyramid` under `Mathlib/` or `Archive/` or `ProofLab/`.
Completing the Level A named pyramidal-square witnesses is the gap
this ticket lands. The Level B namesake `cannonball_square_pyramid`
(only `n = 1` and `n = 24`) is **out of this ticket** and is **not**
sorry-ed. Pell / square-triangular / uniqueness-for-all-n are
residual of this id.

Pin: `catalog/problems/cannonball-square-pyramid/STATEMENT.md`
(OPE-1321; Scout OPE-1310 leftover slot #2; Director OPE-1320).
Encoding: `squarePyramid n := n * (n + 1) * (2 * n + 1) / 6`
(Nat division; exact because `6 ∣ n(n+1)(2n+1)`). Zero `sorry`.
Do not import `Archive.*`.

This is **not** `Nat` mul/div / `n * n` — already Mathlib.
**USE, do not re-prove; do not cite as cannonball.**
This is **not** `sum_range_id` (`Algebra/BigOperators/Intervals.lean`
L249) — DIFFERENT triangular glue. Do **not** re-prove; do **not**
cite as cannonball.
This is **not** `sum_range_pow` (`NumberTheory/Bernoulli.lean` L280)
— DIFFERENT Faulhaber identity over `ℚ`. Do **not** re-prove; do
**not** cite as cannonball.
This is **not** `lucas_lehmer_sufficiency`
(`NumberTheory/LucasLehmer.lean` L476) — DIFFERENT already-in
Mersenne test (different Lucas). Do **not** cite as cannonball.
Do **not** label theorems `lucas_*`.
This is **not** `lucas_theorem` (`Nat/Choose/Lucas.lean` L97) —
DIFFERENT binomial congruence.
This is **not** `Nat.sum_four_squares` — DIFFERENT already-in
four-square theorem.
This is **not** Alcuin integer triangles
(`ProofLab/AlcuinIntegerTriangles.lean`, consumed #153).
This is **not** Proth primality (`ProofLab/ProthPrimality.lean`,
consumed #151) / Pépin / Pocklington / `euler_criterion`.
This is **not** Frucht graph Aut (`ProofLab/FruchtGraphAut.lean`,
consumed #150) / Cayley-graph / GRR / `Aut(Kₙ)≅Sₙ`.
This is **not** platonic-solids (`ProofLab/PlatonicSolids.lean`,
PR #147) / Euler polyhedron / Coxeter `H₃`.
This is **not** egyptian-fractions
(`ProofLab/EgyptianFractions.lean`, PR #148) / Erdős–Straus.
Do not re-prime the consumed mill. Leave OPE-403 alone.
Leave OPE-1195 alone.

v1 is the square-pyramidal closed form on named integers:
`P(1) = 1²` and `P(24) = 70²`, **not labelled cannonball / Lucas**.
The formula `n(n+1)(2n+1)/6` and `k * k` are load-bearing.

Level A: `1` / `24`. Optional extra: `P(2) = 5` is not a square.
**Not** labelled cannonball / Lucas.

Transcribed classical argument (Lucas 1875 / Watson 1918). Compact
form: Wikipedia *Cannonball problem*. Type pin: `squarePyramid n` /
`P(1)=1²` / `P(24)=70²`. Faulhaber `sum_range_pow` is a different
already-in `ℚ` identity. Lucas–Lehmer is a different already-in
Mersenne test. No novelty claim. Default no claim.
-/
import Mathlib.Tactic

set_option linter.unusedVariables false

namespace ProofLab.CannonballSquarePyramid

/-! ## Level A: P(1) = 1² and P(24) = 70²
(not labelled cannonball / Lucas) -/

/-- Square-pyramidal number `n(n+1)(2n+1)/6`. Encoding; **not**
labelled cannonball / Lucas. Does **not** re-prove `Nat` mul/div
or Faulhaber `sum_range_pow`. Nat division is exact because
`6 ∣ n(n+1)(2n+1)`. -/
def squarePyramid (n : ℕ) : ℕ :=
  n * (n + 1) * (2 * n + 1) / 6

/-- `P(1) = 1²`. Glue; **not** labelled cannonball / Lucas. -/
theorem cannonball_one : squarePyramid 1 = 1 * 1 := by
  rfl

/-- `P(24) = 70²`. Glue; **not** labelled cannonball / Lucas. -/
theorem cannonball_twenty_four : squarePyramid 24 = 70 * 70 := by
  rfl

/-- Optional extra: `P(2) = 5` is not a square.
Glue; **not** labelled cannonball / Lucas. -/
theorem cannonball_two_not_square (k : ℕ) : k * k ≠ squarePyramid 2 := by
  have hP : squarePyramid 2 = 5 := rfl
  rw [hP]
  intro hk
  have hle : k ≤ 2 := by
    by_contra hgt
    have hk3 : 3 ≤ k := Nat.succ_le_of_lt (lt_of_not_ge hgt)
    have : 9 ≤ k * k := Nat.mul_le_mul hk3 hk3
    omega
  interval_cases k <;> cases hk

/-
Residual (Level B, **out of this ticket**, not sorry-ed):
`cannonball_square_pyramid` — the only positive `n` with
`squarePyramid n` a square are `n = 1` and `n = 24`
(Lucas 1875 / Watson 1918). Do **not** sorry the namesake.
Pell / square-triangular / uniqueness-for-all-n remain residual
of this id; do **not** expand them as extra namesakes.
Do **not** prove Faulhaber / `sum_range_pow` as namesake /
`lucas_lehmer_sufficiency` as namesake / `lucas_theorem` as
namesake / `Nat.sum_four_squares` as namesake / Pell /
square-triangular / Alcuin leftover-revivals / Heronian / Pick /
Brahmagupta / `PythagoreanTriple.classification` as namesake /
frucht-graph-aut / Cayley-graph gadgets / GRR / `Aut(Kₙ)≅Sₙ` /
proth-primality / Pépin / Pocklington / `euler_criterion` /
platonic-solids / Euler polyhedron / Coxeter `H₃` /
egyptian-fractions / Erdős–Straus.
Leave OPE-403 alone. Leave OPE-1195 alone.
Do **not** label theorems `lucas_*`.
-/

end ProofLab.CannonballSquarePyramid
