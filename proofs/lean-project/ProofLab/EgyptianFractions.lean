/-
Egyptian fraction expansions — Level A only (`1 = 1/1` /
unit `1/n` / `3/4 = 1/2+1/4` / `2/3 = 1/2+1/6`, optional
`1 = 1/2+1/3+1/6`). **Not labelled Egyptian / Farey /
Kraft / harmonic.**

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 pin `a719ba5c3115` has `Rat` / `add_div` /
`one_div_mul_add_mul_one_div_eq_one_div_add_one_div` /
`inv_sub_inv` / `Finset.sum` as **infra**. ZERO named
Egyptian-fraction theorem / `egyptianFraction` /
`EgyptianFraction` / `unitFractionSum` / `sylvesterGreedy`
under `Mathlib/` or `Archive/` or `ProofLab/`. Completing
the Level A named-rational unit sums is the gap this ticket
lands. The Level B namesake `egyptian_fractions` (every
positive rational is a finite sum of distinct unit
fractions) is **out of this ticket** and is **not**
sorry-ed. Erdős–Straus / Sylvester sequence / greedy-length
bounds / harmonic-series-as-namesake are residual of this
id.

Pin: `catalog/problems/egyptian-fractions/STATEMENT.md`
(OPE-1289; Scout OPE-1278 leftover slot #2; Director
OPE-1288). Encoding: `Finset ℕ` denominators / `Rat`
`unitSum`. Zero `sorry`. Do not import `Archive.*`.

This is **not** `Rat` / `add_div` /
`one_div_mul_add_mul_one_div_eq_one_div_add_one_div` /
`inv_sub_inv` / `Finset.sum` — already Mathlib. **USE, do
not re-prove; do not cite as Egyptian.**
This is **not** Farey (`ProofLab/FareySequence.lean`,
PR #127) / Stern–Brocot / Calkin–Wilf / Ford circles —
DIFFERENT adjacent-fraction theorem (`bc−ad=1`). Do **not**
cite as Egyptian; do **not** revive Level B.
This is **not** Kraft (`ProofLab/KraftInequality.lean`,
PR #138) / McMillan / Huffman / Shannon — DIFFERENT
prefix-free-sum theorem.
This is **not** harmonic-series divergence
(`tendsto_sum_range_one_div_nat_succ_atTop`) — already-in.
Do **not** cite as Egyptian.
This is **not** Erdős–Straus `4/n = 1/x+1/y+1/z` — OPEN;
residual of this id; do **not** sorry it.
This is **not** Platonic solids
(`ProofLab/PlatonicSolids.lean`, PR #147) / Euler
polyhedron / Coxeter `H₃` / Kepler–Poinsot.
This is **not** Fine–Wilf (`ProofLab/FineWilf.lean`, PR #144)
/ Lyndon–Schützenberger.
This is **not** British flag (`ProofLab/BritishFlag.lean`,
PR #145) / Napoleon / Simson / Viviani.
Do not re-prime the consumed mill. Leave OPE-403 alone.
Leave OPE-1195 alone.

v1 is the unit-fraction-sum predicate on named rationals:
`1 = 1/1`, a pure unit `1/n`, `3/4 = 1/2 + 1/4`, and
`2/3 = 1/2 + 1/6`, **not labelled Egyptian**. Distinct
positive denominators are load-bearing. `Rat` addition of
`1/n` is load-bearing.

Level A: `1 = 1/1`. Pure unit `1/n`. `3/4 = 1/2 + 1/4`.
`2/3 = 1/2 + 1/6`. Optional extra: `1 = 1/2 + 1/3 + 1/6`.
**Not** labelled Egyptian.

Transcribed classical argument (Rhind papyrus practice;
Fibonacci, *Liber Abaci*, 1202; J. J. Sylvester, *On a
point in the theory of vulgar fractions*, Amer. J. Math. 3
(1880) 332–335). Compact form: Wikipedia *Egyptian
fraction*. Type pin: `Finset ℕ` denominators / `Rat`
`unitSum`. Farey is a different consumed adjacent-fraction
theorem. Kraft is a different consumed prefix-free-sum
theorem. Harmonic divergence is already-in. Erdős–Straus is
a different open residual. No novelty claim. Default no
claim.
-/
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

set_option linter.unusedVariables false

open Finset

namespace ProofLab.EgyptianFractions

/-! ## Encoding: Finset of denominators / unitSum
(not labelled Egyptian) -/

/-- Sum of unit fractions `∑ 1/n` over a finite set of
denominators. Uses Mathlib `Finset.sum` / `Rat`; does
**not** re-prove them. Encoding; **not** labelled Egyptian. -/
def unitSum (denoms : Finset ℕ) : ℚ :=
  denoms.sum fun n => (1 : ℚ) / n

/-- Distinct positive denominators, nonempty. Encoding of
the unit-fraction-sum predicate; **not** the namesake
`egyptian_fractions` and **not** labelled Egyptian. -/
def Egyptian (denoms : Finset ℕ) : Prop :=
  (∀ n ∈ denoms, 0 < n) ∧ denoms.Nonempty

/-! ## Level A: 1=1/1 / unit 1/n / 3/4=1/2+1/4 / 2/3=1/2+1/6
(not labelled Egyptian) -/

/-- `1 = 1/1`. Glue; **not** labelled Egyptian. Uses
`Finset.sum_singleton`; does **not** re-prove summation. -/
theorem egyptian_one :
    unitSum {1} = 1 := by
  unfold unitSum
  rw [sum_singleton]
  norm_num

/-- Pure unit `1/n`. Glue; **not** labelled Egyptian. Positive
denominator is load-bearing. Uses `Finset.sum_singleton`;
does **not** re-prove summation. -/
theorem egyptian_unit (n : ℕ) (hn : 0 < n) :
    unitSum {n} = (1 : ℚ) / n := by
  unfold unitSum
  rw [sum_singleton]

/-- `3/4 = 1/2 + 1/4`. Distinct positive denominators are
load-bearing. Uses `Finset.sum_insert` / `add_div` infra;
does **not** re-prove field arithmetic. Glue; **not**
labelled Egyptian. -/
theorem egyptian_three_four :
    unitSum {2, 4} = (3 : ℚ) / 4 := by
  have h24 : (2 : ℕ) ∉ ({4} : Finset ℕ) := by simp
  unfold unitSum
  rw [sum_insert h24, sum_singleton]
  norm_num

/-- `2/3 = 1/2 + 1/6`. Distinct positive denominators are
load-bearing. Uses `Finset.sum_insert`; does **not**
re-prove field arithmetic. Glue; **not** labelled Egyptian. -/
theorem egyptian_two_three :
    unitSum {2, 6} = (2 : ℚ) / 3 := by
  have h26 : (2 : ℕ) ∉ ({6} : Finset ℕ) := by simp
  unfold unitSum
  rw [sum_insert h26, sum_singleton]
  norm_num

/-- Optional extra telescoping: `1 = 1/2 + 1/3 + 1/6`.
Glue; **not** labelled Egyptian. Uses `Finset.sum_insert`;
does **not** re-prove `inv_sub_inv`. -/
theorem egyptian_one_half_third_sixth :
    unitSum {2, 3, 6} = 1 := by
  have h2 : (2 : ℕ) ∉ ({3, 6} : Finset ℕ) := by simp
  have h3 : (3 : ℕ) ∉ ({6} : Finset ℕ) := by simp
  unfold unitSum
  rw [sum_insert h2, sum_insert h3, sum_singleton]
  norm_num

/- Residual of this id (comment, **not** `sorry`):
Level B namesake `egyptian_fractions` — every positive
rational is a finite sum of distinct unit fractions
(Fibonacci–Sylvester greedy termination). Out of this
ticket. Do **not** prove `egyptian_fractions` / Erdős–Straus
`4/n = 1/x+1/y+1/z` / Sylvester sequence / greedy-length
bounds / harmonic-series divergence as namesake /
`tendsto_sum_range_one_div_nat_succ_atTop` as namesake /
Farey as namesake / Stern–Brocot / Calkin–Wilf / Ford
circles / Kraft / McMillan / Huffman / Shannon /
platonic-solids / Euler polyhedron / Coxeter `H₃` /
Kepler–Poinsot / `Rat` / `add_div` / `inv_sub_inv` /
`Finset.sum` / Fine–Wilf / Lyndon–Schützenberger /
british-flag / Napoleon / Simson / Viviani. -/

end ProofLab.EgyptianFractions
