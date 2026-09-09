/-
Lagrange quadratic continued fractions — Level A only (golden-ratio
CF head and first two partial denominators; optional √2 extra).
**Not labelled Lagrange / Pell.**

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 pin `a719ba5c3115` has `GenContFract` / `partDens` /
`GenContFract.of` / `terminates_iff_rat` / `FloorRing ℝ` /
`goldenRatio` / `gold_sq` / `one_lt_gold` / `gold_lt_two` as **infra**.
ZERO named Lagrange CF-periodicity / `lagrange_quadratic` /
`eventuallyPeriodic` / `IsPeriodicCF` / `quadratic_iff_periodic`
under `Mathlib/` or `Archive/` or `ProofLab/`. Completing the Level A
φ head / first two `partDens` glue is the gap this ticket lands. The
Level B namesake `lagrange_quadratic_cf` (irrational quadratic ⇒
eventually periodic `partDens`) is **out of this ticket** and is
**not** sorry-ed. Pell / Galois purely-periodic / Hurwitz extras are
residual of this id.

Pin: `catalog/problems/lagrange-quadratic-cf/STATEMENT.md`
(OPE-1228; Scout OPE-1216 leftover slot #2; Director OPE-1227).
Encoding: Mathlib `GenContFract.of` / `partDens` / `goldenRatio` on
`ℝ`. Zero `sorry`. Do not import `Archive.*`.

This is **not** `terminates_iff_rat` (TerminatesIffRat.lean L321) —
already Mathlib; rationals terminate. **USE, do not re-prove; do not
cite as Lagrange.**
This is **not** Dirichlet / Legendre convergents
(`exists_rat_abs_sub_le_and_den_le` / `exists_rat_eq_convergent` in
DiophantineApproximation.lean) — different already-in CF theorems.
This is **not** Beatty / Rayleigh (already Rayleigh.lean).
This is **not** Wantzel / `IsConstructible`
(`ProofLab/WantzelConstructible.lean`, PR #133).
This is **not** circulant-det (`ProofLab/CirculantDet.lean`, PR #132).
This is **not** Petersen 1-factor (`ProofLab/PetersenOneFactor.lean`,
PR #135).
Do not re-prime the consumed mill. Leave OPE-403 alone.
Leave OPE-1195 alone.

v1 is the golden-ratio simple CF on `ℝ`: head `⌊φ⌋ = 1` and the
first two partial denominators equal `1`, **not labelled Lagrange**.
Count in `ℕ`. Optional extra: `√2` head `1` and first partial
denominator `2`. `FloorRing ℝ` / `of` / `partDens` are load-bearing.
`gold_sq` (`φ² = φ+1`) is load-bearing for the φ engine.
`1 < φ < 2` is load-bearing for the head.

Level A: `1 < φ < 2` so `⌊φ⌋ = 1`, hence `(of φ).h = 1`. `gold_sq`
gives `φ = 1 + 1/φ`, so the simple-CF engine repeats partial
denominator `1`. Optional `√2`: `1 < √2 < 2` so head `1`, first
`partDen` `2`. **Not** labelled Lagrange.

Transcribed classical argument (Lagrange 1770). Compact form:
Wikipedia *Lagrange's theorem (continued fraction)*. Type pin:
`GenContFract.of` / `partDens` / `goldenRatio`. `terminates_iff_rat`
is a different already-in theorem. Wantzel is a different consumed
quadratic-degree theorem. No novelty claim. Default no claim.
-/
import Mathlib.Algebra.ContinuedFractions.Computation.Translations
import Mathlib.Data.Real.GoldenRatio
import Mathlib.Tactic

set_option linter.unusedVariables false

open Real goldenRatio
open GenContFract
open scoped goldenRatio

noncomputable section

namespace ProofLab.LagrangeQuadraticCf

/-! ## Level A: φ head = 1 / first two partDens = 1 / optional √2
(not labelled Lagrange / Pell) -/

/-- `1 < φ < 2`, so the floor is `1`. Uses `one_lt_gold` /
`gold_lt_two`; does **not** re-prove them. Glue; **not** labelled
Lagrange. -/
theorem goldenRatio_floor : ⌊(φ : ℝ)⌋ = 1 := by
  refine Int.floor_eq_on_Ico 1 φ ⟨?_, ?_⟩
  · exact_mod_cast one_lt_gold.le
  · have : ((1 : ℤ) : ℝ) + 1 = 2 := by norm_num
    rw [this]
    exact gold_lt_two

/-- Head of the simple CF of `φ` is `1`. Uses `of_h_eq_floor`;
does **not** re-prove CF construction. Glue; **not** labelled
Lagrange. -/
theorem goldenRatio_of_h : (GenContFract.of (φ : ℝ)).h = 1 := by
  simp [of_h_eq_floor, goldenRatio_floor]

/-- From `gold_sq`: `φ² = φ + 1` and `φ ≠ 0` give `φ⁻¹ = φ - 1`.
Uses `gold_sq` / `gold_ne_zero`; does **not** re-prove them. -/
theorem goldenRatio_inv_eq_sub_one : (φ : ℝ)⁻¹ = φ - 1 := by
  refine inv_eq_of_mul_eq_one_right ?_
  calc
    (φ : ℝ) * (φ - 1) = φ ^ 2 - φ := by ring
    _ = φ + 1 - φ := by rw [gold_sq]
    _ = 1 := by ring

/-- Fractional part of `φ` is `φ - 1 = φ⁻¹`. -/
theorem goldenRatio_fract : Int.fract (φ : ℝ) = (φ : ℝ)⁻¹ := by
  rw [← Int.self_sub_floor, goldenRatio_floor, Int.cast_one,
    goldenRatio_inv_eq_sub_one]

theorem goldenRatio_fract_ne_zero : Int.fract (φ : ℝ) ≠ 0 := by
  rw [goldenRatio_fract]
  exact inv_ne_zero gold_ne_zero

theorem goldenRatio_fract_inv : (Int.fract (φ : ℝ))⁻¹ = φ := by
  rw [goldenRatio_fract, inv_inv]

/-- First partial denominator of `φ` is `1`. Uses `of_s_head` /
`partDen_eq_s_b`; does **not** re-prove CF construction. Glue;
**not** labelled Lagrange. -/
theorem goldenRatio_partDen_zero :
    (GenContFract.of (φ : ℝ)).partDens.get? 0 = some 1 := by
  have hs : (GenContFract.of (φ : ℝ)).s.get? 0 =
      some ⟨1, ⌊(Int.fract (φ : ℝ))⁻¹⌋⟩ :=
    of_s_head goldenRatio_fract_ne_zero
  rw [partDen_eq_s_b hs, goldenRatio_fract_inv, goldenRatio_floor]
  simp

/-- Second partial denominator of `φ` is `1`. Uses `of_s_succ`
together with the first-term identity; the engine repeats because
`(fract φ)⁻¹ = φ`. Glue; **not** labelled Lagrange. -/
theorem goldenRatio_partDen_one :
    (GenContFract.of (φ : ℝ)).partDens.get? 1 = some 1 := by
  have hs : (GenContFract.of (φ : ℝ)).s.get? 1 =
      (GenContFract.of (φ : ℝ)).s.get? 0 := by
    rw [of_s_succ (φ : ℝ) 0, goldenRatio_fract_inv]
  obtain ⟨gp, hgp, hb⟩ := exists_s_b_of_partDen goldenRatio_partDen_zero
  rw [partDen_eq_s_b (hs.trans hgp), hb]

/-! ### Optional extra: √2 head 1 / first partDen 2 -/

theorem one_lt_sqrt_two : (1 : ℝ) < √2 :=
  (lt_sqrt (by norm_num)).mpr (by norm_num)

theorem sqrt_two_lt_two : √(2 : ℝ) < 2 :=
  (sqrt_lt' (by norm_num)).mpr (by norm_num)

theorem sqrt_two_floor : ⌊(√2 : ℝ)⌋ = 1 := by
  refine Int.floor_eq_on_Ico 1 (√2) ⟨?_, ?_⟩
  · exact_mod_cast one_lt_sqrt_two.le
  · have : ((1 : ℤ) : ℝ) + 1 = 2 := by norm_num
    rw [this]
    exact sqrt_two_lt_two

/-- Head of the simple CF of `√2` is `1`. Glue; **not** labelled
Lagrange. -/
theorem sqrt_two_of_h : (GenContFract.of (√2 : ℝ)).h = 1 := by
  simp [of_h_eq_floor, sqrt_two_floor]

theorem sqrt_two_fract : Int.fract (√2 : ℝ) = √2 - 1 := by
  rw [← Int.self_sub_floor, sqrt_two_floor, Int.cast_one]

theorem sqrt_two_fract_ne_zero : Int.fract (√2 : ℝ) ≠ 0 := by
  rw [sqrt_two_fract]
  linarith [one_lt_sqrt_two]

/-- `(√2 - 1)⁻¹ = √2 + 1` by rationalising. -/
theorem sqrt_two_sub_one_inv : (√(2 : ℝ) - 1)⁻¹ = √2 + 1 := by
  refine inv_eq_of_mul_eq_one_right ?_
  calc
    (√(2 : ℝ) - 1) * (√2 + 1) = (√2) ^ 2 - 1 := by ring
    _ = 2 - 1 := by rw [Real.sq_sqrt (by norm_num)]
    _ = 1 := by norm_num

theorem sqrt_two_fract_inv : (Int.fract (√2 : ℝ))⁻¹ = √2 + 1 := by
  rw [sqrt_two_fract, sqrt_two_sub_one_inv]

/-- First partial denominator of `√2` is `2`. Glue; **not** labelled
Lagrange. -/
theorem sqrt_two_partDen_zero :
    (GenContFract.of (√2 : ℝ)).partDens.get? 0 = some 2 := by
  have hs : (GenContFract.of (√2 : ℝ)).s.get? 0 =
      some ⟨1, ⌊(Int.fract (√2 : ℝ))⁻¹⌋⟩ :=
    of_s_head sqrt_two_fract_ne_zero
  have hfl : ⌊√(2 : ℝ) + 1⌋ = 2 := by
    have : √(2 : ℝ) + 1 = √2 + (1 : ℤ) := by simp
    rw [this, Int.floor_add_int, sqrt_two_floor]
    norm_num
  rw [partDen_eq_s_b hs, sqrt_two_fract_inv, hfl]
  simp

/- Residual of this id (comment, **not** `sorry`):
Level B namesake `lagrange_quadratic_cf` — irrational quadratic ⇒
eventually periodic `partDens`. Pell units / Galois purely-periodic
characterisation / Hurwitz `|α − p/q| < 1/(√5 q²)` are residual, not
extra namesakes. Out of this ticket. Do **not** prove
`terminates_iff_rat` as namesake / Dirichlet / Legendre convergents /
Beatty / Rayleigh / Wantzel / IsConstructible / circulant-det /
petersen-1-factor. -/

end ProofLab.LagrangeQuadraticCf
