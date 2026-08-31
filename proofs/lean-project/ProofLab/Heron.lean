/-
Heron's formula (formalize-only).

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 has `law_cos` /
`dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle`
(`Geometry/Euclidean/Triangle.lean`), `angle` / `angle_nonneg` / `angle_le_pi`,
`Real.sin` / `sin_eq_sqrt_one_sub_cos_sq` / `Real.sqrt`, and `dist` on a
Euclidean affine space. ZERO Heron / semiperimeter-area theorem under
`Mathlib/`. Completing the namesake is the gap.

Pin: `catalog/problems/heron-formula/STATEMENT.md` (OPE-799; Scout OPE-788
leftover slot #2; Director OPE-798). Encoding: Euclidean `dist` / `angle` /
`Real.sin` / `Real.sqrt`, matching Archive `Theorems100.heron` **without
importing it**. Zero `sorry`. Do not import `Archive.*`.

This is **not** the law of cosines (`law_cos` already Mathlib — used, not
re-proved).
This is **not** Sylvester–Gallai (Kelly closest-point sink; different statement).
This is **not** Pick's theorem (lattice `I + B/2 − 1`; encoding-from-scratch).
This is **not** de Bruijn–Erdős incidence (`HasLines.card_le` already Mathlib).
This is **not** five-colour / planar / Euler `V−E+F=2`.
This is **not** Vosper / inverse Cauchy–Davenport (consumed PR #82).
This is **not** Euclid–Euler / bipartite-odd-cycle / Moore / Stirling second
kind / pentagonal / KST / sunflower / CNS / Kruskal–Katona / Oddtown / Cayley /
Mycielski / Friendship / Havel / Menger / greedy / Brooks / Dilworth /
Eulerian / König / Dirac / EKR.
Leave OPE-403 alone.

Level A `cos_eq_sides` rearranges `law_cos` and `one_sub_cos_sq` rewrites
`1 − cos²` as a four-square difference. **Not** labelled Heron.
Level B namesake `heron` uses `sin γ = √(1−cos² γ)` on `γ ∈ [0, π]` and
algebra to `√(s(s−a)(s−b)(s−c))`. Degenerate collinear triangles are allowed
(`sin = 0`, radical `= 0`); `h1` / `h2` are load-bearing (`a, b > 0`).

Transcribed classical argument (Heron of Alexandria, *Metrica*; Wiedijk 100
Theorem 57). Archive `Wiedijk100Theorems/HeronsFormula.lean` is the *same*
statement and must **not** be imported.
-/
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Tactic

set_option linter.unusedVariables false

open Real EuclideanGeometry

namespace ProofLab.Heron

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P]

/-! ## Level A — cosine-rule rewrite (not labelled Heron) -/

/-- Cosine rule at `p2`: `cos γ = (a² + b² − c²) / (2ab)`.
Uses Mathlib `law_cos`; **not** a re-proof of the law of cosines.
**Not** labelled Heron. `h1` / `h2` are load-bearing (`a, b > 0`). -/
theorem cos_eq_sides {p1 p2 p3 : P} (h1 : p1 ≠ p2) (h2 : p3 ≠ p2) :
    let a := dist p1 p2
    let b := dist p3 p2
    let c := dist p1 p3
    Real.cos (angle p1 p2 p3) = (a * a + b * b - c * c) / (2 * a * b) := by
  intro a b c
  have ha : a ≠ 0 := (dist_pos.mpr h1).ne'
  have hb : b ≠ 0 := (dist_pos.mpr h2).ne'
  field_simp [mul_comm, law_cos p1 p2 p3]

/-- `1 − cos² γ` as a four-square difference of side lengths.
**Not** labelled Heron. -/
theorem one_sub_cos_sq {p1 p2 p3 : P} (h1 : p1 ≠ p2) (h2 : p3 ≠ p2) :
    let a := dist p1 p2
    let b := dist p3 p2
    let c := dist p1 p3
    let γ := angle p1 p2 p3
    1 - Real.cos γ ^ 2
      = ((2 * a * b) ^ 2 - (a * a + b * b - c * c) ^ 2) / (2 * a * b) ^ 2 := by
  intro a b c γ
  have ha : a ≠ 0 := (dist_pos.mpr h1).ne'
  have hb : b ≠ 0 := (dist_pos.mpr h2).ne'
  have hcos := cos_eq_sides h1 h2
  field_simp [hcos]

/-! ## Level B — namesake Heron -/

/-- **Heron's formula**: triangle area `½ a b sin γ` equals
`√(s(s−a)(s−b)(s−c))` with `s = (a+b+c)/2`.
`h1` / `h2` are load-bearing (`a, b > 0`). Degenerate collinear triangles
are allowed by the identities. -/
theorem heron {p1 p2 p3 : P} (h1 : p1 ≠ p2) (h2 : p3 ≠ p2) :
    let a := dist p1 p2
    let b := dist p3 p2
    let c := dist p1 p3
    let s := (a + b + c) / 2
    1 / 2 * a * b * Real.sin (angle p1 p2 p3)
      = Real.sqrt (s * (s - a) * (s - b) * (s - c)) := by
  intro a b c s
  let γ := angle p1 p2 p3
  have ha : a ≠ 0 := (dist_pos.mpr h1).ne'
  have hb : b ≠ 0 := (dist_pos.mpr h2).ne'
  have cos_rule := cos_eq_sides h1 h2
  let numerator := (2 * a * b) ^ 2 - (a * a + b * b - c * c) ^ 2
  let denominator := (2 * a * b) ^ 2
  have split_to_frac : (1 : ℝ) - cos γ ^ 2 = numerator / denominator :=
    one_sub_cos_sq h1 h2
  have numerator_nonneg : 0 ≤ numerator := by
    have frac_nonneg : 0 ≤ numerator / denominator :=
      (sub_nonneg.mpr (cos_sq_le_one γ)).trans_eq split_to_frac
    cases' div_nonneg_iff.mp frac_nonneg with h h
    · exact h.left
    · simpa [numerator, denominator, a, b, c, h1, h2] using
        le_antisymm h.right (sq_nonneg _)
  have ab2_nonneg : 0 ≤ 2 * a * b := by positivity
  calc
    1 / 2 * a * b * sin γ
        = 1 / 2 * a * b * (√ numerator / √ denominator) := by
          rw [sin_eq_sqrt_one_sub_cos_sq, split_to_frac,
            sqrt_div numerator_nonneg] <;>
            simp [γ, angle_nonneg, angle_le_pi]
    _ = 1 / 4 * √ ((2 * a * b) ^ 2 - (a * a + b * b - c * c) ^ 2) := by
          field_simp [numerator, denominator, ab2_nonneg]; ring
    _ = (1 : ℝ) / (4 : ℝ)
          * √ (s * (s - a) * (s - b) * (s - c) * (4 : ℝ) ^ 2) := by
          simp only [s]; ring_nf
    _ = √ (s * (s - a) * (s - b) * (s - c)) := by
          rw [sqrt_mul', sqrt_sq, div_mul_eq_mul_div, one_mul,
            mul_div_cancel_right₀] <;> norm_num

end ProofLab.Heron
