/-
Hadamard determinant inequality — Level A only (n empty / 1 / n=2 /
pairwise-orthogonal rows). **Not labelled Hadamard.**

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 has `Matrix.det` / `det_apply` / `detRowAlternating`
and ZERO named Hadamard determinant inequality / `hadamard_det` /
`HadamardInequality` / `det_le_prod`. Completing the Level A n=0/1 /
n=2 / orthogonal-rows glue is the gap this ticket lands. The Level B
namesake `hadamard_det` (Gram `G = A * Aᵀ`, `(det A)^2 = det G ≤ ∏
diagonal`, AM-GM on eigenvalues / induction) is **out of this ticket**
and is **not** sorry-ed. Complex conjugate-transpose / column-norm /
Fischer / Minkowski / volume-of-parallelotope extras are residual.

Pin: `catalog/problems/hadamard-det/STATEMENT.md` (OPE-1120; Scout
OPE-1110 leftover slot #2; Director OPE-1119). Encoding: Mathlib
`Matrix.det` + Euclidean `ℓ²` row norm. Zero `sorry`. Do not import
`Archive.*`.

This is **not** `Matrix.det_le` (`AbsoluteValue.lean` — weaker
entrywise `n! x^n` bound; **USE nothing as a namesake**, do **not**
re-prove, do **not** cite as Hadamard). This is **not** Gershgorin /
Levy–Desplanques (`Gershgorin.lean` `eigenvalue_mem_ball` /
`det_ne_zero_of_sum_row_lt_diag`). This is **not** the Hadamard
*product* (`Data/Matrix/Hadamard.lean`). This is **not** Hadamard
three-lines (`Analysis/Complex/Hadamard.lean`). This is **not**
Vandermonde det / Cauchy–Binet / Kirchhoff. This is **not**
schwartz-zippel (consumed #114; do not revive Level B). This is
**not** Ore Level B / `konig_edge_chromatic` / AES Level B /
ostrowski-q Level B / frobenius-real-division Level B /
noether-normalization Level B / krenn-gu / hou-zeng-pfc / sun-135.
Do not re-prime the consumed mill. Leave OPE-403 alone.

v1 is the real square Euclidean-row form only. `Fintype n` is
load-bearing. Real coefficients are load-bearing (complex needs
conjugate transpose; out of v1). Euclidean `ℓ²` row norm is
load-bearing (entrywise `n! x^n` is the already-in `det_le`, a
**different** theorem).

Level A: `n=0/1` trivial (`det` of empty is `1`; `det` of `1×1` is
the entry). `n=2` is an explicit square-root inequality. If rows are
pairwise orthogonal, `A * Aᵀ` is diagonal with the squared row
norms, so `|det A| = ∏ rowNorm`. **Not** labelled Hadamard.

Transcribed classical argument (J. Hadamard, Bull. Sci. Math. 17
(1893) 240–246; Horn–Johnson / Beckenbach–Bellman). Compact form:
Wikipedia *Hadamard inequality*. `det_le` (`n! x^n`) is a different
already-in bound, not this claim. No novelty claim. Default no claim.
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

set_option linter.unusedVariables false

open Matrix Finset
open scoped Classical BigOperators

noncomputable section

namespace ProofLab.HadamardDet

variable {n : Type*} [Fintype n]

/-! ## Encoding: Euclidean row norm (not labelled Hadamard) -/

/-- Euclidean `ℓ²` norm of row `i`. Encoding; **not** labelled
Hadamard. -/
def rowNorm (A : Matrix n n ℝ) (i : n) : ℝ :=
  Real.sqrt (∑ j, A i j ^ 2)

lemma rowNorm_nonneg (A : Matrix n n ℝ) (i : n) : 0 ≤ rowNorm A i :=
  Real.sqrt_nonneg _

lemma sum_row_sq_nonneg (A : Matrix n n ℝ) (i : n) :
    0 ≤ ∑ j, A i j ^ 2 :=
  sum_nonneg fun _ _ => sq_nonneg _

lemma rowNorm_sq (A : Matrix n n ℝ) (i : n) :
    rowNorm A i ^ 2 = ∑ j, A i j ^ 2 := by
  rw [rowNorm, Real.sq_sqrt (sum_row_sq_nonneg A i)]

lemma prod_rowNorm_nonneg (A : Matrix n n ℝ) :
    0 ≤ ∏ i, rowNorm A i :=
  prod_nonneg fun i _ => rowNorm_nonneg A i

/-! ## Level A: n empty (not labelled Hadamard) -/

/-- Empty index: `det = 1` and the empty product is `1`. Glue;
**not** labelled Hadamard. -/
theorem abs_det_eq_prod_rowNorm_of_isEmpty [IsEmpty n] (A : Matrix n n ℝ) :
    |A.det| = ∏ i, rowNorm A i := by
  have hdet : A.det = 1 := det_isEmpty
  have hprod : (∏ i, rowNorm A i) = 1 := by
    simp [univ_eq_empty]
  simp [hdet, hprod]

/-- `Fin 0` specialisation of the empty case. Glue; **not** labelled
Hadamard. -/
theorem abs_det_eq_prod_rowNorm_fin_zero (A : Matrix (Fin 0) (Fin 0) ℝ) :
    |A.det| = ∏ i, rowNorm A i :=
  abs_det_eq_prod_rowNorm_of_isEmpty A

/-! ## Level A: n unique / 1×1 (not labelled Hadamard) -/

/-- `1×1`: `det` is the unique entry and the row-norm is its absolute
value. Glue; **not** labelled Hadamard. -/
theorem abs_det_eq_prod_rowNorm_of_unique [DecidableEq n] [Unique n]
    (A : Matrix n n ℝ) : |A.det| = ∏ i, rowNorm A i := by
  have hdet : A.det = A default default := det_unique A
  have hprod : (∏ i, rowNorm A i) = rowNorm A default := by
    simp [univ_unique]
  have hsum : ∑ j, A default j ^ 2 = A default default ^ 2 := by
    simp [univ_unique]
  rw [hdet, hprod, rowNorm, hsum, Real.sqrt_sq_eq_abs]

/-- `Fin 1` specialisation of the unique case. Glue; **not** labelled
Hadamard. -/
theorem abs_det_eq_prod_rowNorm_fin_one (A : Matrix (Fin 1) (Fin 1) ℝ) :
    |A.det| = ∏ i, rowNorm A i :=
  abs_det_eq_prod_rowNorm_of_unique A

/-! ## Level A: n=2 explicit 2×2 inequality (not labelled Hadamard) -/

/-- Cauchy–Schwarz on the two rows, with a sign flip on the second so
the inner product is the `2×2` determinant. Glue; **not** labelled
Hadamard. -/
theorem abs_det_le_prod_rowNorm_fin_two (A : Matrix (Fin 2) (Fin 2) ℝ) :
    |A.det| ≤ rowNorm A 0 * rowNorm A 1 := by
  set g : Fin 2 → ℝ := fun j => if j = 0 then A 1 1 else -A 1 0
  have hdot : ∑ j, A 0 j * g j = A.det := by
    rw [det_fin_two, Fin.sum_univ_two]
    simp [g]
    ring
  have hcs :=
    sum_mul_sq_le_sq_mul_sq (univ : Finset (Fin 2))
      (fun j => A 0 j) g
  have hg : ∑ j, g j ^ 2 = ∑ j, A 1 j ^ 2 := by
    rw [Fin.sum_univ_two, Fin.sum_univ_two]
    simp [g]
    ring
  have hsq : A.det ^ 2 ≤ (∑ j, A 0 j ^ 2) * ∑ j, A 1 j ^ 2 := by
    rw [hdot] at hcs
    rwa [hg] at hcs
  have hs0 := sum_row_sq_nonneg A 0
  have habs : |A.det| = Real.sqrt (A.det ^ 2) := (Real.sqrt_sq_eq_abs _).symm
  rw [habs, rowNorm, rowNorm, ← Real.sqrt_mul hs0 _]
  exact Real.sqrt_le_sqrt hsq

/-! ## Level A: pairwise-orthogonal rows ⇒ equality (not labelled Hadamard) -/

/-- Off-diagonal Gram entries vanish; diagonal entries are squared
row norms. Glue; **not** labelled Hadamard. -/
lemma mul_transpose_eq_diagonal_of_orthogonal_rows [DecidableEq n]
    (A : Matrix n n ℝ)
    (h : ∀ i j : n, i ≠ j → ∑ k, A i k * A j k = 0) :
    A * Aᵀ = diagonal fun i => ∑ k, A i k ^ 2 := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [mul_apply, transpose_apply, diagonal_apply_eq, sq]
  · simp [mul_apply, transpose_apply, diagonal_apply_ne _ hij, h i j hij]

/-- Pairwise-orthogonal rows: `A * Aᵀ` is diagonal, so
`|det A| = ∏ rowNorm`. Glue; **not** labelled Hadamard. Vacuous when
`n` is empty or unique, recovering the `n=0/1` equalities. -/
theorem abs_det_eq_prod_rowNorm_of_orthogonal_rows [DecidableEq n]
    (A : Matrix n n ℝ)
    (h : ∀ i j : n, i ≠ j → ∑ k, A i k * A j k = 0) :
    |A.det| = ∏ i, rowNorm A i := by
  have hgram := mul_transpose_eq_diagonal_of_orthogonal_rows A h
  have hdetG : (A * Aᵀ).det = ∏ i, ∑ k, A i k ^ 2 := by
    rw [hgram, det_diagonal]
  have hsq : A.det ^ 2 = ∏ i, ∑ k, A i k ^ 2 := by
    rw [← hdetG, det_mul, det_transpose, sq]
  have hsq' : A.det ^ 2 = (∏ i, rowNorm A i) ^ 2 := by
    rw [hsq]
    have hcong : ∀ i ∈ univ, ∑ k, A i k ^ 2 = rowNorm A i ^ 2 := fun i _ =>
      (rowNorm_sq A i).symm
    rw [prod_congr rfl hcong, prod_pow]
  have : |A.det| = |∏ i, rowNorm A i| :=
    (sq_eq_sq_iff_abs_eq_abs A.det (∏ i, rowNorm A i)).mp hsq'
  rwa [abs_of_nonneg (prod_rowNorm_nonneg A)] at this

/-
Residual (Level B, **out of this ticket**, not sorry-ed):
  theorem hadamard_det
      {n : Type*} [Fintype n] [DecidableEq n]
      (A : Matrix n n ℝ) :
      |A.det| ≤ ∏ i, rowNorm A i
Gram `G = A * Aᵀ` is PSD, `(det A)^2 = det G`, and for a PSD matrix
`det G ≤ ∏ᵢ Gᵢᵢ` (eigenvalue AM-GM, or induction by bordering). Do
not sorry the namesake. Complex conjugate-transpose form, column-norm
corollary, Fischer / Minkowski remain residual. Do not re-prove
`Matrix.det_le` / Gershgorin / Levy–Desplanques / Hadamard product /
three-lines / Vandermonde det / Cauchy–Binet / Kirchhoff /
schwartz-zippel Level B.
-/

end ProofLab.HadamardDet
