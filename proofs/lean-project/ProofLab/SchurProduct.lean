/-
Hadamard (entrywise) product of positive-semidefinite matrices —
Level A only (empty Fin 0 / n=1 nonnegative scalars / nonnegative
diagonal / rank-one outer-product identity).
**Not labelled Schur / Hadamard product.**

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 has `Matrix.hadamard` / `PosSemidef` /
`posSemidef_diagonal_iff` / `posSemidef_iff_eq_transpose_mul_self`
and ZERO named Schur product theorem / `schurProduct` /
`SchurProduct` / `schur_product` / `hadamard_posSemidef` /
`posSemidef_hadamard`. Completing the Level A empty / n=1 /
diagonal / rank-one glue is the gap this ticket lands. The
Level B namesake `schur_product` (general n via Gram / spectral)
is **out of this ticket** and is **not** sorry-ed. SVD / polar /
Moore–Penrose / complex `RCLike` extras are residual of this id.

Pin: `catalog/problems/schur-product/STATEMENT.md` (OPE-1194;
Scout OPE-1189 prime; Director OPE-1193). Encoding: Mathlib
`Matrix.hadamard` + `PosSemidef`. Zero `sorry`. Do not import
`Archive.*`.

This is **not** `Matrix.hadamard` / `⊙` (`Data/Matrix/Hadamard.lean`
L42) — already Mathlib. **USE as glue; do not re-prove; do not
cite as the product theorem.** This is **not** `Matrix.PosSemidef`
/ `posSemidef_diagonal_iff` / `posSemidef_iff_eq_transpose_mul_self`
(already-in infra). This is **not** the Hadamard *determinant*
inequality (`ProofLab/HadamardDet.lean`, PR #115) — different
consumed Hadamard (row-ℓ² det bound); do **not** revive
`hadamard_det` / Fischer / Minkowski det / three-lines. This is
**not** Schur complement (`SchurComplement.lean`
`det_one_add_mul_comm` L395) — already-in Weinstein–Aronszajn /
matrix-det lemma; do **not** cite as the product theorem. This
is **not** Schur partition / Schur number / weak Schur (consumed
mill). This is **not** SVD / polar / Moore–Penrose. This is
**not** gale-shapley (#126) / farey-sequence (#127) /
`lame-euclid` (leftover, unassigned). Do not re-prime the
consumed mill. Leave OPE-403 alone.

v1 is PSD-preservation of `⊙` on real square matrices indexed
by `Fin n`. Finite `Fin n` is load-bearing. Real `ℝ` (not `ℂ`)
is load-bearing for v1. Hermitian / `PosSemidef` hypotheses are
load-bearing.

Level A: `Fin 0` empty Hermitian form is vacuous. `Fin 1`
reduces to `0 ≤ a * b` from `0 ≤ a` and `0 ≤ b`. Diagonal case
is `posSemidef_diagonal_iff` plus entrywise products. Rank-one:
`(v * vᵀ) ⊙ (w * wᵀ)` has entries `vᵢ wᵢ vⱼ wⱼ`, which is
`(v ⊙ w) * (v ⊙ w)ᵀ`, hence a Gram matrix. **Not** labelled
Schur.

Transcribed classical argument (I. Schur, *Bemerkungen zur
Theorie der beschränkten Bilinearformen mit unendlich vielen
Veränderlichen*, J. Reine Angew. Math. 140 (1911) 1–28;
J. Hadamard 1894). Textbook: Horn–Johnson, *Topics in Matrix
Analysis*, Hadamard products. Compact form: Wikipedia *Schur
product theorem*. Type pin: `Matrix.hadamard` / `PosSemidef` /
`Fin n` / `ℝ`. Hadamard determinant inequality is a different
consumed theorem. Schur complement is a different already-in
identity. No novelty claim. Default no claim.
-/
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Matrix.Hadamard
import Mathlib.Data.Matrix.RowCol
import Mathlib.Tactic

set_option linter.unusedVariables false

open Matrix
open scoped Matrix ComplexOrder

noncomputable section

namespace ProofLab.SchurProduct

/-! ## Level A: empty / n=1 / nonnegative diagonal / rank-one
(not labelled Schur) -/

/-- Every `Fin 0` matrix equals the zero matrix (no entries).
Glue; **not** labelled Schur. -/
lemma eq_zero_fin_zero (A : Matrix (Fin 0) (Fin 0) ℝ) : A = 0 := by
  ext i j
  exact i.elim0

/-- Empty `Fin 0`: the Hadamard product of PSD matrices is PSD
(vacuous Hermitian form). Glue; **not** labelled Schur. -/
theorem posSemidef_hadamard_fin_zero
    (A B : Matrix (Fin 0) (Fin 0) ℝ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (A ⊙ B).PosSemidef := by
  rw [eq_zero_fin_zero (A ⊙ B)]
  exact PosSemidef.zero

/-- A `Fin 1` real matrix equals its diagonal (single entry).
Glue; **not** labelled Schur. Reuses `diagonal`; does **not**
re-prove `PosSemidef`. -/
lemma eq_diagonal_fin_one (A : Matrix (Fin 1) (Fin 1) ℝ) :
    A = diagonal fun i => A i i := by
  ext i j
  have hi : i = j := Subsingleton.elim _ _
  simp [hi]

/-- `Fin 1` real PSD iff the unique entry is nonnegative.
Uses `posSemidef_diagonal_iff`; does **not** re-prove it. -/
lemma posSemidef_fin_one_iff (A : Matrix (Fin 1) (Fin 1) ℝ) :
    A.PosSemidef ↔ 0 ≤ A 0 0 := by
  rw [eq_diagonal_fin_one A, posSemidef_diagonal_iff]
  constructor
  · intro h
    exact h 0
  · intro h i
    fin_cases i
    exact h

/-- `n = 1`: Hadamard product of PSD scalars is PSD
(`0 ≤ a` and `0 ≤ b` ⇒ `0 ≤ a * b`). Glue; **not** labelled
Schur. -/
theorem posSemidef_hadamard_fin_one
    (A B : Matrix (Fin 1) (Fin 1) ℝ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (A ⊙ B).PosSemidef := by
  rw [posSemidef_fin_one_iff] at hA hB ⊢
  simpa [hadamard_apply] using mul_nonneg hA hB

/-- Nonnegative diagonal matrices: entrywise product stays PSD.
Uses `diagonal_hadamard_diagonal` and `posSemidef_diagonal_iff`;
does **not** re-prove either. Glue; **not** labelled Schur. -/
theorem posSemidef_hadamard_diagonal
    {n : ℕ} (a b : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    (diagonal a ⊙ diagonal b).PosSemidef := by
  rw [diagonal_hadamard_diagonal]
  refine posSemidef_diagonal_iff.2 fun i => ?_
  simpa [Pi.mul_apply] using mul_nonneg (ha i) (hb i)

/-- Rank-one identity:
`(v * vᵀ) ⊙ (w * wᵀ) = (v ⊙ w) * (v ⊙ w)ᵀ`
(entries `vᵢ wᵢ vⱼ wⱼ`). Encoding; **not** labelled Schur. -/
theorem hadamard_vecMulVec_vecMulVec {n : ℕ} (v w : Fin n → ℝ) :
    vecMulVec v v ⊙ vecMulVec w w = vecMulVec (v * w) (v * w) := by
  ext i j
  simp [hadamard_apply, vecMulVec_apply, Pi.mul_apply]
  ring

/-- A real outer product `v * vᵀ` is PSD (Gram matrix
`col * (col)ᴴ`). Uses `posSemidef_self_mul_conjTranspose`;
does **not** re-prove the spectral theorem. -/
lemma posSemidef_vecMulVec_self {n : ℕ} (v : Fin n → ℝ) :
    (vecMulVec v v).PosSemidef := by
  have hv : star v = v := funext fun _ => star_trivial _
  rw [vecMulVec_eq (ι := Unit) v v, ← hv, ← conjTranspose_col]
  exact posSemidef_self_mul_conjTranspose _

/-- Rank-one Hadamard product of two outer products is PSD
(the identity reduces it to a Gram matrix). Glue; **not**
labelled Schur. -/
theorem posSemidef_hadamard_rankOne {n : ℕ} (v w : Fin n → ℝ) :
    (vecMulVec v v ⊙ vecMulVec w w).PosSemidef := by
  rw [hadamard_vecMulVec_vecMulVec]
  exact posSemidef_vecMulVec_self (v * w)

/-
Residual (Level B, **out of this ticket**, not sorry-ed):
  theorem schur_product {n : ℕ}
      (A B : Matrix (Fin n) (Fin n) ℝ)
      (hA : A.PosSemidef) (hB : B.PosSemidef) :
      (A ⊙ B).PosSemidef
Write `A = Cᵀ * C` via `posSemidef_iff_eq_transpose_mul_self`;
`A ⊙ B = ∑_k (row_k C)ᵀ (row_k C) ⊙ B`, each summand
`D_k B D_k` for a real diagonal `D_k`, hence PSD.
Do not sorry the namesake. SVD / polar / Moore–Penrose /
complex `RCLike` form remain residual of this id.
Do not re-prove `Matrix.hadamard` / `PosSemidef` /
`posSemidef_diagonal_iff` / `posSemidef_iff_eq_transpose_mul_self` /
`IsHermitian.eigenvalues`. Do not prove `hadamard_det` / Fischer /
Minkowski det / three-lines / Schur complement /
`det_one_add_mul_comm` / Schur partition / Schur number /
weak Schur / lame-euclid / `fib_gcd` / gale_shapley /
farey_adjacent.
-/

end ProofLab.SchurProduct
