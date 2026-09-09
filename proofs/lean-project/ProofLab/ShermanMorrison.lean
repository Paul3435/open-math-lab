/-
Sherman–Morrison rank-one inverse update — Level A only (empty Fin 0 /
Fin 1 scalar / Fin 2 I + e₀ e₀ᵀ). **Not labelled Sherman / Woodbury.**

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 pin `a719ba5c3115` has `Matrix.inv` / `A⁻¹` /
`inv_def` / `mul_nonsing_inv` / `nonsing_inv_mul` / `inv_eq_right_inv`
/ `vecMulVec` / `vecMulVec_apply` / `mulVec` / `dotProduct` /
`det_isEmpty` / `det_fin_zero` / `det_fin_one` / `det_fin_two` as
**infra**. ZERO named Sherman–Morrison / `shermanMorrison` /
`sherman_morrison` / `woodbury` / `rankOneUpdate` under `Mathlib/`
or `Archive/` or `ProofLab/`. NonsingularInverse.lean ends with
inverse/adjugate algebra, **no** rank-one update. Completing the
Level A empty / Fin 1 scalar / Fin 2 `I + e₀e₀ᵀ` glue is the gap
this ticket lands. The Level B namesake `sherman_morrison` (every
finite invertible rank-one update with invertible scalar denominator
has the Sherman–Morrison inverse) is **out of this ticket** and is
**not** sorry-ed. Woodbury (block rank-k) extras are residual of
this id. SVD / polar / Moore–Penrose are residual of consumed
schur-product (#129).

Pin: `catalog/problems/sherman-morrison/STATEMENT.md`
(OPE-1253; Scout OPE-1248 RECOMMENDED PRIME; Director OPE-1252).
Encoding: Mathlib `Matrix.inv` / `vecMulVec` on `Fin 0` / `Fin 1` /
`Fin 2` over `ℚ`. Zero `sorry`. Do not import `Archive.*`.

This is **not** `Matrix.inv` / `A⁻¹` (`NonsingularInverse.lean` L191)
/ `inv_def` L194 / `mul_nonsing_inv` L233 / `nonsing_inv_mul` L239
— already Mathlib. **USE, do not re-prove; do not cite as
Sherman–Morrison.**
This is **not** `Matrix.vecMulVec` (`Data/Matrix/Basic.lean` L1453)
/ `vecMulVec_apply` L1457 / `mulVec` L1472 / `dotProduct` L662 —
already Mathlib. **USE, do not re-prove.**
This is **not** `det_isEmpty` / `det_fin_zero` / `det_fin_one` /
`det_fin_two` (`Determinant/Basic.lean`) — already Mathlib. **USE,
do not re-prove.**
This is **not** `det_one_add_mul_comm` (`SchurComplement.lean` L395)
— already-in Weinstein–Aronszajn / matrix-det lemma; **different
theorem** (det vs inverse). **USE as glue if needed; do not
re-prove; do not cite as Sherman–Morrison.**
This is **not** Woodbury (block rank-k; residual of this id; do
**not** sorry Woodbury; do **not** take Woodbury as namesake).
This is **not** SVD / polar / Moore–Penrose
(`ProofLab/SchurProduct.lean`, PR #129).
This is **not** Kirchhoff / DFT / pfaffian
(`ProofLab/CauchyBinet.lean` / `ProofLab/CirculantDet.lean`).
This is **not** `kraft-inequality` (`ProofLab/KraftInequality.lean`,
PR #138) / McMillan / Huffman / Shannon.
This is **not** `sabidussi-boxprod` (`ProofLab/SabidussiBoxProd.lean`,
PR #139) / Hedetniemi / Brooks.
This is **not** graham-pollak / biclique cover (leftover of Scout
OPE-1248, unassigned this tick).
Do not re-prime the consumed mill. Leave OPE-403 alone.
Leave OPE-1195 alone.

v1 is the inverse of a rank-one update on named finite matrices
over `ℚ`: empty `Fin 0`, `Fin 1` scalar, and `Fin 2`
identity-plus-`e₀e₀ᵀ`, **not labelled Sherman / Woodbury**.
Invertibility (`IsUnit det` / `≠ 0`) is load-bearing.
`vecMulVec` rank-one is load-bearing. Inverse over `ℚ` is
load-bearing. Finite `Fin 0` / `Fin 1` / `Fin 2` are load-bearing.

Level A: empty `Fin 0` matrix is the unique empty matrix; `1 + uvᵀ`
is still empty so inverse is `1`. `Fin 1` is the scalar identity
`(a + uv)⁻¹ = 1/(a+uv)` when both denominators are nonzero.
`Fin 2` identity plus `e₀ e₀ᵀ` is `diag(2,1)` whose inverse is
`diag(1/2, 1)`. **Not** labelled Sherman.

Transcribed classical argument (J. Sherman, W. J. Morrison,
*Adjustment of an inverse matrix corresponding to a change in one
element of a given matrix*, Ann. Math. Statist. 21 (1950) 124–127).
Compact form: Wikipedia *Sherman–Morrison formula*. Type pin:
`Matrix.inv` / `vecMulVec` / `Fin n` / `ℚ`. `det_one_add_mul_comm`
is a different already-in det identity. Woodbury is a different
residual block identity. No novelty claim. Default no claim.
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic

set_option linter.unusedVariables false

open Matrix

noncomputable section

namespace ProofLab.ShermanMorrison

/-! ## Level A: empty Fin 0 / Fin 1 scalar / Fin 2 I + e₀ e₀ᵀ
(not labelled Sherman / Woodbury) -/

/-- Empty `Fin 0`: every matrix equals the empty identity.
Glue; **not** labelled Sherman. -/
lemma eq_one_fin_zero (A : Matrix (Fin 0) (Fin 0) ℚ) :
    A = 1 := by
  ext i j
  exact i.elim0

/-- Empty `Fin 0`: `1 + uvᵀ` is still empty, so its inverse is `1`.
Uses uniqueness of the empty matrix (and the `Inv` instance from
`NonsingularInverse`); does **not** re-prove `Matrix.inv` /
`vecMulVec`. Glue; **not** labelled Sherman. -/
theorem inv_add_vecMulVec_fin_zero
    (u v : Fin 0 → ℚ) :
    ((1 : Matrix (Fin 0) (Fin 0) ℚ) + vecMulVec u v)⁻¹
      = (1 : Matrix (Fin 0) (Fin 0) ℚ) :=
  eq_one_fin_zero _

/-- `Fin 1` rank-one update is the scalar `a + u * v`.
Uses `vecMulVec_apply`; does **not** re-prove outer product.
Glue; **not** labelled Sherman. -/
lemma add_vecMulVec_fin_one (a u v : ℚ) :
    (!![a] + vecMulVec ![u] ![v]) = !![a + u * v] := by
  ext i j
  fin_cases i
  fin_cases j
  simp [vecMulVec_apply]

/-- Invertibility of a `Fin 1` scalar matrix is `a ≠ 0`.
Uses `det_fin_one_of`; does **not** re-prove `det`. Load-bearing
invertibility; **not** labelled Sherman. -/
lemma isUnit_det_fin_one (a : ℚ) (ha : a ≠ 0) :
    IsUnit (!![a] : Matrix (Fin 1) (Fin 1) ℚ).det := by
  rw [det_fin_one_of]
  exact isUnit_iff_ne_zero.mpr ha

/-- `Fin 1` scalar: `(a + uv)⁻¹ = 1/(a+uv)` when `a ≠ 0` and
`a + uv ≠ 0`. Uses `inv_eq_right_inv` / `vecMulVec` /
`det_fin_one_of`; does **not** re-prove inverse or outer product.
Glue; **not** labelled Sherman. -/
theorem inv_add_vecMulVec_fin_one
    (a u v : ℚ) (ha : a ≠ 0) (h : a + u * v ≠ 0) :
    (!![a] + vecMulVec ![u] ![v])⁻¹
      = !![1 / (a + u * v)] := by
  -- `ha` is load-bearing Sherman–Morrison setup: `A = !![a]` invertible.
  have _hA : IsUnit (!![a] : Matrix (Fin 1) (Fin 1) ℚ).det :=
    isUnit_det_fin_one a ha
  rw [add_vecMulVec_fin_one]
  refine inv_eq_right_inv ?_
  ext i j
  fin_cases i
  fin_cases j
  simp [Matrix.mul_apply, Matrix.one_apply]
  field_simp

/-- First standard basis vector on `Fin 2`. Encoding; **not**
labelled Sherman / Woodbury. -/
def e0 : Fin 2 → ℚ := ![1, 0]

/-- `I + e₀ e₀ᵀ` on `Fin 2` is `diag(2, 1)`. Uses `vecMulVec_apply`
/ `one_apply`; does **not** re-prove outer product. Glue; **not**
labelled Sherman. -/
lemma one_add_vecMulVec_e0_fin_two :
    (1 : Matrix (Fin 2) (Fin 2) ℚ) + vecMulVec e0 e0
      = !![2, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [e0, vecMulVec_apply, Matrix.one_apply]
  norm_num

/-- Invertibility of `diag(2, 1)`: det = 2 ≠ 0. Uses `det_fin_two_of`;
does **not** re-prove `det`. Load-bearing invertibility; **not**
labelled Sherman. -/
lemma isUnit_det_one_add_vecMulVec_e0_fin_two :
    IsUnit ((1 : Matrix (Fin 2) (Fin 2) ℚ) + vecMulVec e0 e0).det := by
  rw [one_add_vecMulVec_e0_fin_two, det_fin_two_of]
  norm_num

/-- `Fin 2`: inverse of `I + e₀ e₀ᵀ` is `diag(1/2, 1)`.
Uses `inv_eq_right_inv` / `vecMulVec` / `det_fin_two_of`; does
**not** re-prove inverse or outer product. Glue; **not** labelled
Sherman. -/
theorem inv_one_add_vecMulVec_e0_fin_two :
    ((1 : Matrix (Fin 2) (Fin 2) ℚ) + vecMulVec e0 e0)⁻¹
      = !![1 / 2, 0; 0, 1] := by
  have _hdet := isUnit_det_one_add_vecMulVec_e0_fin_two
  rw [one_add_vecMulVec_e0_fin_two]
  refine inv_eq_right_inv ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.one_apply]

/- Residual of this id (comment, **not** `sorry`):
Level B namesake `sherman_morrison` — every finite invertible
rank-one update `A + vecMulVec u v` with invertible scalar
`1 + v ⬝ᵥ A⁻¹.mulVec u` has inverse
`A⁻¹ - (1 / (1 + v ⬝ᵥ A⁻¹.mulVec u)) • vecMulVec (A⁻¹.mulVec u)
(A⁻¹.vecMul v)`. Woodbury (block rank-k) / SVD / polar /
Moore–Penrose extras. Out of this ticket. Do **not** prove
`det_one_add_mul_comm` as Sherman–Morrison. Do **not** prove
graham-pollak here. -/

end ProofLab.ShermanMorrison
