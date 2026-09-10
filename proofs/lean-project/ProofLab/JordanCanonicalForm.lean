/-
Named 2×2 blocks — Level A only (`J = !![0, 1; 0, 0]` squares to 0
and is not 0; `D = !![1, 0; 0, 2]` is diagonal).
**Not labelled Jordan.**

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 pin `a719ba5c3115` has `Matrix` / `Matrix.mul` /
`!![…]` / `Matrix.diagonal` as **infra**. ZERO named
`jordanCanonical` / `JordanForm` / `jordan_form` / `IsJordanBlock` /
`JordanBlock` under `Mathlib/` or `Archive/` or `ProofLab/`.
Completing the Level A named 2×2 nilpotent / diagonal witnesses is
the gap this ticket lands. The Level B namesake
`jordan_canonical_form` (every square matrix over an algebraically
closed field is similar to a Jordan form) is **out of this ticket**
and is **not** sorry-ed. Rational canonical form / uniqueness of
Jordan blocks are residual of this id.

Pin: `catalog/problems/jordan-canonical-form/STATEMENT.md`
(OPE-1332; Scout OPE-1326 RECOMMENDED PRIME; Director OPE-1331).
Encoding: `jordanNilpotentFinTwo` / `jordanDiagonalFinTwo` on
`Matrix (Fin 2) (Fin 2) ℤ`. Zero `sorry`. Do not import `Archive.*`.

This is **not** `Matrix` / `Matrix.mul` / `!![…]` — already Mathlib.
**USE, do not re-prove; do not cite as Jordan form.**
This is **not** `Matrix.aeval_self_charpoly`
(`LinearAlgebra/Charpoly/Basic.lean`) — DIFFERENT already-in
Cayley–Hamilton. Do **not** re-prove; do **not** cite as Jordan form.
This is **not** `exists_isNilpotent_isSemisimple`
(`LinearAlgebra/JordanChevalley.lean`) — DIFFERENT already-in
Dunford split. Do **not** re-prove; do **not** cite as Jordan form.
This is **not** `IsJordan` (`Algebra/Jordan/Basic.lean`) —
DIFFERENT already-in Jordan-algebra identity. Do **not** re-prove;
do **not** cite as Jordan form. Encoding names
`jordanNilpotentFinTwo` / `jordanDiagonalFinTwo` are the STATEMENT
pin, **not** the algebra class.
This is **not** Sherman–Morrison (`ProofLab/ShermanMorrison.lean`,
consumed #141) / Woodbury / SVD.
This is **not** Cauchy–Binet (`ProofLab/CauchyBinet.lean`) /
circulant-det / Hadamard / Schur-product (consumed matrix mills).
This is **not** Alcuin integer triangles
(`ProofLab/AlcuinIntegerTriangles.lean`, consumed #153).
This is **not** cannonball square-pyramid
(`ProofLab/CannonballSquarePyramid.lean`, consumed #154).
This is **not** orthogonal Latin squares (leftover of Scout
OPE-1326, unassigned this tick).
Do not re-prime the consumed mill. Leave OPE-403 alone.
Leave OPE-1195 alone.

v1 is the named 2×2 blocks: `J * J = 0` and `J ≠ 0` (so the zero
matrix is **not** the Level A nilpotent witness), and `D` equals
`Matrix.diagonal` of `(1, 2)`, **not labelled Jordan**.
Matrix multiplication on `Fin 2` is load-bearing.

Level A: nilpotent `Fin 2` / diagonal `Fin 2`. Optional extra:
`J₁(1) = !![1, 1; 0, 1]` has `(J - I)² = 0`.
**Not** labelled Jordan.

Transcribed classical argument (Camille Jordan 1870). Compact form:
Wikipedia *Jordan normal form*. Type pin: `jordanNilpotentFinTwo` /
`Matrix (Fin 2)`. Dunford `exists_isNilpotent_isSemisimple` is a
different already-in split. `IsJordan` is a different already-in
algebra. No novelty claim. Default no claim.
-/
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

set_option linter.unusedVariables false

open Matrix

namespace ProofLab.JordanCanonicalForm

/-! ## Level A: named 2×2 nilpotent and diagonal blocks
(not labelled Jordan) -/

/-- Nilpotent 2×2 block `!![0, 1; 0, 0]`. Encoding; **not**
labelled Jordan. Does **not** re-prove `Matrix.mul`. -/
def jordanNilpotentFinTwo : Matrix (Fin 2) (Fin 2) ℤ :=
  !![0, 1; 0, 0]

/-- `J * J = 0`. Glue; **not** labelled Jordan.
Load-bearing: matrix multiplication on `Fin 2`. -/
theorem jordanNilpotentFinTwo_sq :
    jordanNilpotentFinTwo * jordanNilpotentFinTwo = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jordanNilpotentFinTwo, mul_apply]

/-- `J ≠ 0`. Glue; **not** labelled Jordan.
Load-bearing: the zero matrix is **not** the Level A witness. -/
theorem jordanNilpotentFinTwo_ne_zero :
    jordanNilpotentFinTwo ≠ 0 := by
  intro h
  have h01 : jordanNilpotentFinTwo 0 1 = 0 := by simp [h]
  simp [jordanNilpotentFinTwo] at h01

/-- Diagonal 2×2 `!![1, 0; 0, 2]`. Encoding; **not** labelled
Jordan. Does **not** re-prove `Matrix.diagonal`. -/
def jordanDiagonalFinTwo : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1, 0; 0, 2]

/-- `D` equals `Matrix.diagonal` of `(1, 2)` (1×1 blocks).
Encoding, **not** labelled Jordan. -/
theorem jordanDiagonalFinTwo_isDiagonal :
    diagonal (fun i : Fin 2 => if i = 0 then (1 : ℤ) else 2)
      = jordanDiagonalFinTwo := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagonal, jordanDiagonalFinTwo]

/-- Optional extra: `J₁(1) = !![1, 1; 0, 1]`. Encoding; **not**
labelled Jordan. -/
def jordanBlockOneFinTwo : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1, 1; 0, 1]

/-- Optional extra: `(J₁(1) - I)² = 0`. Glue; **not** labelled
Jordan. -/
theorem jordanBlockOneFinTwo_sub_one_sq :
    (jordanBlockOneFinTwo - 1) * (jordanBlockOneFinTwo - 1) = 0 := by
  have h : jordanBlockOneFinTwo - 1 = jordanNilpotentFinTwo := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [jordanBlockOneFinTwo, jordanNilpotentFinTwo]
  rw [h]
  exact jordanNilpotentFinTwo_sq

/-
Residual (Level B, **out of this ticket**, not sorry-ed):
`jordan_canonical_form` — every square matrix over an algebraically
closed field is similar to a block-diagonal matrix of Jordan blocks
(Jordan 1870). Do **not** sorry the namesake.
Rational canonical form / uniqueness of Jordan blocks remain
residual of this id; do **not** expand them as extra namesakes.
Do **not** prove `aeval_self_charpoly` as namesake /
`exists_isNilpotent_isSemisimple` as namesake / `IsJordan` as
namesake / Jordan–Hölder as namesake / orthogonal-latin-squares /
ProjectivePlane as namesake / Equiv.Perm as namesake /
alcuin-integer-triangles / integerTriangle / Heron leftover-revivals /
cannonball-square-pyramid / Lucas uniqueness / Watson / Faulhaber /
sherman-morrison / Woodbury / cauchy-binet / circulant-det /
schur-product / hadamard-det.
Leave OPE-403 alone. Leave OPE-1195 alone.
Do **not** label theorems as Jordan-algebra / Dunford collisions.
-/

end ProofLab.JordanCanonicalForm
