/-
Cauchy–Binet — Level A only (|m|=0 / |m|=1 / square det_mul glue).
**Not labelled Cauchy–Binet.**

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 has `Matrix.det` / `det_mul` / `det_isEmpty` / `det_unique`
/ `submatrix` / `powersetCard` and ZERO named Cauchy–Binet / `cauchy_binet`
/ `CauchyBinet`. Completing the Level A empty / 1×1 / square `det_mul` glue
is the gap this ticket lands. The Level B namesake `cauchy_binet` (Leibniz
expansion of `det(A * B)` grouped by image subset `S ⊆ n`) is **out of
this ticket** and is **not** sorry-ed. Kirchhoff matrix-tree / Gram /
compound-matrix extras are residual (Cayley leftover-risk).

Pin: `catalog/problems/cauchy-binet/STATEMENT.md` (OPE-1130; Scout
OPE-1125 prime; Director OPE-1129). Encoding: Mathlib `Matrix.det` +
`submatrix` + `powersetCard`. Zero `sorry`. Do not import `Archive.*`.

This is **not** `Matrix.det_mul` (`Determinant/Basic.lean` L129) — already
Mathlib square multiplicativity. **USE as glue; do not re-prove; do not
cite as Cauchy–Binet.** This is **not** `Matrix.det_le` (already-in
`n! x^n`). This is **not** Hadamard determinant inequality
(`ProofLab/HadamardDet.lean`, PR #115) — different consumed theorem
(row-norm bound on `|det|`); **USE `Matrix.det`; do not re-prove
`hadamard_det`; do not revive Hadamard Level B.** This is **not**
Gershgorin / Levy–Desplanques / Hadamard product / three-lines /
Vandermonde det. This is **not** Kirchhoff matrix-tree (Cayley
leftover-risk; residual of this id). This is **not** Schwartz–Zippel
Level B / Ore Level B / `konig_edge_chromatic` / AES-B / ostrowski-q
Level B / frobenius-real-division Level B / noether-normalization
Level B / krenn-gu / hou-zeng-pfc / sun-135. Do not re-prime the
consumed mill. Leave OPE-403 alone. Do **not** prove
bollobas-two-families / Sperner / LYM here.

v1 is the commutative-ring rectangular form. `Fintype m` / `Fintype n`
are load-bearing. `CommRing R` is load-bearing (`det_mul` lives there;
no field required). The column-index subtype / reindex `Equiv` is
load-bearing. When `Fintype.card m > Fintype.card n` the powerset is
empty and the minor-sum is `0` (or `1` if `m` is empty) — load-bearing
on the sum side. LHS `det = 0` for nonempty `m` with strictly smaller
inner index is residual except the empty-`n` zero-matrix glue.

Level A: empty index `det = 1` on both sides (`det_isEmpty`). Size `1`:
`A * B` is the scalar `∑_j A i j * B j i`. Square case: `powersetCard
|m|` of `univ n` is a singleton when `|m| = |n|`, and `submatrix` along
the unique `Equiv` is `det_mul`. **Not** labelled Cauchy–Binet.

Transcribed classical argument (J. Binet 1812 / A.-L. Cauchy 1815;
Horn–Johnson, *Matrix Analysis*, §0.8.7). Compact form: Wikipedia
*Cauchy–Binet formula*. `det_mul` is a different already-in square
identity, not this claim. No novelty claim. Default no claim.
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option linter.unusedVariables false

open Matrix Finset
open scoped Classical BigOperators

noncomputable section

namespace ProofLab.CauchyBinet

variable {R : Type*} [CommRing R]
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-! ## Encoding: square minors via a card-equiv (not labelled Cauchy–Binet) -/

/-- Reindex `m ≃ {x // x ∈ S}` when `|S| = |m|`. Encoding; **not** labelled
Cauchy–Binet. Same equiv is used on columns of `A` and rows of `B` so
permutation signs cancel in the product of dets. -/
def indexEquiv (S : Finset n) (h : S.card = Fintype.card m) :
    m ≃ { x // x ∈ S } :=
  Fintype.equivOfCardEq (by rw [Fintype.card_coe, h])

/-- Product of matching square minors of `A` (columns `S`) and `B`
(rows `S`), reindexed along `indexEquiv`. Encoding; **not** labelled
Cauchy–Binet. -/
def squareMinors (A : Matrix m n R) (B : Matrix n m R) (S : Finset n)
    (h : S.card = Fintype.card m) : R :=
  let e := indexEquiv (m := m) S h
  det (A.submatrix id (Subtype.val ∘ e)) *
    det (B.submatrix (Subtype.val ∘ e) id)

/-- Sum of matching square minors of size `|m|` over subsets of `n`.
Encoding of the Cauchy–Binet right-hand side; **not** labelled
Cauchy–Binet. The `dite` is definitional hygiene: membership in
`powersetCard` already forces the card equation. -/
def minorSum (A : Matrix m n R) (B : Matrix n m R) : R :=
  ∑ S ∈ (univ : Finset n).powersetCard (Fintype.card m),
    if h : S.card = Fintype.card m then squareMinors A B S h else 0

lemma squareMinors_eq (A : Matrix m n R) (B : Matrix n m R) (S : Finset n)
    (h : S.card = Fintype.card m) :
    squareMinors A B S h =
      det (A.submatrix id (Subtype.val ∘ indexEquiv (m := m) S h)) *
        det (B.submatrix (Subtype.val ∘ indexEquiv (m := m) S h) id) :=
  rfl

lemma minorSum_apply (A : Matrix m n R) (B : Matrix n m R) :
    minorSum A B =
      ∑ S ∈ (univ : Finset n).powersetCard (Fintype.card m),
        if h : S.card = Fintype.card m then squareMinors A B S h else 0 :=
  rfl

/-- Identify `{x // x ∈ univ}` with `n`. Encoding; **not** labelled
Cauchy–Binet. -/
def subtypeUnivEquiv : { x : n // x ∈ (univ : Finset n) } ≃ n :=
  Equiv.subtypeUnivEquiv (fun _ => mem_univ _)

/-! ## Level A: |m|=0 (not labelled Cauchy–Binet) -/

/-- Empty row index: `det(A * B) = 1` and the unique empty-subset minor
product is `1`. Glue; **not** labelled Cauchy–Binet. -/
theorem det_mul_eq_minorSum_of_isEmpty [IsEmpty m] (A : Matrix m n R)
    (B : Matrix n m R) : det (A * B) = minorSum A B := by
  have hcard : Fintype.card m = 0 := Fintype.card_eq_zero
  have hdet : det (A * B) = 1 := det_isEmpty
  have hpow : (univ : Finset n).powersetCard (Fintype.card m) = {∅} := by
    rw [hcard, powersetCard_zero]
  have hS : (∅ : Finset n).card = Fintype.card m := by
    simp [hcard]
  have hminors : squareMinors A B (∅ : Finset n) hS = 1 := by
    have hA : det (A.submatrix id (Subtype.val ∘ indexEquiv (m := m) ∅ hS)) = 1 :=
      det_isEmpty
    have hB : det (B.submatrix (Subtype.val ∘ indexEquiv (m := m) ∅ hS) id) = 1 :=
      det_isEmpty
    simp [squareMinors, hA, hB]
  rw [hdet, minorSum, hpow, sum_singleton, dif_pos hS, hminors]

/-- `Fin 0` specialisation of the empty case. Glue; **not** labelled
Cauchy–Binet. -/
theorem det_mul_eq_minorSum_fin_zero (A : Matrix (Fin 0) n R)
    (B : Matrix n (Fin 0) R) : det (A * B) = minorSum A B :=
  det_mul_eq_minorSum_of_isEmpty A B

/-! ## Level A: |m|=1 (not labelled Cauchy–Binet) -/

lemma val_indexEquiv_singleton [Unique m] (j : n)
    (h : ({j} : Finset n).card = Fintype.card m) :
    Subtype.val (indexEquiv (m := m) {j} h (default : m)) = j :=
  mem_singleton.mp (indexEquiv (m := m) {j} h (default : m)).property

/-- `1×1`: `det(A * B)` is the unique entry, a dot product of a row of
`A` with a column of `B`; the minor-sum runs over singletons of `n`.
Glue; **not** labelled Cauchy–Binet. -/
theorem det_mul_eq_minorSum_of_unique [Unique m] (A : Matrix m n R)
    (B : Matrix n m R) : det (A * B) = minorSum A B := by
  have hcard : Fintype.card m = 1 := Fintype.card_unique
  rw [det_unique, mul_apply, minorSum]
  have hpow :
      (univ : Finset n).powersetCard (Fintype.card m) =
        (univ : Finset n).map ⟨singleton, singleton_injective⟩ := by
    rw [hcard, powersetCard_one]
  rw [hpow, sum_map]
  refine Finset.sum_congr rfl ?_
  intro j _
  simp only [Function.Embedding.coeFn_mk]
  have hS : ({j} : Finset n).card = Fintype.card m := by
    simp [card_singleton, hcard]
  rw [dif_pos hS]
  have hA : det (A.submatrix id
      (Subtype.val ∘ indexEquiv (m := m) {j} hS)) = A default j := by
    rw [det_unique]
    simp [submatrix_apply, val_indexEquiv_singleton]
  have hB : det (B.submatrix
      (Subtype.val ∘ indexEquiv (m := m) {j} hS) id) = B j default := by
    rw [det_unique]
    simp [submatrix_apply, val_indexEquiv_singleton]
  simp [squareMinors, hA, hB]

/-- `Fin 1` specialisation of the unique case. Glue; **not** labelled
Cauchy–Binet. -/
theorem det_mul_eq_minorSum_fin_one (A : Matrix (Fin 1) n R)
    (B : Matrix n (Fin 1) R) : det (A * B) = minorSum A B :=
  det_mul_eq_minorSum_of_unique A B

/-! ## Level A: |m|=|n| square det_mul glue (not labelled Cauchy–Binet) -/

/-- When `|m| = |n|`, `powersetCard |m|` of `univ n` is the singleton
`{univ}`, and the matching minors are `A` / `B` reindexed along a
card-equiv. Then `submatrix_mul_equiv` + Mathlib `det_mul` recover
`det(A * B)`. Glue; **not** labelled Cauchy–Binet. **Do not cite
`det_mul` as Cauchy–Binet.** -/
theorem det_mul_eq_minorSum_of_card_eq (hcard : Fintype.card m = Fintype.card n)
    (A : Matrix m n R) (B : Matrix n m R) : det (A * B) = minorSum A B := by
  have huniv : (univ : Finset n).card = Fintype.card m := by
    rw [card_univ, hcard]
  have hpow : (univ : Finset n).powersetCard (Fintype.card m) = {univ} := by
    rw [← huniv, powersetCard_self]
  have hS : (univ : Finset n).card = Fintype.card m := huniv
  rw [minorSum, hpow, sum_singleton, dif_pos hS]
  -- Reindex along the card-equiv composed with `{x // x ∈ univ} ≃ n`.
  set e := indexEquiv (m := m) univ hS
  set e' : m ≃ n := e.trans (subtypeUnivEquiv (n := n))
  have he' : (Subtype.val ∘ e : m → n) = e' := by
    funext i
    rfl
  have hmul : A.submatrix id e' * B.submatrix e' id = A * B := by
    rw [submatrix_mul_equiv, submatrix_id_id]
  have hA : A.submatrix id (Subtype.val ∘ e) = A.submatrix id e' := by
    simp [he']
  have hB : B.submatrix (Subtype.val ∘ e) id = B.submatrix e' id := by
    simp [he']
  -- Mathlib `det_mul` (square multiplicativity) — USE, do not re-prove.
  calc
    det (A * B) = det (A.submatrix id e' * B.submatrix e' id) := by rw [hmul]
    _ = det (A.submatrix id e') * det (B.submatrix e' id) := det_mul _ _
    _ = squareMinors A B univ hS := by
      simp [squareMinors, hA, hB]

/-- Equal `Fin k` indices: square `det_mul` glue. **Not** labelled
Cauchy–Binet. -/
theorem det_mul_eq_minorSum_fin (k : ℕ) (A : Matrix (Fin k) (Fin k) R)
    (B : Matrix (Fin k) (Fin k) R) : det (A * B) = minorSum A B :=
  det_mul_eq_minorSum_of_card_eq (by simp) A B

/-! ## Level A: oversized inner index, sum side (not labelled Cauchy–Binet) -/

/-- When `|m| > |n|` the `powersetCard` is empty, so the minor-sum is
`0`. Glue; **not** labelled Cauchy–Binet. (If `m` is empty then
`|m| = 0 ≤ |n|`, so this hypothesis already forces `m` nonempty.) -/
theorem minorSum_eq_zero_of_card_lt (hlt : Fintype.card n < Fintype.card m)
    (A : Matrix m n R) (B : Matrix n m R) : minorSum A B = 0 := by
  have hempty : (univ : Finset n).powersetCard (Fintype.card m) = ∅ := by
    simpa [card_univ] using
      (powersetCard_eq_empty (s := (univ : Finset n)) (n := Fintype.card m)).2
        (by simpa [card_univ] using hlt)
  simp [minorSum, hempty]

/-- Empty inner index and nonempty outer index: `A * B` is the zero
matrix, so `det = 0`, matching the empty minor-sum. Glue; **not**
labelled Cauchy–Binet. -/
theorem det_mul_eq_minorSum_of_isEmpty_n [IsEmpty n] [Nonempty m]
    (A : Matrix m n R) (B : Matrix n m R) : det (A * B) = minorSum A B := by
  have hlt : Fintype.card n < Fintype.card m := by
    have hn : Fintype.card n = 0 := Fintype.card_eq_zero
    have hm : 0 < Fintype.card m := Fintype.card_pos
    simpa [hn] using hm
  have hAB : A * B = 0 := by
    ext i j
    simp [mul_apply]
  have hdet : det (A * B) = 0 := by
    rw [hAB]
    exact det_zero ‹Nonempty m›
  rw [hdet, minorSum_eq_zero_of_card_lt hlt A B]

/-
Residual (Level B, **out of this ticket**, not sorry-ed):
  theorem cauchy_binet
      {R : Type*} [CommRing R]
      {m n : Type*} [Fintype m] [Fintype n]
      [DecidableEq m] [DecidableEq n]
      (A : Matrix m n R) (B : Matrix n m R) :
      det (A * B) =
        ∑ S ∈ (Finset.univ : Finset n).powersetCard (Fintype.card m),
          det (A.submatrix id (subtype S)) *
          det (B.submatrix (subtype S) id)
Leibniz expansion of `det(A * B)` (`det_apply`) grouped by the image
subset `S ⊆ n` of an injection `m → n`. Do not sorry the namesake.
When `|m| > |n|` and `n` is nonempty, `det(A * B) = 0` (rank / Leibniz)
is residual on the left-hand side; the minor-sum is already `0` by
`minorSum_eq_zero_of_card_lt`. Kirchhoff matrix-tree / Gram /
compound matrices remain residual. Do not re-prove `Matrix.det_mul` /
`det_le` / Gershgorin / Hadamard product / three-lines / Vandermonde /
`hadamard_det` / `schwartz_zippel` / Kirchhoff / Cayley namesake /
bollobas-two-families / Sperner / LYM.
-/

end ProofLab.CauchyBinet
