/-
Doubly stochastic matrices — Level A only (empty / n=1 / perm-is-DS /
conv(perm) ⊆ DS / n=2 explicit I/transposition combo).
**Not labelled Birkhoff / von Neumann.**

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 has `Matrix` / `stdBasisMatrix` / `convexHull` /
`Equiv.Perm.permMatrix` / Hall SDR and ZERO named Birkhoff–von Neumann /
`birkhoffVonNeumann` / `isDoublyStochastic` / `doublyStochastic`.
Completing the Level A empty / n=1 / permutation-is-DS /
`conv(perm) ⊆ DS` / n=2 glue is the gap this ticket lands. The
Level B namesake `birkhoff_von_neumann` (`DS ⊆ conv(perm)` via Hall
peeling on the positive support) is **out of this ticket** and is
**not** sorry-ed. Gale–Ryser / transportation polytopes /
Birkhoff-polytope volume extras are residual of this id.

Pin: `catalog/problems/birkhoff-von-neumann/STATEMENT.md` (OPE-1162;
Scout OPE-1157 prime; Director OPE-1161). Encoding: Mathlib
`Equiv.Perm.permMatrix` + `convexHull` + row/column sums. Zero
`sorry`. Do not import `Archive.*`.

This is **not** `Equiv.Perm.permMatrix`
(`LinearAlgebra/Matrix/Permutation.lean` L34) — already Mathlib.
**USE it as glue; do not re-prove; do not redefine; do not cite as
BvN.** This is **not** `stdBasisMatrix` / `convexHull` / `Matrix.one`
(already-in infra). This is **not** Hall's marriage theorem
(`Finset.all_card_le_biUnion_card_iff_exists_injective`) — already
Mathlib; USE as later namesake glue; do **not** re-prove; do **not**
cite as BvN. This is **not** Birkhoff lattice representation
(`Order/Birkhoff.lean`) — different Birkhoff. This is **not**
Birkhoff averages / mean ergodic. This is **not** König matching
ν=τ (consumed). This is **not** Gale–Ryser / transportation. This
is **not** Cauchy–Binet (#117) / Hadamard (#115) / LDL /
`Matrix.det`. This is **not** Singleton (#120) / hook-length (#121)
/ Hamming-bound / Plotkin / Catalan / RSK. This is **not**
nash-williams-arboricity (leftover, unassigned). Do not re-prime
the consumed mill. Leave OPE-403 alone.

v1 is the combinatorial inclusion only. Finite `Fin n` is
load-bearing. Nonnegativity AND both marginals are load-bearing
(a nonnegative matrix with only row-sums 1 is *row-stochastic*, a
different theorem). Peeling a permutation via Hall on the positive
support is the Level B engine, not this ticket.

Level A: `n = 0` empty matrix (vacuous). `n = 1` the unique entry
is `1`. A permutation matrix has a single `1` in each row and
column, hence is DS. Convex combinations preserve nonnegativity
and both marginals, so `conv(perm) ⊆ DS`. For `n = 2`, every DS
matrix is `[[a,1-a],[1-a,a]]` with `0 ≤ a ≤ 1`, equal to
`a • I + (1-a) • σ`. **Not** labelled Birkhoff.

Transcribed classical argument (G. Birkhoff, *Three observations
on linear algebra*, Univ. Nac. Tucumán Rev. Ser. A 5 (1946)
147–151; J. von Neumann, *A certain zero-sum two-person game
equivalent to the optimal assignment problem*, Contributions to
the theory of games II (1953) 5–12). Textbook: Bhatia, *Matrix
Analysis*, or Brualdi–Ryser, *Combinatorial Matrix Theory*.
Compact form: Wikipedia *Birkhoff–von Neumann theorem*. Type pin:
Mathlib `Matrix` / `stdBasisMatrix` / `convexHull` /
`Equiv.Perm.permMatrix`. Hall is a different already-in theorem.
Lattice Birkhoff is a different already-in theorem. No novelty
claim. Default no claim.
-/
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Analysis.Convex.Hull
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

set_option linter.unusedVariables false

open Matrix Finset Equiv
open scoped Classical BigOperators

noncomputable section

namespace ProofLab.BirkhoffVonNeumann

variable {n : ℕ}

/-! ## Encoding: doubly stochastic (not labelled Birkhoff) -/

/-- Nonnegative real `n × n` matrix with every row-sum and every
column-sum equal to `1`. Both marginals are load-bearing.
**Not** labelled Birkhoff / von Neumann. Reuses Mathlib `Matrix`;
does **not** re-prove `permMatrix` / Hall / lattice Birkhoff. -/
def IsDoublyStochastic (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i j, 0 ≤ A i j) ∧
  (∀ i, ∑ j, A i j = 1) ∧
  (∀ j, ∑ i, A i j = 1)

/-- The set of doubly stochastic matrices. Encoding; **not** labelled
Birkhoff. -/
def doublyStochasticSet (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  { A | IsDoublyStochastic A }

lemma mem_doublyStochasticSet {A : Matrix (Fin n) (Fin n) ℝ} :
    A ∈ doublyStochasticSet n ↔ IsDoublyStochastic A :=
  Iff.rfl

/-! ## Glue: Mathlib `permMatrix` entries (do not redefine) -/

/-- Mathlib `Equiv.Perm.permMatrix` is `1` at `(i, σ i)` and `0`
elsewhere (`PEquiv.toMatrix`). Glue; **not** a redefinition;
**not** labelled Birkhoff. -/
lemma permMatrix_apply (σ : Perm (Fin n)) (i j : Fin n) :
    (σ.permMatrix ℝ) i j = if σ i = j then (1 : ℝ) else 0 := by
  simp [Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]

lemma permMatrix_nonneg (σ : Perm (Fin n)) (i j : Fin n) :
    0 ≤ (σ.permMatrix ℝ : Matrix (Fin n) (Fin n) ℝ) i j := by
  rw [permMatrix_apply]
  split_ifs <;> simp

lemma permMatrix_rowSum (σ : Perm (Fin n)) (i : Fin n) :
    ∑ j, (σ.permMatrix ℝ : Matrix (Fin n) (Fin n) ℝ) i j = 1 := by
  simp_rw [permMatrix_apply]
  rw [Fintype.sum_eq_single (σ i)]
  · simp
  · intro j hj
    simp [Ne.symm hj]

lemma permMatrix_colSum (σ : Perm (Fin n)) (j : Fin n) :
    ∑ i, (σ.permMatrix ℝ : Matrix (Fin n) (Fin n) ℝ) i j = 1 := by
  simp_rw [permMatrix_apply]
  rw [Fintype.sum_eq_single (σ.symm j)]
  · simp [Equiv.apply_eq_iff_eq_symm_apply]
  · intro i hi
    simp [Equiv.apply_eq_iff_eq_symm_apply, hi]

/-- The identity matrix is the permutation matrix of `1 : Perm`.
Glue; **not** labelled Birkhoff. -/
lemma permMatrix_one :
    ((1 : Perm (Fin n)).permMatrix ℝ) = (1 : Matrix (Fin n) (Fin n) ℝ) := by
  ext i j
  rw [permMatrix_apply, one_apply]
  simp

/-! ## Level A: permutation matrices are DS (not labelled Birkhoff) -/

/-- A permutation matrix has a single `1` in each row and column,
hence is doubly stochastic. Glue; **not** labelled Birkhoff.
Uses Mathlib `Equiv.Perm.permMatrix`; does **not** re-prove it. -/
theorem permMatrix_isDoublyStochastic (σ : Perm (Fin n)) :
    IsDoublyStochastic (σ.permMatrix ℝ) :=
  ⟨permMatrix_nonneg σ, permMatrix_rowSum σ, permMatrix_colSum σ⟩

/-- The identity matrix is doubly stochastic. Glue; **not** labelled
Birkhoff. -/
theorem one_isDoublyStochastic :
    IsDoublyStochastic (1 : Matrix (Fin n) (Fin n) ℝ) := by
  simpa [permMatrix_one] using permMatrix_isDoublyStochastic (1 : Perm (Fin n))

/-! ## Level A: n = 0 empty (not labelled Birkhoff) -/

/-- Empty index: every quantifier over `Fin 0` is vacuous, so the
empty matrix is doubly stochastic. Glue; **not** labelled Birkhoff. -/
theorem isDoublyStochastic_of_isEmpty [IsEmpty (Fin n)]
    (A : Matrix (Fin n) (Fin n) ℝ) : IsDoublyStochastic A :=
  ⟨fun i => isEmptyElim i, fun i => isEmptyElim i, fun j => isEmptyElim j⟩

/-- `Fin 0` specialisation of the empty case. Glue; **not** labelled
Birkhoff. -/
theorem isDoublyStochastic_fin_zero (A : Matrix (Fin 0) (Fin 0) ℝ) :
    IsDoublyStochastic A :=
  isDoublyStochastic_of_isEmpty A

/-! ## Level A: n = 1 unique `[1]` (not labelled Birkhoff) -/

/-- `1×1`: doubly stochastic iff the unique entry is `1`. Glue;
**not** labelled Birkhoff. -/
theorem isDoublyStochastic_fin_one_iff (A : Matrix (Fin 1) (Fin 1) ℝ) :
    IsDoublyStochastic A ↔ A 0 0 = 1 := by
  constructor
  · intro h
    have hrow := h.2.1 0
    rw [Fin.sum_univ_one] at hrow
    exact hrow
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro i j
      fin_cases i; fin_cases j
      simp [h]
    · intro i
      fin_cases i
      simp [Fin.sum_univ_one, h]
    · intro j
      fin_cases j
      simp [Fin.sum_univ_one, h]

/-- The unique `1×1` doubly stochastic matrix is `[1]`. Glue; **not**
labelled Birkhoff. -/
theorem isDoublyStochastic_one_fin_one :
    IsDoublyStochastic (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  rw [isDoublyStochastic_fin_one_iff]
  simp [one_apply]

/-! ## Level A: convex combinations of DS are DS (not labelled Birkhoff) -/

/-- Convex combinations preserve nonnegativity and both marginals.
Glue; **not** labelled Birkhoff. Load-bearing: both row- and
column-sums (row-stochastic alone is a different theorem). -/
theorem isDoublyStochastic_convex {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsDoublyStochastic A) (hB : IsDoublyStochastic B)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    IsDoublyStochastic (a • A + b • B) := by
  refine ⟨?nonneg, ?row, ?col⟩
  · intro i j
    have : 0 ≤ a * A i j + b * B i j :=
      add_nonneg (mul_nonneg ha (hA.1 i j)) (mul_nonneg hb (hB.1 i j))
    simpa [add_apply, smul_apply] using this
  · intro i
    calc
      ∑ j, (a • A + b • B) i j
        = ∑ j, (a * A i j + b * B i j) := by simp [add_apply, smul_apply]
      _ = a * ∑ j, A i j + b * ∑ j, B i j := by
          simp [mul_sum, sum_add_distrib]
      _ = a * 1 + b * 1 := by rw [hA.2.1 i, hB.2.1 i]
      _ = 1 := by linarith
  · intro j
    calc
      ∑ i, (a • A + b • B) i j
        = ∑ i, (a * A i j + b * B i j) := by simp [add_apply, smul_apply]
      _ = a * ∑ i, A i j + b * ∑ i, B i j := by
          simp [mul_sum, sum_add_distrib]
      _ = a * 1 + b * 1 := by rw [hA.2.2 j, hB.2.2 j]
      _ = 1 := by linarith

/-- The set of doubly stochastic matrices is convex. Glue; **not**
labelled Birkhoff. -/
theorem convex_doublyStochasticSet : Convex ℝ (doublyStochasticSet n) := by
  intro A hA B hB a b ha hb hab
  exact isDoublyStochastic_convex hA hB ha hb hab

/-- Convex combinations of permutation matrices are doubly stochastic:
`conv(perm) ⊆ DS`. Glue; **not** labelled Birkhoff. The reverse
inclusion is the Level B namesake and is **out of this ticket**. -/
theorem convexHull_permMatrix_subset_ds :
    convexHull ℝ (Set.range fun σ : Perm (Fin n) =>
        (σ.permMatrix ℝ : Matrix (Fin n) (Fin n) ℝ)) ⊆
      doublyStochasticSet n := by
  refine convexHull_min ?_ convex_doublyStochasticSet
  rintro _ ⟨σ, rfl⟩
  exact permMatrix_isDoublyStochastic σ

/-! ## Level A: n = 2 explicit I / transposition combo (not labelled Birkhoff) -/

/-- For `n = 2`, a doubly stochastic matrix has equal diagonal
entries `a` and off-diagonal `1 - a`, with `0 ≤ a ≤ 1`. Glue;
**not** labelled Birkhoff. -/
theorem ds_fin_two_entries (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : IsDoublyStochastic A) :
    A 0 0 = A 1 1 ∧ A 0 1 = 1 - A 0 0 ∧ A 1 0 = 1 - A 0 0 ∧
      0 ≤ A 0 0 ∧ A 0 0 ≤ 1 := by
  have r0 : A 0 0 + A 0 1 = 1 := by
    have := hA.2.1 0
    rw [Fin.sum_univ_two] at this
    exact this
  have r1 : A 1 0 + A 1 1 = 1 := by
    have := hA.2.1 1
    rw [Fin.sum_univ_two] at this
    exact this
  have c0 : A 0 0 + A 1 0 = 1 := by
    have := hA.2.2 0
    rw [Fin.sum_univ_two] at this
    exact this
  have h01 : A 0 1 = 1 - A 0 0 := by linarith
  have h10 : A 1 0 = 1 - A 0 0 := by linarith
  have h11 : A 1 1 = A 0 0 := by linarith
  have ha0 : 0 ≤ A 0 0 := hA.1 0 0
  have ha1 : A 0 0 ≤ 1 := by
    have : 0 ≤ A 0 1 := hA.1 0 1
    linarith
  exact ⟨h11.symm, h01, h10, ha0, ha1⟩

/-- `n = 2`: every doubly stochastic matrix equals
`a • I + (1 - a) • σ` for `a = A 0 0` and `σ` the transposition
`(0 1)`. Glue; **not** labelled Birkhoff. -/
theorem ds_fin_two_eq_combo (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : IsDoublyStochastic A) :
    A = A 0 0 • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
      (1 - A 0 0) • ((Equiv.swap (0 : Fin 2) 1).permMatrix ℝ) := by
  have h := ds_fin_two_entries A hA
  have hσ0 : Equiv.swap (0 : Fin 2) 1 0 = 1 := Equiv.swap_apply_left _ _
  have hσ1 : Equiv.swap (0 : Fin 2) 1 1 = 0 := Equiv.swap_apply_right _ _
  ext i j
  simp only [add_apply, smul_apply, one_apply, permMatrix_apply]
  fin_cases i <;> fin_cases j <;> simp [hσ0, hσ1, h.1, h.2.1, h.2.2.1]

/-- The `n = 2` convex combination of `I` and the transposition is
doubly stochastic when `0 ≤ a ≤ 1`. Glue; **not** labelled Birkhoff. -/
theorem combo_fin_two_isDoublyStochastic {a : ℝ} (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1) :
    IsDoublyStochastic
      (a • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        (1 - a) • ((Equiv.swap (0 : Fin 2) 1).permMatrix ℝ)) := by
  have hb : 0 ≤ 1 - a := sub_nonneg.mpr ha1
  have hab : a + (1 - a) = 1 := by ring
  exact isDoublyStochastic_convex one_isDoublyStochastic
    (permMatrix_isDoublyStochastic _) ha0 hb hab

/-- `n = 2` characterisation: doubly stochastic iff the matrix is
`a • I + (1 - a) • σ` for some `0 ≤ a ≤ 1`. Glue; **not** labelled
Birkhoff. -/
theorem isDoublyStochastic_fin_two_iff (A : Matrix (Fin 2) (Fin 2) ℝ) :
    IsDoublyStochastic A ↔
      ∃ a : ℝ, 0 ≤ a ∧ a ≤ 1 ∧
        A = a • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
          (1 - a) • ((Equiv.swap (0 : Fin 2) 1).permMatrix ℝ) := by
  constructor
  · intro hA
    refine ⟨A 0 0, ?_, ?_, ds_fin_two_eq_combo A hA⟩
    · exact (ds_fin_two_entries A hA).2.2.2.1
    · exact (ds_fin_two_entries A hA).2.2.2.2
  · rintro ⟨a, ha0, ha1, rfl⟩
    exact combo_fin_two_isDoublyStochastic ha0 ha1

/-
Residual (Level B, **out of this ticket**, not sorry-ed):
  theorem birkhoff_von_neumann {n : ℕ}
      (A : Matrix (Fin n) (Fin n) ℝ)
      (hA : IsDoublyStochastic A) :
      A ∈ convexHull ℝ
        (Set.range fun σ : Equiv.Perm (Fin n) => σ.permMatrix ℝ)
The positive support of a DS matrix has a perfect matching (Hall);
subtract a scaled permutation matrix; induct on the number of
positive entries. Do not sorry the namesake. Gale–Ryser /
transportation polytopes / Birkhoff-polytope volume remain residual
of this id. Do not re-prove Hall / lattice Birkhoff / Birkhoff
averages / König matching / LDL / cauchy_binet / Kirchhoff /
singleton_bound / hook_length / nash-williams-arboricity.
-/

end ProofLab.BirkhoffVonNeumann
