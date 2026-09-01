/-
Expander mixing lemma (Alon–Chung 1988 / Alon–Spencer), formalize-only.

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 has `SimpleGraph.adjMatrix` / `isSymm_adjMatrix` /
`IsRegularOfDegree` / `adjMatrix_mulVec` / `IsHermitian.eigenvalues` /
`eigenvectorBasis` / `spectral_theorem` as **infra** (different facts).
ZERO named expander mixing / Alon–Chung discrepancy bound under
`Mathlib/` or `Archive/`. Completing the d-regular mixing bound is the
gap. Do **not** import `Archive.*`.

Pin: `catalog/problems/expander-mixing/STATEMENT.md` (OPE-881; Scout
OPE-870 leftover; Director OPE-880). Encoding: `SimpleGraph.adjMatrix ℝ`
+ `IsHermitian.eigenvalues`. Zero `sorry`. Do not import `Archive.*`.

This is **not** erdos-ramsey-lower (consumed #94 — counting, different).
This is **not** Friendship / Moore / Mycielski / KST / greedy / Brooks.
This is **not** Kirchhoff / Cayley namesake (`lapMatrix` is Laplacian).
This is **not** Wilf `χ ≤ 1+λ_max` (Cassini-class: greedy + Gershgorin).
This is **not** LLL / Chernoff / Azuma / expander Chernoff.
This is **not** mason-stothers (consumed #97).
This is **not** Cheeger / Alon–Boppana / Ramanujan / LPS.
Do **not** re-prove `adjMatrix` / `isSymm_adjMatrix` / `IsRegularOfDegree`
/ `adjMatrix_mulVec` / `spectral_theorem` / `IsHermitian.eigenvalues` /
Gershgorin / Rayleigh.
Leave OPE-403 alone.

v1 is the d-regular undirected form. Non-regular / normalized Laplacian /
directed expanders are out of v1. `n = Fintype.card V` in the denominator
is load-bearing.

Level A `adjMatrix_isHermitian` / `adjMatrix_mulVec_allOnes` /
`orth_allOnes_invariant` is **not** labelled expander: Hermitian
adjacency, eigenvalue `d` on all-ones, `1^⊥` is A-invariant.
Level B engine: indicator inner-product form of `e(S,T)`, mean-zero
residual, mixing identity, residual `ℓ²` bound.
Namesake residual: the pin's `μ ≠ d → |μ| ≤ λ` does **not** bound extra
`d`-eigenvectors in `1^⊥` (disconnected regular graphs). The CS spectral
glue on `1^⊥` needs the operator-norm form of “second eigenvalue”.
Not sorry-ed. No Cheeger. No Kirchhoff.

Transcribed classical argument (Alon–Chung Discrete Math. 72 (1988);
Alon–Spencer expander mixing; Hoory–Linial–Wigderson Bull. AMS 43
(2006) §2). No novelty claim. Default no claim.
-/
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option maxHeartbeats 800000

open Finset SimpleGraph Matrix
open scoped Classical BigOperators

noncomputable section

namespace ProofLab.ExpanderMixing

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## Pin helpers -/

/-- Default Hermitian witness from already-upstream symmetry of `adjMatrix`.
For `ℝ`, `star = id`. Not labelled expander. -/
theorem adjMatrix_isHermitian : (G.adjMatrix ℝ).IsHermitian := by
  refine (IsHermitian.ext_iff (A := G.adjMatrix ℝ)).2 ?_
  intro i j
  simp [adj_comm]

/-- Indicator of a vertex set (engine, not labelled expander). -/
def ind (S : Finset V) : V → ℝ := fun v => if v ∈ S then 1 else 0

lemma sum_ind (S : Finset V) : ∑ v, ind S v = S.card := by
  simp [ind, sum_boole]

lemma card_eq_zero_of_univ_real {S : Finset V}
    (hn : (Fintype.card V : ℝ) = 0) : S.card = 0 := by
  have hV : Fintype.card V = 0 := Nat.cast_eq_zero.mp hn
  have : S.card ≤ Fintype.card V := Finset.card_le_univ S
  omega

/-! ## Level A: Hermitian + eigenvalue `d` on all-ones + `1^⊥` invariant.
**Not** labelled expander. -/

/-- `A 1 = d • 1` for a `d`-regular graph. Glue: already-upstream
`adjMatrix_mulVec_const_apply_of_regular`. Not labelled expander. -/
theorem adjMatrix_mulVec_allOnes {d : ℕ} (hreg : G.IsRegularOfDegree d) :
    G.adjMatrix ℝ *ᵥ (fun _ : V => (1 : ℝ)) = fun _ : V => (d : ℝ) := by
  ext v
  simpa [Function.const, mul_one] using
    (adjMatrix_mulVec_const_apply_of_regular (G := G) (α := ℝ) (d := d)
      (a := (1 : ℝ)) hreg (v := v))

/-- Real-symmetric inner-product identity `⟨x, A y⟩ = ⟨A x, y⟩`.
Glue from `adjMatrix` symmetry (entries), not a re-proof of the spectral
theorem. Not labelled expander. -/
lemma dotProduct_mulVec_comm_adj (x y : V → ℝ) :
    dotProduct x (G.adjMatrix ℝ *ᵥ y) = dotProduct (G.adjMatrix ℝ *ᵥ x) y := by
  simp only [dotProduct, mulVec, adjMatrix_apply, mul_sum, sum_mul, ite_mul,
    mul_ite, one_mul, zero_mul, mul_one, mul_zero]
  rw [sum_comm]
  refine Fintype.sum_congr _ _ fun j => Fintype.sum_congr _ _ fun i => ?_
  by_cases h : G.Adj j i <;> simp [h, adj_comm]

/-- The orthogonal complement of all-ones is `A`-invariant.
**Not** labelled expander. -/
theorem orth_allOnes_invariant {d : ℕ} (hreg : G.IsRegularOfDegree d)
    {x : V → ℝ} (hx : ∑ v, x v = 0) :
    ∑ v, (G.adjMatrix ℝ *ᵥ x) v = 0 := by
  have hdot :
      dotProduct (fun _ : V => (1 : ℝ)) (G.adjMatrix ℝ *ᵥ x) =
        dotProduct (G.adjMatrix ℝ *ᵥ fun _ : V => (1 : ℝ)) x :=
    dotProduct_mulVec_comm_adj (fun _ => (1 : ℝ)) x
  have hA1 := adjMatrix_mulVec_allOnes (G := G) hreg
  have : (d : ℝ) * ∑ v, x v =
      dotProduct (fun _ : V => (1 : ℝ)) (G.adjMatrix ℝ *ᵥ x) := by
    rw [hdot, hA1]
    simp [dotProduct, mul_sum]
  simpa [dotProduct, hx] using this.symm

/-! ## Level B engine: indicator form, residual, mixing identity, `ℓ²` bound.
Not the namesake. -/

/-- Neighbor-sum of an indicator is the adjacency row restricted to `T`. Engine. -/
lemma sum_neighbor_ind (v : V) (T : Finset V) :
    ∑ u ∈ G.neighborFinset v, ind T u = ∑ t ∈ T, (G.adjMatrix ℝ) v t := by
  simp only [ind, adjMatrix_apply, sum_boole]
  exact_mod_cast congrArg Finset.card <| by
    ext u
    simp [mem_neighborFinset, and_comm]

/-- Ordered edge count as an adjacency inner product. Engine. -/
theorem edge_eq_dotProduct (S T : Finset V) :
    ∑ s ∈ S, ∑ t ∈ T, (G.adjMatrix ℝ) s t =
      dotProduct (ind S) (G.adjMatrix ℝ *ᵥ ind T) := by
  simp only [dotProduct, adjMatrix_mulVec_apply]
  have hpt (v : V) :
      ind S v * ∑ u ∈ G.neighborFinset v, ind T u =
        if v ∈ S then ∑ t ∈ T, (G.adjMatrix ℝ) v t else 0 := by
    by_cases hv : v ∈ S
    · simpa [ind, hv] using sum_neighbor_ind (G := G) v T
    · simp [ind, hv]
  simp_rw [hpt]
  simp [sum_ite, sum_const_zero]

/-- Mean-zero residual `1_S − (|S|/n) 1`. Engine, not labelled expander. -/
def residual (S : Finset V) : V → ℝ :=
  fun v => ind S v - (S.card : ℝ) / Fintype.card V

lemma sum_residual (S : Finset V) : ∑ v, residual S v = 0 := by
  simp only [residual, sum_sub_distrib, sum_ind, sum_const, card_univ,
    nsmul_eq_mul]
  by_cases hn : (Fintype.card V : ℝ) = 0
  · have hS : S.card = 0 := card_eq_zero_of_univ_real hn
    simp [hn, hS]
  · field_simp [hn]

lemma residual_add_mean (S : Finset V) :
    ind S = residual S + fun _ : V => (S.card : ℝ) / Fintype.card V := by
  ext v
  simp [residual]

/-- Mixing identity: `e(S,T) − (d/n)|S||T| = ⟨f, A g⟩`. Engine. -/
theorem mixing_identity {d : ℕ} (hreg : G.IsRegularOfDegree d)
    (S T : Finset V) :
    ∑ s ∈ S, ∑ t ∈ T, (G.adjMatrix ℝ) s t -
        (d * S.card * T.card : ℝ) / Fintype.card V =
      dotProduct (residual S) (G.adjMatrix ℝ *ᵥ residual T) := by
  let cS : ℝ := S.card / Fintype.card V
  let cT : ℝ := T.card / Fintype.card V
  have hS : ind S = residual S + fun _ : V => cS := residual_add_mean S
  have hT : ind T = residual T + fun _ : V => cT := residual_add_mean T
  have hA1 := adjMatrix_mulVec_allOnes (G := G) hreg
  have hAindT :
      G.adjMatrix ℝ *ᵥ ind T =
        G.adjMatrix ℝ *ᵥ residual T + fun _ : V => (d : ℝ) * cT := by
    have hconst :
        (fun _ : V => cT) = cT • fun _ : V => (1 : ℝ) := by
      ext; simp
    rw [hT, mulVec_add, hconst, mulVec_smul, hA1]
    ext v
    simp [cT, mul_div_assoc, mul_comm]
  rw [edge_eq_dotProduct (G := G) S T, hS, hAindT]
  have hbilin :
      dotProduct (residual S + fun _ : V => cS)
          (G.adjMatrix ℝ *ᵥ residual T + fun _ : V => (d : ℝ) * cT) =
        dotProduct (residual S) (G.adjMatrix ℝ *ᵥ residual T) +
          dotProduct (residual S) (fun _ : V => (d : ℝ) * cT) +
          dotProduct (fun _ : V => cS) (G.adjMatrix ℝ *ᵥ residual T) +
          dotProduct (fun _ : V => cS) (fun _ : V => (d : ℝ) * cT) := by
    simp [dotProduct, add_mul, mul_add, sum_add_distrib]
    ac_rfl
  rw [hbilin]
  have hcross1 :
      dotProduct (residual S) (fun _ : V => (d : ℝ) * cT) = 0 := by
    simp only [dotProduct]
    have hmul : ∀ v, residual S v * ((d : ℝ) * cT) =
        ((d : ℝ) * cT) * residual S v := fun _ => mul_comm _ _
    simp_rw [hmul, ← mul_sum, sum_residual, mul_zero]
  have hcross2 :
      dotProduct (fun _ : V => cS) (G.adjMatrix ℝ *ᵥ residual T) = 0 := by
    change ∑ v, cS * (G.adjMatrix ℝ *ᵥ residual T) v = 0
    have hsum : ∑ v, (G.adjMatrix ℝ *ᵥ residual T) v = 0 :=
      orth_allOnes_invariant hreg (sum_residual T)
    rw [← mul_sum, hsum, mul_zero]
  have hmean :
      dotProduct (fun _ : V => cS) (fun _ : V => (d : ℝ) * cT) =
        (d * S.card * T.card : ℝ) / Fintype.card V := by
    simp only [dotProduct, cS, cT, mul_assoc]
    by_cases hn : (Fintype.card V : ℝ) = 0
    · have hSc : S.card = 0 := card_eq_zero_of_univ_real hn
      have hTc : T.card = 0 := card_eq_zero_of_univ_real hn
      simp [hn, hSc, hTc]
    · field_simp [hn]
      ring
  simp [hcross1, hcross2, hmean]

/-- `‖1_S − (|S|/n) 1‖² = |S| (1 − |S|/n)`. Engine. -/
theorem residual_dot_self (S : Finset V) :
    dotProduct (residual S) (residual S) =
      (S.card : ℝ) * (1 - (S.card : ℝ) / Fintype.card V) := by
  let c : ℝ := S.card / Fintype.card V
  have hexp :
      dotProduct (residual S) (residual S) =
        (∑ v ∈ S, (1 - c) * (1 - c)) + (∑ v ∈ Sᶜ, (-c) * (-c)) := by
    simp only [dotProduct, residual, ind, c]
    rw [← sum_add_sum_compl (s := S)]
    refine congrArg₂ (· + ·) ?_ ?_
    · refine sum_congr rfl ?_
      intro v hv; simp [hv]
    · refine sum_congr rfl ?_
      intro v hv
      have : v ∉ S := mem_compl.mp hv
      simp [this]
  have hsplit :
      (∑ v ∈ S, (1 - c) * (1 - c)) + (∑ v ∈ Sᶜ, (-c) * (-c)) =
        (S.card : ℝ) * (1 - c) ^ 2 +
          ((Fintype.card V - S.card : ℕ) : ℝ) * c ^ 2 := by
    simp [sum_const, card_compl, nsmul_eq_mul, sq]
  have halg :
      (S.card : ℝ) * (1 - c) ^ 2 +
          ((Fintype.card V - S.card : ℕ) : ℝ) * c ^ 2 =
        (S.card : ℝ) * (1 - c) := by
    have hsub : ((Fintype.card V - S.card : ℕ) : ℝ) =
        (Fintype.card V : ℝ) - S.card :=
      Nat.cast_sub (Finset.card_le_univ S)
    rw [hsub]
    by_cases hn : (Fintype.card V : ℝ) = 0
    · have hS : S.card = 0 := card_eq_zero_of_univ_real hn
      simp [c, hn, hS]
    · field_simp [c, hn]
      ring
  calc
    dotProduct (residual S) (residual S) = _ := hexp
    _ = _ := hsplit
    _ = (S.card : ℝ) * (1 - c) := halg
    _ = (S.card : ℝ) * (1 - (S.card : ℝ) / Fintype.card V) := rfl

theorem residual_dot_self_le (S : Finset V) :
    dotProduct (residual S) (residual S) ≤ S.card := by
  rw [residual_dot_self, mul_sub, mul_one]
  have ha : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  have hn : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  exact sub_le_self _ (mul_nonneg ha (div_nonneg ha hn))

lemma abs_dotProduct_le (x y : V → ℝ) :
    |dotProduct x y| ≤
      Real.sqrt (dotProduct x x) * Real.sqrt (dotProduct y y) := by
  have hin (a b : V → ℝ) :
      ⟪(WithLp.equiv 2 (V → ℝ)).symm a,
        (WithLp.equiv 2 (V → ℝ)).symm b⟫_ℝ =
      dotProduct a b := by
    simpa [star_trivial] using
      (EuclideanSpace.inner_piLp_equiv_symm (𝕜 := ℝ) (ι := V) a b)
  have hle :=
    abs_real_inner_le_norm
      ((WithLp.equiv 2 (V → ℝ)).symm x)
      ((WithLp.equiv 2 (V → ℝ)).symm y)
  have hx :
      ‖(WithLp.equiv 2 (V → ℝ)).symm x‖ = Real.sqrt (dotProduct x x) := by
    rw [norm_eq_sqrt_real_inner, hin]
  have hy :
      ‖(WithLp.equiv 2 (V → ℝ)).symm y‖ = Real.sqrt (dotProduct y y) := by
    rw [norm_eq_sqrt_real_inner, hin]
  simpa [hin, hx, hy] using hle

theorem residual_sqrt_le (S : Finset V) :
    Real.sqrt (dotProduct (residual S) (residual S)) ≤ Real.sqrt S.card :=
  Real.sqrt_le_sqrt (residual_dot_self_le S)

/-
Namesake residual (not sorry-ed):

The textbook CS step wants `|⟨A f, g⟩| ≤ λ ‖f‖ ‖g‖` for `f,g ⊥ 1`, then
`‖f‖ ≤ √|S|`. The identity and the `ℓ²` bound are above.

Closing `|⟨A f, g⟩| ≤ λ ‖f‖ ‖g‖` from the pin

    `∀ i, eigenvalues i ≠ d → |eigenvalues i| ≤ λ`

needs every eigenvector in `1^⊥` to have `|μ| ≤ λ`. Eigenvectors with
`μ ≠ d` are automatically in `1^⊥`. Extra `d`-eigenvectors in `1^⊥`
exist precisely when the graph is disconnected; the pin does not bound
those. Do **not** sorry-in `expander_mixing`. Do **not** expand into
Cheeger / Alon–Boppana / Kirchhoff / Wilf.
-/

end ProofLab.ExpanderMixing
