/-
Combinatorial Nullstellensatz, non-vanishing form (Alon 1999, Theorem 1.2):
if `f ∈ F[x₁,…,xₙ]` has `deg_{xᵢ} f ≤ tᵢ` and the coefficient of `∏ xᵢ^{tᵢ}` is
nonzero, then `f` does not vanish on any box `S₁ × ⋯ × Sₙ` with `|Sᵢ| > tᵢ`.

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 has `MvPolynomial.coeff` / `degreeOf` / `eval`. ZERO combinatorial
Nullstellensatz / Alon-CNS ident in Mathlib+Archive.

Pin: `catalog/problems/combinatorial-nullstellensatz/STATEMENT.md` (OPE-729;
Scout OPE-717 leftover slot #2; Director OPE-728). Encoding: `f : MvPolynomial (Fin n) F`,
`t : Fin n → ℕ`, `S : Fin n → Finset F`. Monomial `Finsupp.equivFunOnFinite.symm t`.
Per-variable `degreeOf`, **not** `totalDegree`. Zero `sorry`. Do not import `Archive.*`.

This is **not** Hilbert Nullstellensatz (`RingTheory/Nullstellensatz.lean`).
This is **not** Chevalley–Warning (`FieldTheory/ChevalleyWarning.lean`).
This is **not** EGZ (`Combinatorics/Additive/ErdosGinzburgZiv.lean`).
This is **not** Alon–Füredi / cap sets. This is **not** sunflower / Kruskal–Katona /
Oddtown / EKR.

Level A: `n = 0` (nonzero constant); univariate `Polynomial` root-cardinality glue;
`n = 1`; `f = C c` constants. Zero sorry. **Not labelled combinatorial Nullstellensatz.**
Level B: namesake `combinatorial_nullstellensatz` by induction on `n` (peel `x₀` via
`finSuccEquiv`; remainder degree `< |S 0|` so the leading `x₀^{t 0}` coefficient is
preserved; IH in `n` variables; univariate evaluation in `x₀`).
-/
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Finsupp.Fin
import Mathlib.Tactic

set_option maxHeartbeats 800000

open MvPolynomial
open scoped Classical

noncomputable section

namespace ProofLab.CombinatorialNullstellensatz

variable {F : Type*} [Field F]

/-! ## Engine lemmas (not labelled combinatorial Nullstellensatz) -/

/-- The STATEMENT monomial `t` is `Finsupp.cons` of the head exponent with the tail. -/
theorem monomial_eq_cons {n : ℕ} (t : Fin (n + 1) → ℕ) :
    (Finsupp.equivFunOnFinite.symm t : Fin (n + 1) →₀ ℕ) =
      Finsupp.cons (t 0) (Finsupp.equivFunOnFinite.symm fun i : Fin n => t i.succ) := by
  ext i
  refine Fin.cases ?_ ?_ i
  · simp [Finsupp.cons_zero]
  · intro j
    simp [Finsupp.cons_succ]

/-- Per-variable degree of an `finSuccEquiv` coefficient is bounded by the corresponding
tail degree of `f`. Engine, not a second id. -/
theorem degreeOf_coeff_finSuccEquiv_le {n : ℕ} (f : MvPolynomial (Fin (n + 1)) F)
    (k : ℕ) (j : Fin n) {d : ℕ} (h : f.degreeOf j.succ ≤ d) :
    ((finSuccEquiv F n f).coeff k).degreeOf j ≤ d := by
  rw [degreeOf_le_iff] at h ⊢
  intro m hm
  have hm' : Finsupp.cons k m ∈ f.support := support_coeff_finSuccEquiv.mp hm
  simpa [Finsupp.cons_succ] using h (Finsupp.cons k m) hm'

/-- `deg_{x₀} f ≤ d` implies the univariate `finSuccEquiv` polynomial has `natDegree ≤ d`. -/
theorem natDegree_finSuccEquiv_le {n : ℕ} (f : MvPolynomial (Fin (n + 1)) F) {d : ℕ}
    (h : f.degreeOf 0 ≤ d) : (finSuccEquiv F n f).natDegree ≤ d := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  by_contra hne
  have hsup : ((finSuccEquiv F n f).coeff N).support.Nonempty := by
    rwa [Finset.nonempty_iff_ne_empty, ne_eq, support_eq_empty]
  obtain ⟨m, hm⟩ := hsup
  have hm' : Finsupp.cons N m ∈ f.support := support_coeff_finSuccEquiv.mp hm
  have : (Finsupp.cons N m) 0 ≤ d := (degreeOf_le_iff.mp h) _ hm'
  simp only [Finsupp.cons_zero] at this
  exact (not_le_of_gt hN) this

/-- On zero variables, evaluation is the constant coefficient. Glue. -/
theorem eval_eq_coeff_zero_empty (f : MvPolynomial (Fin 0) F) (x : Fin 0 → F) :
    eval x f = f.coeff 0 := by
  rw [eval_eq]
  have hprod : ∀ d : Fin 0 →₀ ℕ, (∏ i ∈ d.support, x i ^ d i) = 1 := fun d => by
    have : d.support = (∅ : Finset (Fin 0)) :=
      Finset.eq_empty_iff_forall_not_mem.mpr fun i _ => i.elim0
    simp [this]
  simp_rw [hprod, mul_one]
  apply Finset.sum_eq_single (0 : Fin 0 →₀ ℕ)
  · intro d _ hd0
    exact (hd0 (by ext i; exact i.elim0)).elim
  · intro hnotin
    exact not_mem_support_iff.mp hnotin

/-! ## Level A: `n = 0` / univariate glue / `n = 1` / constants (not labelled CNS) -/

/-- `n = 0`: a nonzero constant (the unique monomial) does not vanish. Glue. -/
theorem combinatorial_nullstellensatz_zero (f : MvPolynomial (Fin 0) F) (t : Fin 0 → ℕ)
    (_S : Fin 0 → Finset F)
    (hcoeff : f.coeff (Finsupp.equivFunOnFinite.symm t) ≠ 0) :
    ∃ x : Fin 0 → F, (∀ i, x i ∈ _S i) ∧ eval x f ≠ 0 := by
  have ht0 : Finsupp.equivFunOnFinite.symm t = (0 : Fin 0 →₀ ℕ) := by
    ext i
    exact i.elim0
  rw [ht0] at hcoeff
  refine ⟨isEmptyElim, fun i => i.elim0, ?_⟩
  rwa [eval_eq_coeff_zero_empty]

/-- Univariate root bound: a polynomial of `natDegree ≤ t` with `coeff t ≠ 0` misses a
box of size `> t`. Mathlib `Polynomial` glue; **not** labelled combinatorial Nullstellensatz. -/
theorem univariate_nonvanishing (p : Polynomial F) (t : ℕ) (S : Finset F)
    (hdeg : p.natDegree ≤ t) (hcard : t < S.card) (hcoeff : p.coeff t ≠ 0) :
    ∃ x ∈ S, p.eval x ≠ 0 := by
  have hp0 : p ≠ 0 := by
    intro hp
    simp [hp] at hcoeff
  have hroots : p.roots.toFinset.card ≤ t := by
    have h1 : p.roots.toFinset.card ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
    have h2 : Multiset.card p.roots ≤ p.natDegree := Polynomial.card_roots' p
    omega
  have hnot : ¬ S ⊆ p.roots.toFinset := by
    intro hsub
    have := Finset.card_le_card hsub
    omega
  obtain ⟨x, hxS, hxnin⟩ := Finset.not_subset.mp hnot
  refine ⟨x, hxS, ?_⟩
  intro heval
  have : x ∈ p.roots.toFinset :=
    Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp0).mpr heval)
  exact hxnin this

/-- `n = 1`: reduce to the univariate root bound via `finSuccEquiv`. Glue, not CNS. -/
theorem combinatorial_nullstellensatz_one (f : MvPolynomial (Fin 1) F) (t : Fin 1 → ℕ)
    (S : Fin 1 → Finset F) (hdeg : ∀ i, f.degreeOf i ≤ t i)
    (hcard : ∀ i, t i < (S i).card)
    (hcoeff : f.coeff (Finsupp.equivFunOnFinite.symm t) ≠ 0) :
    ∃ x : Fin 1 → F, (∀ i, x i ∈ S i) ∧ eval x f ≠ 0 := by
  let x0 : Fin 0 → F := isEmptyElim
  let p : Polynomial F := Polynomial.map (eval x0) (finSuccEquiv F 0 f)
  have hdegP : p.natDegree ≤ t 0 :=
    (Polynomial.natDegree_map_le _ _).trans (natDegree_finSuccEquiv_le f (hdeg 0))
  have hcoeffP : p.coeff (t 0) ≠ 0 := by
    have hmap : p.coeff (t 0) = eval x0 ((finSuccEquiv F 0 f).coeff (t 0)) :=
      Polynomial.coeff_map _ _
    rw [hmap, eval_eq_coeff_zero_empty]
    have hmon := monomial_eq_cons t
    have htail : (Finsupp.equivFunOnFinite.symm fun i : Fin 0 => t i.succ) =
        (0 : Fin 0 →₀ ℕ) := by
      ext i
      exact i.elim0
    have : f.coeff (Finsupp.cons (t 0) (0 : Fin 0 →₀ ℕ)) ≠ 0 := by
      rwa [hmon, htail] at hcoeff
    rwa [finSuccEquiv_coeff_coeff]
  obtain ⟨y, hyS, hy⟩ := univariate_nonvanishing p (t 0) (S 0) hdegP (hcard 0) hcoeffP
  refine ⟨Fin.cons y x0, ?_, ?_⟩
  · intro i
    rw [Fin.eq_zero i, Fin.cons_zero]
    exact hyS
  · have hmap : eval (Fin.cons y x0) f = p.eval y := eval_eq_eval_mv_eval' x0 y f
    rwa [hmap]

/-- Constants: if `C c` has a nonzero STATEMENT coefficient then `t = 0` and `c ≠ 0`,
so any point of a nonempty box works. Glue. -/
theorem combinatorial_nullstellensatz_C {n : ℕ} (c : F) (t : Fin n → ℕ)
    (S : Fin n → Finset F) (hcard : ∀ i, t i < (S i).card)
    (hcoeff : (C c : MvPolynomial (Fin n) F).coeff (Finsupp.equivFunOnFinite.symm t) ≠ 0) :
    ∃ x : Fin n → F, (∀ i, x i ∈ S i) ∧ eval x (C c) ≠ 0 := by
  have ht0 : ∀ i, t i = 0 := by
    intro i
    by_contra hne
    have hne0 : (Finsupp.equivFunOnFinite.symm t : Fin n →₀ ℕ) ≠ 0 := by
      intro hz
      have : t i = 0 := by
        have := congrArg (fun m : Fin n →₀ ℕ => (m : Fin n → ℕ) i) hz
        simpa using this
      exact hne this
    have : (C c : MvPolynomial (Fin n) F).coeff (Finsupp.equivFunOnFinite.symm t) = 0 := by
      rw [coeff_C, if_neg (Ne.symm hne0)]
    exact hcoeff this
  have hc : c ≠ 0 := by
    have hmon0 : Finsupp.equivFunOnFinite.symm t = (0 : Fin n →₀ ℕ) := by
      ext i
      simpa using ht0 i
    have : (C c : MvPolynomial (Fin n) F).coeff (Finsupp.equivFunOnFinite.symm t) = c := by
      rw [hmon0, coeff_C, if_pos rfl]
    rwa [this] at hcoeff
  have hS : ∀ i, (S i).Nonempty := by
    intro i
    exact Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le (t i)) (hcard i))
  refine ⟨fun i => Classical.choose (hS i), fun i => Classical.choose_spec (hS i), ?_⟩
  simpa [eval_C] using hc

/-! ## Level B: namesake non-vanishing form (Alon 1999, Theorem 1.2) -/

/-- Alon 1999 combinatorial Nullstellensatz, **non-vanishing form**. Formalize-only;
**no novelty claim**. Not Hilbert NS, not Chevalley–Warning, not EGZ. -/
theorem combinatorial_nullstellensatz {n : ℕ}
    (f : MvPolynomial (Fin n) F) (t : Fin n → ℕ) (S : Fin n → Finset F)
    (hdeg : ∀ i, f.degreeOf i ≤ t i) (hcard : ∀ i, t i < (S i).card)
    (hcoeff : f.coeff (Finsupp.equivFunOnFinite.symm t) ≠ 0) :
    ∃ x : Fin n → F, (∀ i, x i ∈ S i) ∧ eval x f ≠ 0 := by
  induction n with
  | zero =>
    exact combinatorial_nullstellensatz_zero f t S hcoeff
  | succ n ih =>
    let t' : Fin n → ℕ := fun i => t i.succ
    let S' : Fin n → Finset F := fun i => S i.succ
    let g : MvPolynomial (Fin n) F := (finSuccEquiv F n f).coeff (t 0)
    have hdeg' : ∀ i, g.degreeOf i ≤ t' i := fun i =>
      degreeOf_coeff_finSuccEquiv_le f (t 0) i (hdeg i.succ)
    have hcard' : ∀ i, t' i < (S' i).card := fun i => hcard i.succ
    have hcoeff' : g.coeff (Finsupp.equivFunOnFinite.symm t') ≠ 0 := by
      have hmon := monomial_eq_cons t
      have : f.coeff (Finsupp.cons (t 0) (Finsupp.equivFunOnFinite.symm t')) ≠ 0 := by
        rwa [← hmon]
      rwa [finSuccEquiv_coeff_coeff]
    obtain ⟨x', hx', hgx'⟩ := ih g t' S' hdeg' hcard' hcoeff'
    let p : Polynomial F := Polynomial.map (eval x') (finSuccEquiv F n f)
    have hdegP : p.natDegree ≤ t 0 :=
      (Polynomial.natDegree_map_le _ _).trans (natDegree_finSuccEquiv_le f (hdeg 0))
    have hcoeffP : p.coeff (t 0) ≠ 0 := by
      have : p.coeff (t 0) = eval x' g := Polynomial.coeff_map _ _
      rwa [this]
    obtain ⟨y, hyS, hy⟩ := univariate_nonvanishing p (t 0) (S 0) hdegP (hcard 0) hcoeffP
    refine ⟨Fin.cons y x', ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ ?_ i
      · simpa using hyS
      · intro j
        simpa using hx' j
    · have hmap : eval (Fin.cons y x') f = p.eval y := eval_eq_eval_mv_eval' x' y f
      rwa [hmap]

end ProofLab.CombinatorialNullstellensatz
