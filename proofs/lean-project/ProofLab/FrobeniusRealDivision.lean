/-
Frobenius theorem on real division algebras, Level A only (finrank ∈ {1,2,4}).
Formalize-only — **no novelty claim**, **default no claim**.

status: known-classical, formalize-only.
Mathlib v4.10.0 pin `a719ba5c3115` has `Quaternion` / `DivisionRing ℍ[R]` /
`Quaternion.finrank_eq_four`, `Complex.finrank_real_complex`, `Complex.liftAux`,
`Irreducible.natDegree_le_two` on `ℝ[X]`, `minpoly`, `IsAlgClosed ℂ`, and
`IsAlgClosed.algebraMap_surjective_of_isIntegral`. ZERO named real-division
classification / `finrank ∈ {1,2,4}` theorem under `Mathlib/` or `Archive/`.
Completing the rank trichotomy is the gap. Do **not** import `Archive.*`.
Do **not** import `GroupTheory.SpecificGroups.Quaternion` (that is `Q₈`).

Pin: `catalog/problems/frobenius-real-division/STATEMENT.md` (OPE-1067;
Scout OPE-1062 RECOMMENDED PRIME; Director OPE-1066). Encoding: Mathlib
`DivisionRing` + `Algebra ℝ D` + `FiniteDimensional ℝ D`. Zero `sorry`.
Do **not** label the theorem Frobenius. Level B namesake `AlgEquiv` is
**out of this ticket**, not sorry-ed.

This is **not** Gelfand–Mazur (`NormedRing.algEquivComplexOfComplete`,
already Mathlib; complex Banach; different theorem).
This is **not** Artin–Wedderburn (`proof_wanted`; leftover-risk; do not prove).
This is **not** Hurwitz 1-2-4-8 / octonions (non-associative leftover class).
This is **not** the Frobenius coin problem (`ProofLab/Frobenius.lean`;
already Mathlib `frobeniusNumber_pair`).
This is **not** the Frobenius endomorphism.
This is **not** Mason–Stothers / expander-mixing / krenn-gu / hou-zeng-pfc /
sun-135 / noether-normalization. Leave OPE-403 alone.

Level A (this module, **not** labelled Frobenius): Palais AMM 1968.
`ℝ ⊆ Z(D)`. Rank 1 iff `algebraMap ℝ D` is surjective. Otherwise a
non-real element has minpoly degree 2; complete the square to get `i`
with `i² = -1`. Conjugation by `i` is an involution; the `+1` space is
the centralizer, a finite-dimensional domain over `ℂ` via `Complex.liftAux`,
hence rank 2 by `IsAlgClosed.algebraMap_surjective_of_isIntegral` and
`Complex.finrank_real_complex`. If the `-1` space vanishes, rank 2;
otherwise right-multiplication by a nonzero anticommuting element
identifies the two eigenspaces, so rank 4.
Level B namesake `frobenius_real_division` (`D ≃ₐ[ℝ] ℝ` or `ℂ` or `ℍ[ℝ]`)
is **out of this ticket**. Honest residual, not `sorry`.

Transcribed classical Frobenius 1878 / Palais, *The classification of
real division algebras*, Amer. Math. Monthly 75 (1968) 366–368.
No novelty claim. Default no claim.
-/
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Algebra.Quaternion
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.FiniteDimensional
import Mathlib.Data.Complex.Module
import Mathlib.Data.Real.Sqrt
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.Tower
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.Tactic
import Mathlib.Tactic.NoncommRing

set_option linter.unusedVariables false
set_option maxHeartbeats 800000

open FiniteDimensional Polynomial Submodule
open scoped Classical

noncomputable section

namespace ProofLab.FrobeniusRealDivision

/-! ## Glue (already-upstream ranks; not labelled Frobenius) -/

/-- Mathlib `Complex.finrank_real_complex`. Glue, **not** labelled Frobenius.
Do **not** re-prove. -/
theorem complex_finrank_glue : finrank ℝ ℂ = 2 :=
  Complex.finrank_real_complex

/-- Mathlib `Quaternion.finrank_eq_four`. Glue, **not** labelled Frobenius.
Do **not** re-prove. Use `Quaternion ℝ`, not the `Q₈` group. -/
theorem quaternion_finrank_glue : finrank ℝ (Quaternion ℝ) = 4 :=
  Quaternion.finrank_eq_four

variable {D : Type*} [DivisionRing D] [Algebra ℝ D] [FiniteDimensional ℝ D]

/-! ## Rank 1 (algebraMap surjective) -/

theorem finrank_eq_one_of_algebraMap_surjective
    (h : Function.Surjective (algebraMap ℝ D)) : finrank ℝ D = 1 := by
  have hspan : (⊤ : Submodule ℝ D) = span ℝ {(1 : D)} := by
    refine le_antisymm ?_ le_top
    intro x _
    obtain ⟨r, rfl⟩ := h x
    rw [Algebra.algebraMap_eq_smul_one]
    exact smul_mem _ _ (mem_span_singleton_self _)
  have h1 : (1 : D) ≠ 0 := one_ne_zero
  rw [← finrank_top, hspan, finrank_span_singleton h1]

/-! ## Completing the square: a non-real element yields `i² = -1` -/

lemma minpoly_natDegree_eq_two_of_not_mem_range {a : D}
    (ha : a ∉ Set.range (algebraMap ℝ D)) :
    (minpoly ℝ a).natDegree = 2 := by
  have hint : IsIntegral ℝ a := IsIntegral.of_finite ℝ a
  have hle : (minpoly ℝ a).natDegree ≤ 2 :=
    (minpoly.irreducible hint).natDegree_le_two
  have hge : 2 ≤ (minpoly ℝ a).natDegree :=
    (minpoly.two_le_natDegree_iff hint).2 ha
  exact le_antisymm hle hge

lemma monic_natDegree_two_form {p : ℝ[X]} (hm : p.Monic) (hd : p.natDegree = 2) :
    p = X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) := by
  ext n
  match n with
  | 0 =>
    simp [coeff_add, coeff_X_pow, coeff_C_mul, coeff_C, coeff_X]
  | 1 =>
    simp [coeff_add, coeff_X_pow, coeff_C_mul, coeff_C, coeff_X]
  | 2 =>
    have hlead : p.coeff 2 = 1 := by
      simpa [hd] using hm.coeff_natDegree
    simp [coeff_add, coeff_X_pow, coeff_C_mul, coeff_C, coeff_X, hlead]
  | n + 3 =>
    have : p.coeff (n + 3) = 0 :=
      coeff_eq_zero_of_natDegree_lt (by omega)
    simp [coeff_add, coeff_X_pow, coeff_C_mul, coeff_C, coeff_X, this]

lemma aeval_quadratic (a : D) {p q : ℝ} {f : ℝ[X]}
    (hf : f = X ^ 2 + C p * X + C q) :
    aeval a f = a * a + algebraMap ℝ D p * a + algebraMap ℝ D q := by
  subst hf
  simp [aeval_add, aeval_mul, Algebra.smul_def, pow_two]

lemma sq_add_halves (a : D) (p q : ℝ)
    (haeval : a * a + algebraMap ℝ D p * a + algebraMap ℝ D q = 0) :
    let t : D := a + algebraMap ℝ D (p / 2)
    t * t = algebraMap ℝ D (p ^ 2 / 4 - q) := by
  intro t
  set c := algebraMap ℝ D (p / 2)
  have hca : a * c = c * a := (Algebra.commutes (p / 2) a).symm
  have h2c : c + c = algebraMap ℝ D p := by
    rw [← map_add, add_halves]
  have hcc : c * c = algebraMap ℝ D (p ^ 2 / 4) := by
    rw [← map_mul]
    congr 1
    ring
  have hneg : a * a + algebraMap ℝ D p * a = -algebraMap ℝ D q :=
    add_eq_zero_iff_eq_neg.mp haeval
  have hexpand : (a + c) * (a + c) = a * a + a * c + c * a + c * c := by
    rw [add_mul, mul_add, mul_add]
    abel
  have : t * t = a * a + algebraMap ℝ D p * a + algebraMap ℝ D (p ^ 2 / 4) := by
    change (a + c) * (a + c) = _
    rw [hexpand, hca, add_assoc (a * a), ← add_mul, h2c, hcc]
  rw [this, hneg, map_sub, add_comm (-algebraMap ℝ D q), ← sub_eq_add_neg]

lemma mem_range_of_sq_eq_algebraMap {t : D} {r : ℝ} (hr : 0 ≤ r)
    (ht : t * t = algebraMap ℝ D r) :
    t ∈ Set.range (algebraMap ℝ D) := by
  set s := Real.sqrt r
  have hs : s * s = r := Real.mul_self_sqrt hr
  have hcent : t * algebraMap ℝ D s = algebraMap ℝ D s * t :=
    (Algebra.commutes s t).symm
  have hfac : (t - algebraMap ℝ D s) * (t + algebraMap ℝ D s) =
      t * t - algebraMap ℝ D s * algebraMap ℝ D s := by
    have h1 : t * algebraMap ℝ D s = algebraMap ℝ D s * t := hcent
    rw [sub_mul, mul_add, mul_add, h1, sub_add_eq_sub_sub]
    abel
  have hfac0 : (t - algebraMap ℝ D s) * (t + algebraMap ℝ D s) = 0 := by
    rw [hfac, ht, ← map_mul, hs, sub_self]
  rcases eq_zero_or_eq_zero_of_mul_eq_zero hfac0 with h | h
  · exact ⟨s, (sub_eq_zero.mp h).symm⟩
  · refine ⟨-s, ?_⟩
    have : t = -algebraMap ℝ D s := add_eq_zero_iff_eq_neg.mp h
    simpa [map_neg] using this.symm

theorem exists_sq_eq_neg_one (h : ¬ Function.Surjective (algebraMap ℝ D)) :
    ∃ i : D, i * i = -1 := by
  obtain ⟨a, ha⟩ : ∃ a : D, a ∉ Set.range (algebraMap ℝ D) := by
    contrapose! h
    exact h
  have hint : IsIntegral ℝ a := IsIntegral.of_finite ℝ a
  have hm : (minpoly ℝ a).Monic := minpoly.monic hint
  have hd : (minpoly ℝ a).natDegree = 2 :=
    minpoly_natDegree_eq_two_of_not_mem_range ha
  set p := (minpoly ℝ a).coeff 1
  set q := (minpoly ℝ a).coeff 0
  have hform : minpoly ℝ a = X ^ 2 + C p * X + C q :=
    monic_natDegree_two_form hm hd
  have haeval : a * a + algebraMap ℝ D p * a + algebraMap ℝ D q = 0 := by
    have := minpoly.aeval ℝ a
    rwa [aeval_quadratic a hform] at this
  set t : D := a + algebraMap ℝ D (p / 2)
  have ht2 : t * t = algebraMap ℝ D (p ^ 2 / 4 - q) :=
    sq_add_halves a p q haeval
  set r : ℝ := p ^ 2 / 4 - q
  change t * t = algebraMap ℝ D r at ht2
  by_cases hr : 0 ≤ r
  · have htR : t ∈ Set.range (algebraMap ℝ D) :=
      mem_range_of_sq_eq_algebraMap hr ht2
    obtain ⟨s, hs⟩ := htR
    have : a ∈ Set.range (algebraMap ℝ D) := by
      refine ⟨s - p / 2, ?_⟩
      have haeq : a = t - algebraMap ℝ D (p / 2) := by
        change a = a + algebraMap ℝ D (p / 2) - algebraMap ℝ D (p / 2)
        simp
      rw [haeq, ← hs, map_sub]
    exact (ha this).elim
  · have hrneg : r < 0 := lt_of_not_ge hr
    set δ := Real.sqrt (-r)
    have hδpos : 0 < δ := Real.sqrt_pos.2 (neg_pos.mpr hrneg)
    have hδ : δ ≠ 0 := hδpos.ne'
    have hδsq : δ * δ = -r := Real.mul_self_sqrt (le_of_lt (neg_pos.mpr hrneg))
    refine ⟨(δ⁻¹ : ℝ) • t, ?_⟩
    have hsmul :
        ((δ⁻¹ : ℝ) • t) * ((δ⁻¹ : ℝ) • t) = algebraMap ℝ D (δ⁻¹ * δ⁻¹ * r) := by
      rw [smul_mul_smul, ht2, Algebra.algebraMap_eq_smul_one, smul_smul,
        Algebra.algebraMap_eq_smul_one]
    have hval : δ⁻¹ * δ⁻¹ * r = -1 := by
      field_simp [hδ]
      nlinarith [hδsq]
    rw [hsmul, hval, map_neg, map_one]

/-! ## Conjugation involution -/

def conjL (i : D) : D →ₗ[ℝ] D :=
  LinearMap.mulLeftRight ℝ (-i, i)

lemma conjL_apply (i x : D) : conjL i x = (-i) * x * i :=
  rfl

lemma mul_neg_i_of_sq (i : D) (hi : i * i = -1) : i * (-i) = 1 := by
  rw [mul_neg, hi, neg_neg]

lemma neg_i_mul_of_sq (i : D) (hi : i * i = -1) : (-i) * i = 1 := by
  rw [neg_mul, hi, neg_neg]

lemma conjL_mul (i x y : D) (hi : i * i = -1) :
    conjL i (x * y) = conjL i x * conjL i y := by
  have hii : i * (-i) = 1 := mul_neg_i_of_sq i hi
  simp only [conjL_apply]
  symm
  calc
    ((-i) * x * i) * ((-i) * y * i)
        = (-i) * x * (i * (-i)) * y * i := by
          simp only [mul_assoc]
    _ = (-i) * x * (1 : D) * y * i := by rw [hii]
    _ = (-i) * (x * y) * i := by simp only [mul_assoc, mul_one]

lemma conjL_involutive (i : D) (hi : i * i = -1) (x : D) :
    conjL i (conjL i x) = x := by
  have hneg : (-i) * (-i) = -1 := by
    rw [neg_mul_neg, hi]
  simp only [conjL_apply]
  calc
    (-i) * ((-i) * x * i) * i
        = ((-i) * (-i)) * x * (i * i) := by simp only [mul_assoc]
    _ = (-1 : D) * x * (-1) := by rw [hneg, hi]
    _ = x := by simp

lemma conjL_eq_self_iff (i x : D) (hi : i * i = -1) :
    conjL i x = x ↔ i * x = x * i := by
  have hii : i * (-i) = 1 := mul_neg_i_of_sq i hi
  have hii' : (-i) * i = 1 := neg_i_mul_of_sq i hi
  constructor
  · intro hx
    have := congrArg (fun z : D => i * z) hx
    simp only [conjL_apply] at this
    calc
      i * x = i * ((-i) * x * i) := this.symm
      _ = (i * (-i)) * x * i := by simp only [mul_assoc]
      _ = x * i := by rw [hii, one_mul]
  · intro hx
    simp only [conjL_apply]
    calc
      (-i) * x * i = (-i) * (i * x) := by rw [hx]; simp only [mul_assoc]
      _ = ((-i) * i) * x := by simp only [mul_assoc]
      _ = x := by rw [hii', one_mul]

lemma conjL_eq_neg_iff (i x : D) (hi : i * i = -1) :
    conjL i x = -x ↔ i * x = -(x * i) := by
  have hii : i * (-i) = 1 := mul_neg_i_of_sq i hi
  constructor
  · intro hx
    have := congrArg (fun z : D => i * z) hx
    simp only [conjL_apply, mul_neg] at this
    have hxi : x * i = -(i * x) := by
      calc
        x * i = (i * (-i)) * x * i := by rw [hii, one_mul]
        _ = i * ((-i) * x * i) := by simp only [mul_assoc]
        _ = -(i * x) := this
    calc
      i * x = -(-(i * x)) := (neg_neg _).symm
      _ = -(x * i) := by rw [← hxi]
  · intro hx
    simp only [conjL_apply]
    calc
      (-i) * x * i = (-(i * x)) * i := by
          rw [neg_mul]
      _ = -((i * x) * i) := by rw [neg_mul]
      _ = -((-(x * i)) * i) := by rw [hx]
      _ = (x * i) * i := by simp [neg_mul]
      _ = x * (i * i) := by rw [mul_assoc]
      _ = -x := by rw [hi, mul_neg, mul_one]

/-! ## Plus / minus eigenspaces -/

abbrev centralizerI (i : D) : Subalgebra ℝ D :=
  Subalgebra.centralizer ℝ ({i} : Set D)

def minus (i : D) : Submodule ℝ D :=
  LinearMap.ker (conjL i + LinearMap.id)

lemma mem_centralizerI_iff {i x : D} :
    x ∈ centralizerI i ↔ i * x = x * i := by
  simp [centralizerI, Subalgebra.mem_centralizer_iff]

lemma mem_minus_iff {i x : D} : x ∈ minus i ↔ conjL i x = -x := by
  simp [minus, LinearMap.mem_ker, add_eq_zero_iff_eq_neg]

lemma liftAux_mem_centralizer (i : D) (hi : i * i = -1) (z : ℂ) :
    Complex.liftAux i hi z ∈ centralizerI i := by
  rw [mem_centralizerI_iff]
  simp only [Complex.liftAux_apply, add_mul, mul_add]
  have hc : algebraMap ℝ D z.re * i = i * algebraMap ℝ D z.re :=
    Algebra.commutes _ _
  have him : (z.im • i) * i = i * (z.im • i) := by
    rw [smul_mul_assoc, mul_smul_comm]
  rw [hc, him]

def liftCentralizer (i : D) (hi : i * i = -1) :
    ℂ →ₐ[ℝ] ↥(centralizerI i) :=
  (Complex.liftAux i hi).codRestrict (centralizerI i)
    (liftAux_mem_centralizer i hi)

lemma algebraMap_injective_real :
    Function.Injective (algebraMap ℝ D) :=
  NoZeroSMulDivisors.algebraMap_injective ℝ D

lemma one_not_eq_smul_of_sq_neg_one {i : D} (hi : i * i = -1) (r : ℝ) :
    i ≠ algebraMap ℝ D r := by
  intro h
  have : algebraMap ℝ D (r * r) = algebraMap ℝ D (-1) := by
    rw [map_mul, ← h, hi, map_neg, map_one]
  have hr : r * r = -1 := algebraMap_injective_real this
  nlinarith [sq_nonneg r]

lemma linearIndependent_one_i {i : D} (hi : i * i = -1) :
    LinearIndependent ℝ ![ (1 : D), i ] := by
  refine (LinearIndependent.pair_iff' (one_ne_zero : (1 : D) ≠ 0)).2 ?_
  intro r hr
  have : i = algebraMap ℝ D r := by
    simpa [Algebra.algebraMap_eq_smul_one] using hr.symm
  exact one_not_eq_smul_of_sq_neg_one hi r this

lemma span_one_i_le_centralizer {i : D} (hi : i * i = -1) :
    span ℝ ({(1 : D), i} : Set D) ≤ Subalgebra.toSubmodule (centralizerI i) := by
  rw [span_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact (mem_centralizerI_iff).2 (by rw [mul_one, one_mul])
  · exact (mem_centralizerI_iff).2 rfl

lemma lift_commutes (i : D) (hi : i * i = -1)
    (c : ℂ) (x : ↥(centralizerI i)) :
    liftCentralizer i hi c * x = x * liftCentralizer i hi c := by
  apply Subtype.ext
  have hx : (x : D) ∈ centralizerI i := x.property
  have hiC : i * (x : D) = (x : D) * i := (mem_centralizerI_iff).1 hx
  have h1 : algebraMap ℝ D c.re * (x : D) = (x : D) * algebraMap ℝ D c.re :=
    Algebra.commutes _ _
  have him : (c.im • i) * (x : D) = (x : D) * (c.im • i) := by
    simp only [Algebra.smul_def, mul_assoc]
    rw [hiC, ← mul_assoc, ← mul_assoc, Algebra.commutes c.im (x : D)]
  simp only [liftCentralizer, AlgHom.codRestrict, Complex.liftAux_apply]
  change (algebraMap ℝ D c.re + c.im • i) * (x : D) =
    (x : D) * (algebraMap ℝ D c.re + c.im • i)
  rw [add_mul, mul_add, h1, him]

/-- The centralizer of an element with `i² = -1` is 2-dimensional over `ℝ`,
via `Complex.liftAux` + algebraic closure of `ℂ`. Not labelled Frobenius. -/
theorem finrank_centralizer (i : D) (hi : i * i = -1) :
    finrank ℝ (centralizerI i) = 2 := by
  set C := centralizerI i
  let φ : ℂ →ₐ[ℝ] ↥C := liftCentralizer i hi
  letI instAlg : Algebra ℂ ↥C :=
    (φ : ℂ →+* ↥C).toAlgebra' (lift_commutes i hi)
  have hφ (z : ℂ) : algebraMap ℂ ↥C z = φ z := rfl
  haveI : IsScalarTower ℝ ℂ ↥C := IsScalarTower.of_algebraMap_eq fun r => by
    apply Subtype.ext
    -- algebraMap ℝ C r = algebraMap ℂ C (algebraMap ℝ ℂ r)
    change (algebraMap ℝ D r) = (algebraMap ℂ ↥C (algebraMap ℝ ℂ r) : D)
    rw [hφ]
    simp [liftCentralizer, Complex.liftAux_apply]
  haveI : FiniteDimensional ℂ ↥C := FiniteDimensional.right ℝ ℂ ↥C
  haveI : Algebra.IsIntegral ℂ ↥C := inferInstance
  have hsurj : Function.Surjective (algebraMap ℂ ↥C) :=
    IsAlgClosed.algebraMap_surjective_of_isIntegral (k := ℂ) (K := ↥C)
  have hinj : Function.Injective φ.toLinearMap := by
    have : Function.Injective (algebraMap ℂ ↥C) :=
      NoZeroSMulDivisors.algebraMap_injective ℂ ↥C
    intro x y hxy
    simpa [hφ] using this (by simpa [hφ] using hxy)
  have hsurj' : Function.Surjective φ.toLinearMap := by
    intro y
    obtain ⟨z, hz⟩ := hsurj y
    exact ⟨z, by simpa [hφ] using hz⟩
  have e : ℂ ≃ₗ[ℝ] ↥C :=
    LinearEquiv.ofBijective φ.toLinearMap ⟨hinj, hsurj'⟩
  simpa [complex_finrank_glue] using (LinearEquiv.finrank_eq e).symm

lemma isCompl_centralizer_minus (i : D) (hi : i * i = -1) :
    IsCompl (Subalgebra.toSubmodule (centralizerI i)) (minus i) := by
  constructor
  · rw [disjoint_iff, eq_bot_iff]
    intro x hx
    have hxC : x ∈ centralizerI i := by
      have : x ∈ Subalgebra.toSubmodule (centralizerI i) := (mem_inf.mp hx).1
      exact this
    have hxM : x ∈ minus i := (mem_inf.mp hx).2
    have hplus : conjL i x = x := (conjL_eq_self_iff i x hi).2
      ((mem_centralizerI_iff).1 hxC)
    have hminus : conjL i x = -x := (mem_minus_iff).1 hxM
    have : (2 : ℝ) • x = 0 := by
      have hx2 : x + x = 0 := by
        calc
          x + x = conjL i x + x := by rw [hplus]
          _ = -x + x := by rw [hminus]
          _ = 0 := add_left_neg x
      rw [two_smul]
      exact hx2
    have hx0 : x = 0 := (smul_eq_zero.mp this).resolve_left two_ne_zero
    rw [hx0]
    exact zero_mem _
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have hxsplit :
        x = (2⁻¹ : ℝ) • (x + conjL i x) + (2⁻¹ : ℝ) • (x - conjL i x) := by
      have h2 : (2 : ℝ) ≠ 0 := two_ne_zero
      rw [← smul_add]
      have hx2 : (x + conjL i x) + (x - conjL i x) = x + x := by abel
      rw [hx2, ← two_smul ℝ x, smul_smul, inv_mul_cancel h2, one_smul]
    refine (mem_sup).2
      ⟨(2⁻¹ : ℝ) • (x + conjL i x), ?_, (2⁻¹ : ℝ) • (x - conjL i x), ?_,
        hxsplit.symm⟩
    · have hself : conjL i (x + conjL i x) = x + conjL i x := by
        rw [map_add, conjL_involutive i hi, add_comm]
      have : x + conjL i x ∈ centralizerI i :=
        (mem_centralizerI_iff).2 ((conjL_eq_self_iff i _ hi).1 hself)
      exact smul_mem _ _ this
    · have hneg : conjL i (x - conjL i x) = -(x - conjL i x) := by
        rw [map_sub, conjL_involutive i hi, neg_sub]
      exact smul_mem _ _ ((mem_minus_iff).2 hneg)

lemma mulRight_plus_to_minus {i j x : D} (hi : i * i = -1)
    (hx : x ∈ centralizerI i) (hj : j ∈ minus i) :
    x * j ∈ minus i := by
  have hx' : conjL i x = x :=
    (conjL_eq_self_iff i x hi).2 ((mem_centralizerI_iff).1 hx)
  have hj' : conjL i j = -j := (mem_minus_iff).1 hj
  refine (mem_minus_iff).2 ?_
  calc
    conjL i (x * j) = conjL i x * conjL i j := conjL_mul i x j hi
    _ = x * (-j) := by rw [hx', hj']
    _ = -(x * j) := by rw [mul_neg]

lemma mulRight_minus_to_plus {i j x : D} (hi : i * i = -1)
    (hx : x ∈ minus i) (hj : j ∈ minus i) :
    x * j ∈ centralizerI i := by
  have hx' : conjL i x = -x := (mem_minus_iff).1 hx
  have hj' : conjL i j = -j := (mem_minus_iff).1 hj
  have : conjL i (x * j) = x * j := by
    calc
      conjL i (x * j) = conjL i x * conjL i j := conjL_mul i x j hi
      _ = (-x) * (-j) := by rw [hx', hj']
      _ = x * j := by rw [neg_mul_neg]
  exact (mem_centralizerI_iff).2 ((conjL_eq_self_iff i (x * j) hi).1 this)

lemma mulRight_injective {j : D} (hj : j ≠ 0) :
    Function.Injective (LinearMap.mulRight ℝ j : D →ₗ[ℝ] D) := by
  intro x y hxy
  have : (x - y) * j = 0 := by
    have := congrArg (fun z : D => z - y * j) hxy
    simpa [sub_mul] using this
  exact sub_eq_zero.mp ((eq_zero_or_eq_zero_of_mul_eq_zero this).resolve_right hj)

theorem finrank_minus_of_ne_bot (i : D) (hi : i * i = -1) (hne : minus i ≠ ⊥) :
    finrank ℝ (minus i) = 2 := by
  obtain ⟨j, hj, hj0⟩ : ∃ j ∈ minus i, j ≠ 0 := by
    contrapose! hne
    ext x
    simp only [mem_bot]
    constructor
    · intro hx
      exact hne x hx
    · rintro rfl
      exact zero_mem _
  have hinj_right : Function.Injective (LinearMap.mulRight ℝ j) :=
    mulRight_injective hj0
  let fPlus :
      Subalgebra.toSubmodule (centralizerI i) →ₗ[ℝ] minus i :=
    LinearMap.restrict (LinearMap.mulRight ℝ j) fun x hx =>
      mulRight_plus_to_minus hi hx hj
  have hinjPlus : Function.Injective fPlus := by
    intro x y hxy
    exact Subtype.ext (hinj_right (congrArg Subtype.val hxy))
  let fMinus :
      minus i →ₗ[ℝ] Subalgebra.toSubmodule (centralizerI i) :=
    LinearMap.restrict (LinearMap.mulRight ℝ j) fun x hx =>
      mulRight_minus_to_plus hi hx hj
  have hinjMinus : Function.Injective fMinus := by
    intro x y hxy
    exact Subtype.ext (hinj_right (congrArg Subtype.val hxy))
  have hle₁ :
      finrank ℝ (Subalgebra.toSubmodule (centralizerI i)) ≤
        finrank ℝ (minus i) :=
    LinearMap.finrank_le_finrank_of_injective hinjPlus
  have hle₂ :
      finrank ℝ (minus i) ≤
        finrank ℝ (Subalgebra.toSubmodule (centralizerI i)) :=
    LinearMap.finrank_le_finrank_of_injective hinjMinus
  have h2 : finrank ℝ (centralizerI i) = 2 := finrank_centralizer i hi
  have h2' :
      finrank ℝ (Subalgebra.toSubmodule (centralizerI i)) = 2 := by
    simpa using h2
  linarith

/-! ## Level A (not labelled Frobenius) -/

/-- Finite-dimensional associative real division algebras have rank 1, 2, or 4.
Palais AMM 1968. **Not** labelled Frobenius. Level B namesake `AlgEquiv` is
out of this ticket (comment residual, not `sorry`). -/
theorem real_division_finrank_one_two_four :
    finrank ℝ D = 1 ∨ finrank ℝ D = 2 ∨ finrank ℝ D = 4 := by
  by_cases hsurj : Function.Surjective (algebraMap ℝ D)
  · exact Or.inl (finrank_eq_one_of_algebraMap_surjective hsurj)
  · obtain ⟨i, hi⟩ := exists_sq_eq_neg_one hsurj
    have hc : IsCompl (Subalgebra.toSubmodule (centralizerI i)) (minus i) :=
      isCompl_centralizer_minus i hi
    have hsum :
        finrank ℝ (Subalgebra.toSubmodule (centralizerI i)) +
          finrank ℝ (minus i) = finrank ℝ D :=
      Submodule.finrank_add_eq_of_isCompl hc
    have hplus : finrank ℝ (centralizerI i) = 2 := finrank_centralizer i hi
    have hplus' :
        finrank ℝ (Subalgebra.toSubmodule (centralizerI i)) = 2 := by
      simpa using hplus
    by_cases hbot : minus i = ⊥
    · right; left
      have : finrank ℝ (minus i) = 0 := by
        rw [hbot, finrank_bot]
      linarith
    · right; right
      have hminus : finrank ℝ (minus i) = 2 :=
        finrank_minus_of_ne_bot i hi hbot
      linarith

/-
Level B residual (out of this ticket, **not** sorry-ed):
`theorem frobenius_real_division` packaging the rank-1/2/4 cases as
`Nonempty (D ≃ₐ[ℝ] ℝ) ∨ Nonempty (D ≃ₐ[ℝ] ℂ) ∨ Nonempty (D ≃ₐ[ℝ] ℍ[ℝ])`
via `Complex.lift` / `QuaternionAlgebra.Basis.lift`. The rank trichotomy
does not by itself supply the `AlgEquiv`; that is the namesake leftover.
-/

end ProofLab.FrobeniusRealDivision
