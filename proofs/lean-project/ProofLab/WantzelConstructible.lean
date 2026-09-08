/-
Wantzel cube-doubling obstruction — Level A only (Eisenstein
irreducibility of X³ − 2 / AdjoinRoot finrank 3 / 3 ≠ 2^k).
**Not labelled Wantzel / IsConstructible.**

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 pin `a719ba5c3115` has `minpoly` /
`irreducible_of_eisenstein_criterion` / `IntermediateField` /
`AdjoinRoot` / `finrank` as **infra**. ZERO named Wantzel /
`IsConstructible` / `doubling_the_cube` / `constructible` /
`trisect` under `Mathlib/` or `Archive/` or `ProofLab/`.
Completing the Level A Eisenstein + adjoin-degree + 2-power
obstruction glue is the gap this ticket lands. The Level B
namesake `IsConstructible` as a quadratic `IntermediateField`
tower ⇒ minpoly degree is a 2-power is **out of this ticket**
and is **not** sorry-ed. Angle trisection / full Euclidean
geometry / Galois extras are residual of this id.

Pin: `catalog/problems/wantzel-constructible/STATEMENT.md`
(OPE-1211; Scout OPE-1200 leftover; Director OPE-1210).
Encoding: `AdjoinRoot` of `(X ^ 3 - C 2 : ℚ[X])`. Work in
`AdjoinRoot` (do **not** require a real cube-root). Zero
`sorry`. Do not import `Archive.*`.

This is **not** Abel–Ruffini / `IsSolvableByRad`
(`FieldTheory/AbelRuffini.lean` L194) — already Mathlib; a
different theorem (radicals vs quadratic towers). Do **not**
re-prove; do **not** import `Archive.*`.
This is **not** Eisenstein as namesake
(`irreducible_of_eisenstein_criterion`, EisensteinCriterion.lean
L82) — **USE as glue** for `X³ − 2`; do not re-prove.
This is **not** `minpoly` uniqueness / `AdjoinRoot` /
`finrank_mul_finrank` — already Mathlib; USE, do not re-prove.
This is **not** primitive element / Galois correspondence /
Noether Level B (`ProofLab/NoetherNormalization.lean`).
This is **not** angle trisection (the other half of Wiedijk
100.yaml #8) — residual of this id.
This is **not** FTA / rational-root / Gauss lemma as namesake
(Gauss / Eisenstein are glue).
This is **not** circulant-det (`ProofLab/CirculantDet.lean`,
PR #132). This is **not** Schur product (PR #129). This is
**not** Lamé (PR #130). Do not re-prime the consumed mill.
Leave OPE-403 alone. Leave OPE-1195 alone.

v1 is `AdjoinRoot (X ^ 3 - C 2 : ℚ[X])`. `ℚ` / Eisenstein /
`AdjoinRoot` / `finrank` are load-bearing for Level A.

Level A: `X³ − 2` is Eisenstein at the prime ideal `(2)`
(`irreducible_of_eisenstein_criterion` USE, not re-proved).
`AdjoinRoot` of an irreducible degree-3 polynomial has
`finrank 3`. `3 ≠ 2^k` by unique factorisation / a one-line
induction. **Not** labelled Wantzel.

Transcribed classical argument (Wantzel 1837,
J. Math. Pures Appl. 2). Compact form: Wikipedia
*Wantzel's theorem* / doubling the cube. Wiedijk 100
theorems #8 (no Mathlib `decl` this pin). Type pin:
`minpoly` / Eisenstein / `AdjoinRoot` / `ℚ`. Abel–Ruffini
is a different already-in theorem. Angle trisection is the
other half of #8 (residual). No novelty claim. Default no
claim.
-/
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.EisensteinCriterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Tactic

set_option linter.unusedVariables false

open Polynomial Ideal FiniteDimensional

open scoped Polynomial

noncomputable section

namespace ProofLab.WantzelConstructible

/-! ## Level A: Eisenstein X³−2 / AdjoinRoot finrank 3 / 3≠2^k
(not labelled Wantzel / IsConstructible) -/

/-- Integer polynomial `X³ − 2`. Glue for Eisenstein at `(2)`;
**not** labelled Wantzel. -/
def xPowThreeSubTwoInt : ℤ[X] :=
  X ^ 3 - C 2

/-- Mapping `X³ − 2` along `ℤ → ℚ`. Glue; **not** labelled
Wantzel. -/
lemma map_xPowThreeSubTwoInt :
    (X ^ 3 - C 2 : ℚ[X]) = xPowThreeSubTwoInt.map (Int.castRingHom ℚ) := by
  simp [xPowThreeSubTwoInt]

lemma monic_xPowThreeSubTwoInt : xPowThreeSubTwoInt.Monic :=
  monic_X_pow_sub_C (2 : ℤ) three_ne_zero

lemma primitive_xPowThreeSubTwoInt : xPowThreeSubTwoInt.IsPrimitive :=
  monic_xPowThreeSubTwoInt.isPrimitive

lemma degree_xPowThreeSubTwoInt : xPowThreeSubTwoInt.degree = 3 :=
  degree_X_pow_sub_C (n := 3) (Nat.succ_pos 2) (2 : ℤ)

/-- Coefficients of `X³ − 2` over `ℤ`. Glue; **not** labelled
Wantzel. -/
lemma coeff_xPowThreeSubTwoInt (n : ℕ) :
    xPowThreeSubTwoInt.coeff n =
      if n = 3 then 1 else if n = 0 then (-2 : ℤ) else 0 := by
  simp only [xPowThreeSubTwoInt, coeff_sub, coeff_X_pow, coeff_C]
  split_ifs with h3 h0 <;> omega

/-- `X³ − 2` is irreducible over `ℚ` via Eisenstein at `(2)`
and Gauss's lemma. Uses `irreducible_of_eisenstein_criterion`
and `IsPrimitive.Int.irreducible_iff_irreducible_map_cast`;
does **not** re-prove them. Glue; **not** labelled Wantzel. -/
theorem two_ne_zero_int : (2 : ℤ) ≠ 0 :=
  Int.natCast_ne_zero.mpr (Nat.succ_ne_zero 1)

theorem two_not_dvd_one_int : ¬ (2 : ℤ) ∣ 1 :=
  (Nat.prime_iff_prime_int.mp Nat.prime_two).not_dvd_one

theorem four_not_dvd_two_nat : ¬ (4 : ℕ) ∣ 2 :=
  Nat.not_dvd_of_pos_of_lt (Nat.succ_pos 1)
    (Nat.lt_of_succ_lt (Nat.lt_succ_self 3))

theorem irreducible_X_pow_three_sub_two :
    Irreducible (X ^ 3 - C 2 : ℚ[X]) := by
  rw [map_xPowThreeSubTwoInt,
    ← IsPrimitive.Int.irreducible_iff_irreducible_map_cast
      primitive_xPowThreeSubTwoInt]
  refine irreducible_of_eisenstein_criterion
    (P := span ({(2 : ℤ)} : Set ℤ)) ?hP ?hfl ?hfP ?hfd0 ?h0
    primitive_xPowThreeSubTwoInt
  · rw [span_singleton_prime two_ne_zero_int]
    exact Nat.prime_iff_prime_int.mp Nat.prime_two
  · rw [monic_xPowThreeSubTwoInt.leadingCoeff, mem_span_singleton]
    exact two_not_dvd_one_int
  · intro n hn
    rw [degree_xPowThreeSubTwoInt] at hn
    have hn' : n < 3 := by exact_mod_cast hn
    rw [mem_span_singleton, coeff_xPowThreeSubTwoInt]
    interval_cases n
    · exact dvd_neg.mpr (dvd_refl (2 : ℤ))
    · exact dvd_zero _
    · exact dvd_zero _
  · rw [degree_xPowThreeSubTwoInt]
    exact WithBot.coe_lt_coe.mpr (Nat.succ_pos 2)
  · rw [coeff_xPowThreeSubTwoInt, if_neg (Nat.zero_ne_add_one 2),
      if_pos rfl, span_singleton_pow, mem_span_singleton]
    intro h
    have h4 : (4 : ℕ) ∣ 2 :=
      Int.natCast_dvd_natCast.mp (by
        simpa using (dvd_neg.mp h : ((2 : ℤ) ^ 2) ∣ 2))
    exact four_not_dvd_two_nat h4

/-- `AdjoinRoot` of `X³ − 2` over `ℚ` has `finrank 3`.
Uses `AdjoinRoot.powerBasis` / `PowerBasis.finrank` /
`natDegree_X_pow_sub_C`; does **not** re-prove them.
Does **not** require a real cube-root. Glue; **not**
labelled Wantzel. -/
theorem adjoinRoot_X_pow_three_sub_two_finrank :
    finrank ℚ (AdjoinRoot (X ^ 3 - C 2 : ℚ[X])) = 3 := by
  have hf : (X ^ 3 - C 2 : ℚ[X]) ≠ 0 :=
    X_pow_sub_C_ne_zero (Nat.succ_pos 2) (2 : ℚ)
  trans (AdjoinRoot.powerBasis hf).dim
  · exact (AdjoinRoot.powerBasis hf).finrank
  · change (X ^ 3 - C (2 : ℚ)).natDegree = 3
    exact natDegree_X_pow_sub_C

/-- `3` is not a power of `2`. Unique factorisation / one-line
induction. **Not** labelled Wantzel. -/
theorem not_pow_two_three : ∀ k : ℕ, 3 ≠ 2 ^ k := by
  intro k
  cases k with
  | zero =>
    exact Nat.succ_ne_succ.mpr (Nat.succ_ne_zero 1)
  | succ k =>
    intro h
    have hdiv : 2 ∣ 3 := by
      rw [h]
      exact dvd_pow_self 2 (Nat.succ_ne_zero k)
    have heq : 2 = 3 :=
      (Nat.prime_dvd_prime_iff_eq Nat.prime_two Nat.prime_three).mp hdiv
    exact (Nat.succ_ne_succ.mpr
      (Nat.succ_ne_succ.mpr (Nat.succ_ne_zero 0))) heq.symm

/- Residual of this id (comment, **not** `sorry`):
Level B namesake `IsConstructible` — finite tower of
`IntermediateField`s each of relative degree `≤ 2`, hence
minpoly degree is a power of `2`; then any root of `X³ − 2`
is not constructible. Angle trisection / full Euclidean
constructible points / Galois correspondence extras. Out of
this ticket. Do **not** prove Abel–Ruffini / `IsSolvableByRad`
/ primitive element. Cube-doubling-as-namesake beyond this
Eisenstein `X³ − 2` Level A slice is residual. -/

end ProofLab.WantzelConstructible
