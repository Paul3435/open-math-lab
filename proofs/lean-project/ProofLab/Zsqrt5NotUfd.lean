/-
Named small-factorization witnesses — Level A only
(`6 = 2 * 3` / `6 = (1+√-5)(1-√-5)` / `2 ∤ 1+√-5` / `2`
irreducible). **Not labelled Dedekind / Kummer / Gaussian.**

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 pin `a719ba5c3115` has `Zsqrtd` / prefix `ℤ√` /
`sqrtd` / `norm` / `norm_mul` / `norm_eq_zero_iff` /
`Irreducible` as **infra**. ZERO named `zsqrt5` / `not_ufd` /
`UniqueFactorizationMonoid (ℤ√` theorem under `Mathlib/` or
`Archive/` or `ProofLab/` (this run). Completing the Level A
named small-factorization witnesses is the gap this ticket
lands. The Level B namesake `zsqrt5_not_ufd`
(`¬ UniqueFactorizationMonoid (ℤ√(-5))`) is **out of this
ticket** and is **not** sorry-ed. Class number 2 / Dedekind
domain extras are residual of this id. Do **not** label
theorems `dedekind_*` / `kummer_*` / `gaussian_*` as this
factorization. Do **not** define the namesake via class group.

Pin: `catalog/problems/zsqrt5-not-ufd/STATEMENT.md`
(OPE-1380; Scout OPE-1374 prime; Director OPE-1379).
Encoding: `Zsqrt5 := ℤ√(-5)` via Mathlib `Zsqrtd.norm` /
`Irreducible`. Zero `sorry`. Do not import `Archive.*`.

This is **not** `Zsqrtd` / `norm` / `norm_mul` /
`Irreducible` — already Mathlib. **USE, do not re-prove;
do not cite as this non-UFD.**
This is **not** `EuclideanDomain ℤ[i]`
(`NumberTheory/Zsqrtd/GaussianInt.lean` L243). Different
ring `d = -1`. USE `Zsqrtd`; do **not** re-prove; do **not**
cite as this non-UFD.
This is **not** `Nat.Prime.sq_add_sq` (already-in two-square).
Do **not** re-prove; do **not** cite as non-UFD.
This is **not** four-square / three-square
(`ProofLab/LegendreThreeSquares.lean`, consumed #159).
Do **not** revive Gauss Eureka / three triangular numbers.
This is **not** Kummer `padicValNat_choose` (already-in).
This is **not** Myhill–Nerode (`ProofLab/MyhillNerode.lean`,
consumed #162). Do **not** revive Kleene regex iff DFA.
This is **not** Gray codes (`ProofLab/GrayCode.lean`,
consumed #163). Do **not** revive hypercube Hamiltonian.
This is **not** frobenius-real-division
(`ProofLab/FrobeniusRealDivision.lean`, consumed #105).
This is **not** `d8-ne-q8` (leftover of this shortlist).
Do **not** prove D8 ≇ Q8 here.
Do not re-prime the consumed mill. Leave OPE-403 alone.
Leave OPE-1195 alone.

v1 is named small-factorization witnesses: `6 = 2*3` and
`6 = (1+√-5)(1-√-5)` in `ℤ√(-5)`, 2 does not divide
`1+√-5`, and 2 is irreducible, **not labelled Dedekind /
Kummer / Gaussian**. The two products equal 6, and 2
irreducible-not-prime, are load-bearing (so Level A is
**not** "some elements of `Zsqrtd` multiply").

Level A: `six_two_three` / `six_split` /
`two_not_dvd_one_plus_sqrtd` / `two_irreducible`. Optional
extra: 3 irreducible / `⟨1,1⟩` irreducible / not associates.
**Not** labelled Dedekind / Kummer / Gaussian.

Transcribed classical argument (Dedekind / standard
quadratic-integer example). Compact form: Wikipedia
*Algebraic integer* / any ANT textbook on `ℤ[√-5]`.
Type pin: `ℤ√(-5)` / `Zsqrtd.norm` / `Irreducible`.
GaussianInt Euclidean is a different already-in ring.
Two-square is a different already-in theorem. D8 ≇ Q8 is
the leftover of this shortlist. No novelty claim.
Default no claim.
-/
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.Algebra.Associated.Basic
import Mathlib.Tactic

namespace ProofLab.Zsqrt5NotUfd

/-- Ring `ℤ[√-5]`. Glue; **not** labelled Dedekind. -/
abbrev Zsqrt5 := ℤ√(-5)

private lemma d_nonpos : (-5 : ℤ) ≤ 0 := by decide

private lemma d_neg : (-5 : ℤ) < 0 := by decide

private lemma norm_as_sq (z : Zsqrt5) :
    z.norm = z.re * z.re + 5 * (z.im * z.im) := by
  simp [Zsqrtd.norm]
  ring

private lemma mul_self_eq_zero_or_one_le (n : ℤ) :
    n * n = 0 ∨ 1 ≤ n * n := by
  have hsq : n * n = (n.natAbs : ℤ) ^ 2 := by
    rw [← sq, Int.natAbs_sq]
  rw [hsq, sq]
  have : n.natAbs = 0 ∨ 1 ≤ n.natAbs := by omega
  rcases this with h0 | h1
  · simp [h0]
  · right
    have h1z : (1 : ℤ) ≤ n.natAbs := Nat.one_le_cast.mpr h1
    nlinarith

private lemma mul_self_ne_two (n : ℤ) : n * n ≠ 2 := by
  intro h
  have hnat : n.natAbs * n.natAbs = 2 := by
    have := congr_arg Int.natAbs h
    simpa [Int.natAbs_mul] using this
  have : n.natAbs = 0 ∨ n.natAbs = 1 ∨ 2 ≤ n.natAbs := by omega
  rcases this with h0 | h1 | h2
  · simp [h0] at hnat
  · simp [h1] at hnat
  · have : 4 ≤ n.natAbs * n.natAbs := Nat.mul_le_mul h2 h2
    omega

private lemma mul_self_ne_three (n : ℤ) : n * n ≠ 3 := by
  intro h
  have hnat : n.natAbs * n.natAbs = 3 := by
    have := congr_arg Int.natAbs h
    simpa [Int.natAbs_mul] using this
  have : n.natAbs = 0 ∨ n.natAbs = 1 ∨ 2 ≤ n.natAbs := by omega
  rcases this with h0 | h1 | h2
  · simp [h0] at hnat
  · simp [h1] at hnat
  · have : 4 ≤ n.natAbs * n.natAbs := Nat.mul_le_mul h2 h2
    omega

/-- If `a * b = n` with `a, b ≥ 0` and `0 < n`, then `a ≤ n`. -/
private lemma le_of_nonneg_mul_eq {a b n : ℤ}
    (hprod : a * b = n) (ha : 0 ≤ a) (hb : 0 ≤ b) (hn : 0 < n) : a ≤ n := by
  have hb1 : 1 ≤ b := by
    have : b = 0 ∨ 1 ≤ b := by omega
    rcases this with rfl | h
    · have : n = 0 := by simpa using hprod.symm
      omega
    · exact h
  nlinarith

/-- No element of `ℤ√(-5)` has norm 2. Glue for irreducibility. -/
private lemma not_norm_two (z : Zsqrt5) : z.norm ≠ 2 := by
  intro h
  have hn : z.re * z.re + 5 * (z.im * z.im) = 2 := by
    rw [← norm_as_sq, h]
  have him : z.im * z.im = 0 := by
    rcases mul_self_eq_zero_or_one_le z.im with h0 | h1
    · exact h0
    · nlinarith [mul_self_nonneg z.re]
  have : z.re * z.re = 2 := by simpa [him] using hn
  exact mul_self_ne_two z.re this

/-- No element of `ℤ√(-5)` has norm 3. Glue for optional extras. -/
private lemma not_norm_three (z : Zsqrt5) : z.norm ≠ 3 := by
  intro h
  have hn : z.re * z.re + 5 * (z.im * z.im) = 3 := by
    rw [← norm_as_sq, h]
  have him : z.im * z.im = 0 := by
    rcases mul_self_eq_zero_or_one_le z.im with h0 | h1
    · exact h0
    · nlinarith [mul_self_nonneg z.re]
  have : z.re * z.re = 3 := by simpa [him] using hn
  exact mul_self_ne_three z.re this

private lemma two_re : (2 : Zsqrt5).re = 2 := rfl
private lemma two_im : (2 : Zsqrt5).im = 0 := rfl
private lemma three_re : (3 : Zsqrt5).re = 3 := rfl
private lemma three_im : (3 : Zsqrt5).im = 0 := rfl

private lemma two_norm : (2 : Zsqrt5).norm = 4 := by
  simp [Zsqrtd.norm, two_re, two_im]

private lemma three_norm : (3 : Zsqrt5).norm = 9 := by
  simp [Zsqrtd.norm, three_re, three_im]

private lemma one_plus_norm : (⟨1, 1⟩ : Zsqrt5).norm = 6 := by
  simp [Zsqrtd.norm]

/-- Level A (not labelled Dedekind / Kummer / Gaussian):
`6 = 2 * 3` in `ℤ√(-5)`. -/
theorem six_two_three : (2 : Zsqrt5) * 3 = 6 := by
  ext <;> simp

/-- Level A (not labelled Dedekind / Kummer / Gaussian):
`6 = (1+√-5)(1-√-5)` in `ℤ√(-5)`. -/
theorem six_split : (⟨1, 1⟩ : Zsqrt5) * ⟨1, -1⟩ = 6 := by
  ext <;> simp [Zsqrtd.mul_re, Zsqrtd.mul_im]

/-- Level A (not labelled Dedekind / Kummer / Gaussian):
`2` does not divide `1+√-5` in `ℤ√(-5)`. -/
theorem two_not_dvd_one_plus_sqrtd : ¬ (2 : Zsqrt5) ∣ ⟨1, 1⟩ := by
  rintro ⟨z, hz⟩
  have hnorm := congr_arg Zsqrtd.norm hz
  rw [Zsqrtd.norm_mul, two_norm, one_plus_norm] at hnorm
  -- `6 = 4 * z.norm`, so `4 ∣ 6`.
  have : (4 : ℤ) ∣ 6 := ⟨z.norm, by linarith⟩
  omega

/-- Level A (not labelled Dedekind / Kummer / Gaussian):
`2` is irreducible in `ℤ√(-5)`. -/
theorem two_irreducible : Irreducible (2 : Zsqrt5) := by
  refine ⟨?notUnit, ?factors⟩
  · intro h
    have := (Zsqrtd.norm_eq_one_iff' d_nonpos (2 : Zsqrt5)).mpr h
    rw [two_norm] at this
    exact (by decide : (4 : ℤ) ≠ 1) this
  · intro a b hab
    have hprod : a.norm * b.norm = 4 := by
      have := congr_arg Zsqrtd.norm hab
      rw [Zsqrtd.norm_mul, two_norm] at this
      exact this.symm
    have ha0 := Zsqrtd.norm_nonneg d_nonpos a
    have hb0 := Zsqrtd.norm_nonneg d_nonpos b
    have hle : a.norm ≤ 4 := le_of_nonneg_mul_eq hprod ha0 hb0 (by decide)
    have : a.norm = 0 ∨ a.norm = 1 ∨ a.norm = 2 ∨ a.norm = 3 ∨ a.norm = 4 := by
      omega
    rcases this with h0 | h1 | h2 | h3 | h4
    · have : a = 0 := (Zsqrtd.norm_eq_zero_iff d_neg a).1 h0
      simp [this] at hab
    · exact Or.inl ((Zsqrtd.norm_eq_one_iff' d_nonpos a).1 h1)
    · exact (not_norm_two a h2).elim
    · have : (3 : ℤ) * b.norm = 4 := by simpa [h3] using hprod
      omega
    · have hb1 : b.norm = 1 := by nlinarith
      exact Or.inr ((Zsqrtd.norm_eq_one_iff' d_nonpos b).1 hb1)

/-- Optional extra: `3` is irreducible in `ℤ√(-5)`. Glue;
**not** labelled Dedekind. -/
theorem three_irreducible : Irreducible (3 : Zsqrt5) := by
  refine ⟨?notUnit, ?factors⟩
  · intro h
    have := (Zsqrtd.norm_eq_one_iff' d_nonpos (3 : Zsqrt5)).mpr h
    rw [three_norm] at this
    exact (by decide : (9 : ℤ) ≠ 1) this
  · intro a b hab
    have hprod : a.norm * b.norm = 9 := by
      have := congr_arg Zsqrtd.norm hab
      rw [Zsqrtd.norm_mul, three_norm] at this
      exact this.symm
    have ha0 := Zsqrtd.norm_nonneg d_nonpos a
    have hb0 := Zsqrtd.norm_nonneg d_nonpos b
    have hle : a.norm ≤ 9 := le_of_nonneg_mul_eq hprod ha0 hb0 (by decide)
    have : a.norm = 0 ∨ a.norm = 1 ∨ a.norm = 3 ∨ a.norm = 9 := by
      have : a.norm = 0 ∨ a.norm = 1 ∨ a.norm = 2 ∨ a.norm = 3 ∨
          a.norm = 4 ∨ a.norm = 5 ∨ a.norm = 6 ∨ a.norm = 7 ∨
          a.norm = 8 ∨ a.norm = 9 := by omega
      rcases this with h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · have : (2 : ℤ) * b.norm = 9 := by simpa [h] using hprod
        omega
      · exact Or.inr (Or.inr (Or.inl h))
      · have : (4 : ℤ) * b.norm = 9 := by simpa [h] using hprod
        omega
      · have : (5 : ℤ) * b.norm = 9 := by simpa [h] using hprod
        omega
      · have : (6 : ℤ) * b.norm = 9 := by simpa [h] using hprod
        omega
      · have : (7 : ℤ) * b.norm = 9 := by simpa [h] using hprod
        omega
      · have : (8 : ℤ) * b.norm = 9 := by simpa [h] using hprod
        omega
      · exact Or.inr (Or.inr (Or.inr h))
    rcases this with h0 | h1 | h3 | h9
    · have : a = 0 := (Zsqrtd.norm_eq_zero_iff d_neg a).1 h0
      simp [this] at hab
    · exact Or.inl ((Zsqrtd.norm_eq_one_iff' d_nonpos a).1 h1)
    · exact (not_norm_three a h3).elim
    · have hb1 : b.norm = 1 := by nlinarith
      exact Or.inr ((Zsqrtd.norm_eq_one_iff' d_nonpos b).1 hb1)

/-- Optional extra: `1+√-5` is irreducible in `ℤ√(-5)`. Glue;
**not** labelled Dedekind. -/
theorem one_plus_sqrtd_irreducible : Irreducible (⟨1, 1⟩ : Zsqrt5) := by
  refine ⟨?notUnit, ?factors⟩
  · intro h
    have := (Zsqrtd.norm_eq_one_iff' d_nonpos (⟨1, 1⟩ : Zsqrt5)).mpr h
    rw [one_plus_norm] at this
    exact (by decide : (6 : ℤ) ≠ 1) this
  · intro a b hab
    have hprod : a.norm * b.norm = 6 := by
      have := congr_arg Zsqrtd.norm hab
      rw [Zsqrtd.norm_mul, one_plus_norm] at this
      exact this.symm
    have ha0 := Zsqrtd.norm_nonneg d_nonpos a
    have hb0 := Zsqrtd.norm_nonneg d_nonpos b
    have hle : a.norm ≤ 6 := le_of_nonneg_mul_eq hprod ha0 hb0 (by decide)
    have : a.norm = 0 ∨ a.norm = 1 ∨ a.norm = 2 ∨ a.norm = 3 ∨ a.norm = 6 := by
      have : a.norm = 0 ∨ a.norm = 1 ∨ a.norm = 2 ∨ a.norm = 3 ∨
          a.norm = 4 ∨ a.norm = 5 ∨ a.norm = 6 := by omega
      rcases this with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · have : (4 : ℤ) * b.norm = 6 := by simpa [h] using hprod
        omega
      · have : (5 : ℤ) * b.norm = 6 := by simpa [h] using hprod
        omega
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
    rcases this with h0 | h1 | h2 | h3 | h6
    · have : a = 0 := (Zsqrtd.norm_eq_zero_iff d_neg a).1 h0
      have : (⟨1, 1⟩ : Zsqrt5) = 0 := by simpa [this] using hab
      simp [Zsqrtd.ext_iff] at this
    · exact Or.inl ((Zsqrtd.norm_eq_one_iff' d_nonpos a).1 h1)
    · exact (not_norm_two a h2).elim
    · exact (not_norm_three a h3).elim
    · have hb1 : b.norm = 1 := by nlinarith
      exact Or.inr ((Zsqrtd.norm_eq_one_iff' d_nonpos b).1 hb1)

/-- Optional extra: `2` and `1+√-5` are not associates
(norms 4 vs 6). Glue; **not** labelled Dedekind. -/
theorem two_not_associated_one_plus :
    ¬ Associated (2 : Zsqrt5) (⟨1, 1⟩ : Zsqrt5) := by
  intro h
  have := Zsqrtd.norm_eq_of_associated d_nonpos h
  rw [two_norm, one_plus_norm] at this
  exact (by decide : (4 : ℤ) ≠ 6) this

/-
Level B namesake OUT of this ticket (do not sorry):
  theorem zsqrt5_not_ufd :
      ¬ UniqueFactorizationMonoid Zsqrt5
Class number 2 / Dedekind domain / ideal factorization extras
are residual of this id — do not expand; do not label theorems
`dedekind_*` / `kummer_*` / `gaussian_*`; do not define the
namesake via class group.
-/

end ProofLab.Zsqrt5NotUfd
