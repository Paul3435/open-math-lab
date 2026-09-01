/-
Irrationality of e (formalize-only).

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 has `Real.exp` / `NormedSpace.exp`, `exp_eq_tsum_div`
(`Analysis/NormedSpace/Exponential.lean`) and the `Irrational` predicate
(`Data/Real/Irrational.lean`). ZERO `Irrational (Real.exp 1)` /
`irrational_exp_one` under `Mathlib/` or `Archive/`. Completing the namesake
is the gap. Wiedijk 100.yaml #67 is **e transcendental** (external Lean only,
no Mathlib decl) — a **different, harder** theorem. Do **not** import that
file. Do **not** import `Archive.*`. Do **not** prove transcendence.

Pin: `catalog/problems/e-irrational/STATEMENT.md` (OPE-848; Scout OPE-838
leftover slot #2; Director OPE-847). Encoding: Mathlib `Irrational`
(`¬ ∃ q : ℚ, ↑q = Real.exp 1`). `Real.exp` / `exp_eq_tsum_div` are **used,
not re-proved**. Zero `sorry`. Do not import `Archive.*`.

This is **not** e-transcendental (Wiedijk 67 external).
This is **not** π-irrational (Niven integral sink; different theorem).
This is **not** Liouville (`Liouville.transcendental` already Mathlib; e is
not a Liouville number).
This is **not** `harmonic_not_int` / Wilson / Lucas / Wolstenholme.
This is **not** Descartes (consumed PR #91 honest Level A).
This is **not** n-fold PIE (consumed #88).
Leave OPE-403 alone.

v1 is `Irrational (Real.exp 1)`, not transcendence, not `exp q` for
`q ≠ 0`, not π.

Level A `exp_one_sub_partialExpSum_pos` / `exp_one_sub_partialExpSum_lt`
is the tail bound `0 < exp 1 − s n < 2 / (n+1)!` via `exp_eq_tsum_div` at
`x = 1`. **Not** labelled `irrational_exp_one`.
Level B namesake `irrational_exp_one`: if `exp 1 = p / q`, take `n ≥ max q 2`,
multiply the remainder by `n!`, derive a positive integer `< 1`.

Transcribed classical argument (Euler / Fourier 1815 series remainder;
textbook Rudin ch.1). Compact form: Wikipedia *e (mathematical constant)* —
"e is irrational". Wiedijk #67 transcendental external Lean is **not**
Mathlib and **not** this claim.
-/
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Real.Irrational
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option maxHeartbeats 800000

open Finset Nat
open scoped Nat Classical
open NormedSpace

noncomputable section

namespace ProofLab.EIrrational

/-! ## Partial sums of `∑ 1/n!` -/

/-- Partial sum `s n = ∑ k ∈ range (n+1), 1 / k!`. Engine, not labelled
irrational. -/
def partialExpSum (n : ℕ) : ℝ :=
  ∑ k ∈ range (n + 1), (1 : ℝ) / k !

lemma summable_inv_factorial : Summable fun n : ℕ => (1 : ℝ) / n ! := by
  simpa using (expSeries_div_summable (𝕂 := ℝ) (1 : ℝ))

/-- `Real.exp 1 = ∑' 1/n!`. Uses Mathlib `exp_eq_tsum_div`; **not** a re-proof
of the series. -/
lemma exp_one_eq_tsum : Real.exp 1 = ∑' n : ℕ, (1 : ℝ) / n ! := by
  rw [Real.exp_eq_exp_ℝ]
  have h := (expSeries_div_hasSum_exp (𝕂 := ℝ) (1 : ℝ)).tsum_eq
  rw [← h]
  exact tsum_congr fun n => by simp

lemma exp_one_eq_partial_add_tail (n : ℕ) :
    Real.exp 1 =
      partialExpSum n + ∑' k : ℕ, (1 : ℝ) / (k + (n + 1)) ! := by
  rw [exp_one_eq_tsum, partialExpSum]
  simpa using (sum_add_tsum_nat_add (n + 1) summable_inv_factorial).symm

lemma inv_factorial_nonneg (k : ℕ) : 0 ≤ (1 : ℝ) / k ! := by positivity

lemma inv_factorial_pos (k : ℕ) : 0 < (1 : ℝ) / k ! := by positivity

/-! ## Geometric comparison of the tail -/

lemma add_index (n k : ℕ) : k + (n + 1) = n + 1 + k := by
  abel

lemma inv_factorial_tail_le_geom (n k : ℕ) :
    (1 : ℝ) / (k + (n + 1)) ! ≤ ((1 : ℝ) / (n + 1)!) * (1 / 2) ^ k := by
  have hfac : (n + 1)! * (n + 2) ^ k ≤ (n + 1 + k)! :=
    Nat.factorial_mul_pow_le_factorial
  have hpow : (2 : ℕ) ^ k ≤ (n + 2) ^ k :=
    Nat.pow_le_pow_of_le_left (by omega : 2 ≤ n + 2) k
  have h3 : (n + 1)! * 2 ^ k ≤ (n + 1 + k)! :=
    le_trans (Nat.mul_le_mul_left _ hpow) hfac
  have h3R : ((n + 1)! : ℝ) * (2 : ℝ) ^ k ≤ (n + 1 + k)! := by exact_mod_cast h3
  have hpos : (0 : ℝ) < ((n + 1)! : ℝ) * (2 : ℝ) ^ k := by positivity
  have hidx : k + (n + 1) = n + 1 + k := add_index n k
  have hinv :
      (1 : ℝ) / (n + 1 + k)! ≤ 1 / (((n + 1)! : ℝ) * (2 : ℝ) ^ k) :=
    one_div_le_one_div_of_le hpos h3R
  calc
    (1 : ℝ) / (k + (n + 1)) ! = (1 : ℝ) / (n + 1 + k)! := by rw [hidx]
    _ ≤ 1 / (((n + 1)! : ℝ) * (2 : ℝ) ^ k) := hinv
    _ = (1 / (n + 1)!) * (1 / (2 : ℝ) ^ k) := by field_simp
    _ = (1 / (n + 1)!) * (1 / 2) ^ k := by rw [div_pow, one_pow]

lemma inv_factorial_tail_lt_geom_two (n : ℕ) :
    (1 : ℝ) / (2 + (n + 1)) ! < ((1 : ℝ) / (n + 1)!) * (1 / 2) ^ 2 := by
  have hidx : 2 + (n + 1) = n + 3 := by omega
  have hfac : ((n + 3)! : ℝ) = (n + 3) * (n + 2) * (n + 1)! := by
    have h1 : (n + 3)! = (n + 3) * (n + 2)! := by
      rw [show n + 3 = (n + 2) + 1 by omega, Nat.factorial_succ]
    have h2 : (n + 2)! = (n + 2) * (n + 1)! := by
      rw [show n + 2 = (n + 1) + 1 by omega, Nat.factorial_succ]
    rw [h1, h2]
    push_cast
    ring
  have hprod : (4 : ℝ) < (n + 3 : ℝ) * (n + 2) := by
    have : (3 : ℝ) ≤ n + 3 := by exact_mod_cast (by omega : 3 ≤ n + 3)
    have : (2 : ℝ) ≤ n + 2 := by exact_mod_cast (by omega : 2 ≤ n + 2)
    nlinarith
  have hn1 : (0 : ℝ) < (n + 1)! := by positivity
  have hden : (0 : ℝ) < (n + 3 : ℝ) * (n + 2) * (n + 1)! := by positivity
  have : (1 : ℝ) / ((n + 3) * (n + 2) * (n + 1)!) <
      (1 / (n + 1)!) * (1 / 4) := by
    have h4 : ((n + 1)! : ℝ) * 4 < (n + 3) * (n + 2) * (n + 1)! := by
      nlinarith
    have hpos4 : (0 : ℝ) < ((n + 1)! : ℝ) * 4 := by positivity
    have hdiv := (one_div_lt_one_div hden hpos4).mpr h4
    have heq : (1 : ℝ) / (((n + 1)! : ℝ) * 4) = (1 / (n + 1)!) * (1 / 4) := by
      field_simp
    rwa [heq] at hdiv
  have hpow : ((1 : ℝ) / 2) ^ 2 = 1 / 4 := by norm_num
  calc
    (1 : ℝ) / (2 + (n + 1)) ! = (1 : ℝ) / (n + 3)! := by rw [hidx]
    _ = (1 : ℝ) / ((n + 3) * (n + 2) * (n + 1)!) := by rw [hfac]
    _ < (1 / (n + 1)!) * (1 / 4) := this
    _ = (1 / (n + 1)!) * (1 / 2) ^ 2 := by rw [hpow]

lemma summable_geom_scaled (n : ℕ) :
    Summable fun k : ℕ => ((1 : ℝ) / (n + 1)!) * (1 / 2) ^ k :=
  (summable_geometric_two).mul_left _

lemma tsum_geom_scaled (n : ℕ) :
    (∑' k : ℕ, ((1 : ℝ) / (n + 1)!) * (1 / 2) ^ k) = 2 / (n + 1)! := by
  rw [tsum_mul_left, tsum_geometric_two]
  ring

/-! ## Level A — remainder bound (not labelled irrational) -/

/-- Tail of `∑ 1/n!` is positive. Engine, **not** labelled `irrational_exp_one`. -/
theorem exp_one_sub_partialExpSum_pos (n : ℕ) :
    0 < Real.exp 1 - partialExpSum n := by
  have htail := exp_one_eq_partial_add_tail n
  have hsum : Summable fun k : ℕ => (1 : ℝ) / (k + (n + 1)) ! :=
    (summable_nat_add_iff (n + 1)).2 summable_inv_factorial
  have hpos : 0 < ∑' k : ℕ, (1 : ℝ) / (k + (n + 1)) ! :=
    tsum_pos hsum (fun _ => inv_factorial_nonneg _) 0 (inv_factorial_pos _)
  linarith

/-- Tail bound `exp 1 − s n < 2 / (n+1)!`. Via the geometric comparison of
the tail of `exp_eq_tsum_div` at `x = 1`. **Not** labelled
`irrational_exp_one`. -/
theorem exp_one_sub_partialExpSum_lt (n : ℕ) :
    Real.exp 1 - partialExpSum n < 2 / (n + 1)! := by
  have htail := exp_one_eq_partial_add_tail n
  have hf : Summable fun k : ℕ => (1 : ℝ) / (k + (n + 1)) ! :=
    (summable_nat_add_iff (n + 1)).2 summable_inv_factorial
  have hg := summable_geom_scaled n
  have hle : ∀ k : ℕ,
      (1 : ℝ) / (k + (n + 1)) ! ≤ ((1 : ℝ) / (n + 1)!) * (1 / 2) ^ k :=
    inv_factorial_tail_le_geom n
  have hlt := inv_factorial_tail_lt_geom_two n
  have hnn : ∀ k : ℕ, 0 ≤ (1 : ℝ) / (k + (n + 1)) ! := fun _ =>
    inv_factorial_nonneg _
  have := tsum_lt_tsum_of_nonneg hnn hle hlt hg
  have hgeom := tsum_geom_scaled n
  linarith

/-! ## Level B — namesake `irrational_exp_one` -/

lemma factorial_div_cast {n k : ℕ} (hk : k ≤ n) :
    ((n ! : ℝ) / k !) = ↑(n ! / k !) := by
  have hdvd : k ! ∣ n ! := Nat.factorial_dvd_factorial hk
  have hk0 : (k ! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  exact (Nat.cast_div hdvd hk0).symm

lemma factorial_mul_partialExpSum_mem_nat (n : ℕ) :
    ∃ m : ℕ, (n ! : ℝ) * partialExpSum n = m := by
  refine ⟨∑ k ∈ range (n + 1), n ! / k !, ?_⟩
  unfold partialExpSum
  rw [mul_sum]
  refine (Finset.sum_congr rfl ?_).trans (Nat.cast_sum _ _).symm
  intro k hk
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  rw [← factorial_div_cast hk']
  field_simp

lemma factorial_mul_rat_mem_int (n : ℕ) (q : ℚ) (hden : q.den ≤ n) :
    ∃ m : ℤ, (n ! : ℝ) * (q : ℝ) = m := by
  have hpos : 0 < q.den := Nat.pos_of_ne_zero q.den_nz
  have hdvd : q.den ∣ n ! := Nat.dvd_factorial hpos hden
  have hdvdZ : (q.den : ℤ) ∣ (n ! : ℤ) := Int.natCast_dvd.mpr hdvd
  obtain ⟨c, hc⟩ := hdvdZ
  refine ⟨c * q.num, ?_⟩
  have hcR : (n ! : ℝ) = (q.den : ℝ) * (c : ℝ) := by exact_mod_cast hc
  rw [Rat.cast_def, hcR]
  field_simp
  ring

lemma not_int_mem_Ioo_zero_one {z : ℤ} (h0 : (0 : ℝ) < z) (h1 : (z : ℝ) < 1) :
    False := by
  have hz0 : (0 : ℤ) < z := by exact_mod_cast h0
  have hz1 : z < (1 : ℤ) := by exact_mod_cast h1
  omega

lemma two_div_succ_lt_one {n : ℕ} (hn : 2 ≤ n) : (2 : ℝ) / (n + 1) < 1 := by
  have h3 : (3 : ℕ) ≤ n + 1 := by omega
  have hle : (2 : ℝ) / (n + 1) ≤ 2 / 3 := by
    refine div_le_div_of_nonneg_left (by norm_num) (by norm_num) ?_
    exact_mod_cast h3
  linarith

lemma factorial_mul_two_div_succ (n : ℕ) :
    (n ! : ℝ) * (2 / (n + 1)!) = 2 / (n + 1 : ℝ) := by
  have hsucc : ((n + 1)! : ℝ) = (n + 1) * n ! := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hn0 : (n ! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hs0 : ((n + 1)! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp [hsucc, hn0, hs0]
  ring

/-- Namesake: `Real.exp 1` is irrational.
Classical Euler/Fourier remainder: if `exp 1 = p/q`, take `n ≥ max q.den 2`,
then `n! · (exp 1 − s n)` is a positive integer `< 1`. -/
theorem irrational_exp_one : Irrational (Real.exp 1) := by
  rintro ⟨q, hq⟩
  let n := max q.den 2
  have hden : q.den ≤ n := le_max_left _ _
  have hn2 : 2 ≤ n := le_max_right _ _
  have hpos := exp_one_sub_partialExpSum_pos n
  have hlt := exp_one_sub_partialExpSum_lt n
  obtain ⟨a, ha⟩ := factorial_mul_rat_mem_int n q hden
  obtain ⟨b, hb⟩ := factorial_mul_partialExpSum_mem_nat n
  rw [hq] at ha
  set z : ℤ := a - (b : ℤ)
  have hcast : (z : ℝ) = (n ! : ℝ) * (Real.exp 1 - partialExpSum n) := by
    dsimp [z]
    rw [Int.cast_sub, Int.cast_natCast, mul_sub, ha, hb]
  have h0 : (0 : ℝ) < (z : ℝ) := by
    rw [hcast]
    exact mul_pos (Nat.cast_pos.mpr n.factorial_pos) hpos
  have h1 : (z : ℝ) < 1 := by
    rw [hcast]
    have : (n ! : ℝ) * (Real.exp 1 - partialExpSum n) < 2 / (n + 1 : ℝ) := by
      have hmul := mul_lt_mul_of_pos_left hlt (Nat.cast_pos.mpr n.factorial_pos)
      rwa [factorial_mul_two_div_succ n] at hmul
    exact lt_trans this (two_div_succ_lt_one hn2)
  exact not_int_mem_Ioo_zero_one h0 h1

end ProofLab.EIrrational
