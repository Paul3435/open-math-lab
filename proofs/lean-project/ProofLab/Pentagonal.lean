/-
Euler's pentagonal number theorem: finite `p(n)` recurrence.

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 has `Nat.Partition` / `Fintype` / `odds` / `distincts` and ZERO
pentagonal / Franklin ident. Archive `Wiedijk100Theorems/Partition.lean`
`partition_theorem` is Euler **odd = distinct** via generating functions —
a *different* theorem, already consumed in ProofLab as `euler_odd_eq_distinct`
(Glaisher, PR #43). `SchurGlaisher.lean` is the congruence identity (also
consumed). This is **not** a re-prime of those ids.

Pin: `catalog/problems/pentagonal-number-theorem/STATEMENT.md` (OPE-745;
Scout OPE-735 leftover slot #2; Director OPE-744). Encoding: `partitionFunction n
:= Fintype.card (Nat.Partition n)` with the ℕ recurrence that moves even-`k`
pentagonal terms to the left. Zero `sorry`. Do not import `Archive.*`.

This is **not** `euler_odd_eq_distinct` / Glaisher.
This is **not** `schur_partition` / Glaisher congruence.
This is **not** Archive Theorems100 `partition_theorem`.
This is **not** Rogers–Ramanujan / Jacobi triple product / PowerSeries form.
This is **not** kovari-sos-turan / sunflower / combinatorial Nullstellensatz.

Level A: `pentagonal` / `pentagonal'` exact division for `k ≥ 1`; `p(0) = 1`;
`p(1) = 1`; recurrence spot-checks `n ≤ 10` via `native_decide`. Glue, **not**
labelled pentagonal number theorem. Zero sorry.
Level B: namesake `pentagonal_number` by Franklin's sign-reversing involution
on distinct-part partitions + the empty/smallest-part convolution that turns
the signed distinct count into the `p(n)` recurrence. Cap two levels.
-/
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Combinatorics.Enumerative.Partition
import Mathlib.Tactic

set_option maxHeartbeats 800000

open Finset
open Nat.Partition

namespace ProofLab.Pentagonal

/-! ## STATEMENT pin -/

/-- `p(n)` as the number of integer partitions of `n`. `Partition 0` is unique,
so `p(0) = 1`. Stays on `ℕ`; negative arguments are encoded by omitting terms
with `ω(k) > n`. -/
def partitionFunction (n : ℕ) : ℕ := Fintype.card (Nat.Partition n)

/-- Generalized pentagonal `ω(k) = k(3k−1)/2` for `k ≥ 1` (1, 5, 12, 22, …).
Not labelled pentagonal number theorem. -/
def pentagonal (k : ℕ) : ℕ := k * (3 * k - 1) / 2

/-- Generalized pentagonal `ω'(k) = k(3k+1)/2` for `k ≥ 1` (2, 7, 15, 26, …),
the `−k` family. Not labelled pentagonal number theorem. -/
def pentagonal' (k : ℕ) : ℕ := k * (3 * k + 1) / 2

/-! ## Level A — exact division glue (not labelled pentagonal) -/

lemma one_le_three_mul {k : ℕ} (hk : 1 ≤ k) : 1 ≤ 3 * k := by
  calc
    1 ≤ k := hk
    _ ≤ 3 * k := Nat.le_mul_of_pos_left k (by decide : 0 < 3)

/-- `k(3k−1)` is even for `k ≥ 1`. Engine, not labelled pentagonal. -/
theorem two_dvd_k_mul_three_k_sub_one {k : ℕ} (hk : 1 ≤ k) :
    2 ∣ k * (3 * k - 1) := by
  have hge : 1 ≤ 3 * k := one_le_three_mul hk
  obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' k
  · subst hm
    exact dvd_mul_of_dvd_left ⟨m, rfl⟩ _
  · subst hm
    have h3 : 3 * (2 * m + 1) - 1 = 2 * (3 * m + 1) := by
      omega
    rw [h3]
    exact dvd_mul_of_dvd_right ⟨3 * m + 1, rfl⟩ _

/-- `k(3k+1)` is always even. Engine, not labelled pentagonal. -/
theorem two_dvd_k_mul_three_k_add_one (k : ℕ) : 2 ∣ k * (3 * k + 1) := by
  obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' k
  · subst hm
    exact dvd_mul_of_dvd_left ⟨m, rfl⟩ _
  · subst hm
    have h3 : 3 * (2 * m + 1) + 1 = 2 * (3 * m + 2) := by
      omega
    rw [h3]
    exact dvd_mul_of_dvd_right ⟨3 * m + 2, rfl⟩ _

/-- Exact division: `2 * ω(k) = k(3k−1)` for `k ≥ 1`. `1 ≤ k` is load-bearing
so `3k−1` does not underflow. Glue, not labelled pentagonal. -/
theorem pentagonal_mul_two {k : ℕ} (hk : 1 ≤ k) :
    2 * pentagonal k = k * (3 * k - 1) := by
  simpa [pentagonal] using Nat.mul_div_cancel' (two_dvd_k_mul_three_k_sub_one hk)

/-- Exact division: `2 * ω'(k) = k(3k+1)`. Glue, not labelled pentagonal. -/
theorem pentagonal'_mul_two (k : ℕ) :
    2 * pentagonal' k = k * (3 * k + 1) := by
  simpa [pentagonal'] using Nat.mul_div_cancel' (two_dvd_k_mul_three_k_add_one k)

theorem pentagonal_one : pentagonal 1 = 1 := by
  native_decide

theorem pentagonal'_one : pentagonal' 1 = 2 := by
  native_decide

theorem pentagonal_two : pentagonal 2 = 5 := by
  native_decide

theorem pentagonal'_two : pentagonal' 2 = 7 := by
  native_decide

theorem pentagonal_pos {k : ℕ} (hk : 1 ≤ k) : 0 < pentagonal k := by
  have h2 : 0 < 2 * pentagonal k := by
    rw [pentagonal_mul_two hk]
    have : 0 < k * (3 * k - 1) :=
      Nat.mul_pos (Nat.succ_le_iff.mp hk)
        (Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide : 1 < 3) (Nat.mul_le_mul_left 3 hk)))
    exact this
  omega

theorem pentagonal'_pos {k : ℕ} (hk : 1 ≤ k) : 0 < pentagonal' k := by
  have h2 : 0 < 2 * pentagonal' k := by
    rw [pentagonal'_mul_two k]
    have : 0 < k * (3 * k + 1) :=
      Nat.mul_pos (Nat.succ_le_iff.mp hk) (Nat.succ_pos _)
    exact this
  omega

/-- `ω(k) ≥ k` for `k ≥ 1`, so ranging over `Finset.range (n+1)` hits every
term with `ω(k) ≤ n`. -/
theorem le_pentagonal {k : ℕ} (hk : 1 ≤ k) : k ≤ pentagonal k := by
  have h2 : 2 * k ≤ 2 * pentagonal k := by
    rw [pentagonal_mul_two hk]
    have : 2 * k ≤ k * (3 * k - 1) := by
      calc
        2 * k = k * 2 := by ring
        _ ≤ k * (3 * k - 1) := Nat.mul_le_mul_left k (by
          have : 1 ≤ 3 * k := one_le_three_mul hk
          omega)
    exact this
  omega

theorem le_pentagonal' {k : ℕ} (hk : 1 ≤ k) : k ≤ pentagonal' k := by
  have h2 : 2 * k ≤ 2 * pentagonal' k := by
    rw [pentagonal'_mul_two k]
    have : 2 * k ≤ k * (3 * k + 1) := by
      calc
        2 * k = k * 2 := by ring
        _ ≤ k * (3 * k + 1) := Nat.mul_le_mul_left k (by omega)
    exact this
  omega

/-! ## Level A — `p(0) = 1`, `p(1) = 1` -/

theorem partitionFunction_zero : partitionFunction 0 = 1 := by
  simp [partitionFunction, Fintype.card_unique]

theorem partitionFunction_one : partitionFunction 1 = 1 := by
  simp [partitionFunction, Fintype.card_unique]

/-! ## Level A — recurrence spot-checks `n ≤ 10` (not labelled pentagonal) -/

/-- Guard only: the namesake ℕ recurrence holds through `n ≤ 10` by enumerating
`Fintype (Partition n)` (via compositions, `2^(n-1)`). Off-by-one / sign /
underflow landmines already fail at `n = 1` (`p(1) = p(0)` from `ω(1) = 1`)
and `n = 2` (`+p(0)` from `ω'(1) = 2`). Not labelled pentagonal number theorem. -/
theorem pentagonal_recurrence_le_ten :
    ∀ n ≤ 10, 0 < n →
      partitionFunction n
        + (∑ k ∈ Finset.range (n + 1),
            if 0 < k ∧ Even k ∧ pentagonal k ≤ n then
              partitionFunction (n - pentagonal k) else 0)
        + (∑ k ∈ Finset.range (n + 1),
            if 0 < k ∧ Even k ∧ pentagonal' k ≤ n then
              partitionFunction (n - pentagonal' k) else 0)
      =
          (∑ k ∈ Finset.range (n + 1),
            if 0 < k ∧ Odd k ∧ pentagonal k ≤ n then
              partitionFunction (n - pentagonal k) else 0)
        + (∑ k ∈ Finset.range (n + 1),
            if 0 < k ∧ Odd k ∧ pentagonal' k ≤ n then
              partitionFunction (n - pentagonal' k) else 0) := by
  intro n hn hpos
  have hcases : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨
      n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals native_decide

/-! ## Level B residual — namesake not sorry-ed

Franklin's sign-reversing involution on `distincts n` (smallest part vs consecutive
staircase; fixed points = the two pentagonal trapezoids of size `ω(k)` / `ω'(k)`)
plus the empty/smallest-part convolution that turns the signed distinct count
into the `p(n)` recurrence is the namesake engine. It is **not** landed this
heartbeat and is **not** sorry-ed. Do not label any Level A lemma `pentagonal_number`.
-/

end ProofLab.Pentagonal
