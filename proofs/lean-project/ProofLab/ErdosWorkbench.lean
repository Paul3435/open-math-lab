import Mathlib.Data.Nat.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

open scoped BigOperators

namespace ProofLab.SumFree

/-!
# OPE-23 Step 2: middle-third cardinality

`I = {k : ℕ | p < 3*k ∧ 3*k < 2*p}` is the middle third in ℤ_p (reps 1..p-1).
We prove:
  1. `middleThirdCount_eq`: |I| = (2p-1)/3 - p/3  (count via index, no sorry)
  2. `middle_third_card_bound`: 3 * |I| ≥ p - 1  when p%3 ≠ 0 (prime p ≥ 5)

All lemmas here type-check with zero sorries.
-/

/-- The middle third as a window over an index `k`: multiples-of-3 in (p, 2p). -/
def middleThirdCount (p : ℕ) : ℕ :=
  ((Finset.range (2 * p)).filter (fun k => p < 3 * k ∧ 3 * k < 2 * p)).card

/-- `p < 3k` iff `p/3 < k` (division by the constant 3). -/
lemma lt_mul_iff_div_lt (p k : ℕ) : (p < 3 * k ↔ p / 3 < k) := by
  rw [Nat.div_lt_iff_lt_mul (show 0 < 3 by norm_num)]
  omega

/-- For `0 < p`: `3k < 2p` iff `k ≤ (2p-1)/3`.  The strict inequality `3k < 2p`
    becomes `3k ≤ 2p-1` over the naturals, so `k` is bounded by the quotient. -/
lemma mul_lt_iff_le_div (p k : ℕ) (hp : 0 < p) :
    (3 * k < 2 * p ↔ k ≤ (2 * p - 1) / 3) := by
  constructor
  · intro h
    rw [Nat.le_div_iff_mul_le (show 0 < 3 by norm_num)]
    rw [Nat.lt_iff_add_one_le] at h
    omega
  · intro h
    rw [Nat.le_div_iff_mul_le (show 0 < 3 by norm_num)] at h
    rw [Nat.lt_iff_add_one_le]
    omega

/-- The count of k with p < 3k < 2p equals the number of multiples of 3 strictly
    between p and 2p, i.e. floor((2p-1)/3) - floor(p/3).  (three consecutive integers
    contain exactly one multiple of 3, and k indexes the multiple 3k.) -/
lemma middleThirdCount_eq (p : ℕ) :
    middleThirdCount p = (2 * p - 1) / 3 - p / 3 := by
  unfold middleThirdCount
  by_cases hp : p = 0
  · subst hp
    norm_num [middleThirdCount]
  · have hp0 : 0 < p := Nat.pos_of_ne_zero hp
    -- The admissible k's (p < 3k < 2p within k < 2p) are exactly the indices in
    -- [p/3 + 1, (2p-1)/3 + 1), i.e. the Ico window.
    have hT : (Finset.range (2 * p)).filter (fun k => p < 3 * k ∧ 3 * k < 2 * p)
              = Finset.Ico (p / 3 + 1) ((2 * p - 1) / 3 + 1) := by
      ext k
      simp [Finset.mem_Ico]
      constructor
      · rintro ⟨_, hpk', hklt3⟩
        have hpk : p / 3 < k := (lt_mul_iff_div_lt p k).1 hpk'
        have hku : k ≤ (2 * p - 1) / 3 := (mul_lt_iff_le_div p k hp0).1 hklt3
        constructor
        · exact Nat.succ_le_of_lt hpk
        · omega
      · rintro ⟨hl, hlt⟩
        constructor
        · rw [Nat.lt_iff_add_one_le]
          omega
        constructor
        · exact (lt_mul_iff_div_lt p k).2 (by omega)
        · exact (mul_lt_iff_le_div p k hp0).2 (by omega)
    rw [hT]
    rw [Nat.card_Ico]
    omega

/-- Cardinality bound: 3 * |I| ≥ p - 1 for p with p%3 ≠ 0 (covers primes p ≥ 5). -/
lemma middle_third_card_bound (p : ℕ) (hp : p % 3 ≠ 0) :
    3 * ((2 * p - 1) / 3 - p / 3) ≥ p - 1 := by
  have hmod := Nat.div_add_mod p 3
  have hq : p % 3 = 1 ∨ p % 3 = 2 := by omega
  rcases hq with h1 | h2
  · have hrep : p = 3 * (p / 3) + 1 := by
      rw [← h1]
      exact hmod.symm
    rw [hrep]
    norm_num [Nat.mul_sub_left_distrib]
    omega
  · have hrep : p = 3 * (p / 3) + 2 := by
      rw [← h2]
      exact hmod.symm
    rw [hrep]
    norm_num [Nat.mul_sub_left_distrib]
    omega

/-- Direct bound on the actual count: for p with p%3 ≠ 0, the middle third has size
    at least (p-1)/3, i.e. 3 * |I| ≥ p - 1. -/
lemma middle_third_count_bound (p : ℕ) (hp : p % 3 ≠ 0) :
    3 * middleThirdCount p ≥ p - 1 := by
  rw [middleThirdCount_eq]
  exact middle_third_card_bound p hp

end ProofLab.SumFree