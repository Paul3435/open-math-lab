-- PSEUDO-LEAN (not type-checked — Lean toolchain not installed)
-- Formalization draft for Erdős-Woods k=16 verification
-- Status: Draft — requires Lean installation to build
-- Problem: proofs/erdos-woods/STATEMENT.md
-- Result: attacks/erdos-woods-20260730-125506/RESULT.md

import Mathlib.Data.Nat.Prime
import Mathlib.Order.Interval.Set.Basic

namespace ProofLab.ErdosWoods

/-! # Erdős-Woods Numbers

This file contains a formalization draft of the Erdős-Woods number definition
and the verification that k=16 is an Erdős-Woods number with witness a=5.

## Main Definitions

* `IsErdosWoodsWitness k a`: Predicate stating that `a` is a witness for `k`
* `IsErdosWoodsNumber k`: Predicate stating that `k` is an Erdős-Woods number

## Main Results

* `erdos_woods_16`: k=16 is an Erdős-Woods number (witness a=5)
* `erdos_woods_16_minimal`: a=5 is the minimal witness for k=16

## References

* Erdős, P. and Woods, A. R. (1980). "On Rings of Products of Primes"
* OEIS A059756: Erdős-Woods numbers
-/

/--
A prime p ≤ k distinguishes i from a if p divides exactly one of them.
This is the exclusive-or (XOR) condition: (p | i) ⊕ (p | a)
-/
def PrimeDistinguishes (p k i a : ℕ) : Prop :=
  Nat.Prime p ∧ p ≤ k ∧ (p ∣ i ↔ ¬(p ∣ a))

/--
A positive integer a is a witness for k if every integer in [a, a+k]
is distinguished from a by at least one prime p ≤ k.
-/
def IsErdosWoodsWitness (k a : ℕ) : Prop :=
  0 < a ∧ ∀ i ∈ Set.Icc a (a + k), i ≠ a →
    ∃ p : ℕ, PrimeDistinguishes p k i a

/--
A positive integer k is an Erdős-Woods number if there exists
a witness a for k.
-/
def IsErdosWoodsNumber (k : ℕ) : Prop :=
  ∃ a : ℕ, IsErdosWoodsWitness k a

/--
Helper: Check if a specific prime distinguishes two numbers
-/
lemma prime_distinguishes_decidable (p k i a : ℕ) :
  Decidable (PrimeDistinguishes p k i a) := by
  sorry  -- Relies on decidability of divisibility and primality

/--
Computational verification that a=5 is a witness for k=16
by checking all 17 integers in [5, 21].
-/
lemma witness_5_for_16_verified :
  IsErdosWoodsWitness 16 5 := by
  unfold IsErdosWoodsWitness
  constructor
  · norm_num  -- 0 < 5
  · intro i hi h_ne
    -- The interval [5, 21] contains 17 integers
    -- For each i ∈ {6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21}:
    -- We need to show ∃ p ≤ 16: PrimeDistinguishes p 16 i 5

    -- Primes ≤ 16: {2, 3, 5, 7, 11, 13}
    -- a = 5, so only prime dividing a is 5

    interval_cases i
    · -- i = 5: excluded by h_ne
      contradiction
    · -- i = 6 = 2 × 3: distinguished by 2 (divides 6, not 5)
      use 2
      sorry
    · -- i = 7: distinguished by 7 (divides 7, not 5)
      use 7
      sorry
    · -- i = 8 = 2³: distinguished by 2
      use 2
      sorry
    · -- i = 9 = 3²: distinguished by 3
      use 3
      sorry
    · -- i = 10 = 2 × 5: distinguished by 2 (5 divides both, but 2 only divides 10)
      use 2
      sorry
    · -- i = 11: distinguished by 11
      use 11
      sorry
    · -- i = 12 = 2² × 3: distinguished by 2
      use 2
      sorry
    · -- i = 13: distinguished by 13
      use 13
      sorry
    · -- i = 14 = 2 × 7: distinguished by 2
      use 2
      sorry
    · -- i = 15 = 3 × 5: distinguished by 3 (5 divides both, but 3 only divides 15)
      use 3
      sorry
    · -- i = 16 = 2⁴: distinguished by 2
      use 2
      sorry
    · -- i = 17 (prime > 16): distinguished by 5 (divides a, not i)
      use 5
      sorry
    · -- i = 18 = 2 × 3²: distinguished by 2
      use 2
      sorry
    · -- i = 19 (prime > 16): distinguished by 5
      use 5
      sorry
    · -- i = 20 = 2² × 5: distinguished by 2
      use 2
      sorry
    · -- i = 21 = 3 × 7: distinguished by 3
      use 3
      sorry

/--
Witnesses 1,2,3,4 fail for k=16
-/
lemma not_witness_1_to_4 :
  ¬IsErdosWoodsWitness 16 1 ∧
  ¬IsErdosWoodsWitness 16 2 ∧
  ¬IsErdosWoodsWitness 16 3 ∧
  ¬IsErdosWoodsWitness 16 4 := by
  constructor
  · -- a=1 fails: i=17 is not distinguished (both coprime to all primes ≤ 16)
    sorry
  constructor
  · -- a=2 fails: i=4 is not distinguished (both divisible only by 2)
    sorry
  constructor
  · -- a=3 fails: i=9 is not distinguished (both divisible only by 3)
    sorry
  · -- a=4 fails: i=8 is not distinguished (both divisible only by 2)
    sorry

/--
Main theorem: k=16 is an Erdős-Woods number
-/
theorem erdos_woods_16 : IsErdosWoodsNumber 16 := by
  use 5
  exact witness_5_for_16_verified

/--
Minimality: a=5 is the smallest witness for k=16
-/
theorem erdos_woods_16_minimal :
  IsErdosWoodsWitness 16 5 ∧
  (∀ a : ℕ, 0 < a → a < 5 → ¬IsErdosWoodsWitness 16 a) := by
  constructor
  · exact witness_5_for_16_verified
  · intro a ha_pos ha_lt5
    interval_cases a
    · norm_num at ha_pos  -- a = 0: contradiction with 0 < a
    · exact not_witness_1_to_4.1  -- a = 1
    · exact not_witness_1_to_4.2.1  -- a = 2
    · exact not_witness_1_to_4.2.2.1  -- a = 3
    · exact not_witness_1_to_4.2.2.2  -- a = 4

end ProofLab.ErdosWoods
