/-
Sum-Free Subsets in Finite Sets

Formalization of: Every finite set of n positive integers contains a sum-free
subset of size at least n/3.  (Erdős 1965.)

A subset A is sum-free if there do not exist x, y, z ∈ A such that x + y = z.

status: statement corrected to positive integers (0 ∉ S). Core lemmas proved;
        main theorem's hard branch (Erdős Z_p averaging) is a documented gap
        (OPE-14.1 / OPE-23).
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Defs
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic

namespace ProofLab.SumFree

/-!
# Sum-Free Sets

## Main Definitions

* `IsSumFree`: Predicate for sum-free subsets of ℕ
* `residueClass0Mod3`, `residueClass1Mod3`, `residueClass2Mod3`: Residue filters

## Main Results (with status)

* `empty_sum_free`          — proved
* `singleton_sum_free`      — proved (for nonzero a)
* `sum_free_subset`         — proved
* `residueClass1_sum_free`  — proved
* `residueClass2_sum_free`  — proved
* `mod3_partition`          — proved
* `sum_free_subset_bound`   — statement corrected (positives); hard branch OPEN (OPE-14.1)

## Proof Gap (PROOF_GAP → OPE-14.1 / OPE-23)

The naive modulo-3 approach (take the larger of C₁, C₂) fails when |C₀| > n/3.
The remaining branch of `sum_free_subset_bound` needs the Erdős (1965)
averaging argument over ℤ_p:

  1. Let p be a prime with p > max(S).
  2. Let I = {k ∈ ℤ_p : p/3 < k < 2p/3}. |I| ≥ (p-1)/3, and I is sum-free in ℤ_p.
  3. For t ∈ {1,…,p−1}, A_t = {s ∈ S : t·s mod p ∈ I} is sum-free in ℕ.
  4. Σ_t |A_t| = n·|I| ≥ n·(p−1)/3, so some A_t has |A_t| ≥ n/3.

This is the open part; it is tracked separately as OPE-14.1 / OPE-23 and is left
as an honest `sorry` here (the supporting residue-class construction is complete).
-/

/-- A finite set A ⊆ ℕ is sum-free if no element is the sum of two (not
    necessarily distinct) elements. -/
def IsSumFree (A : Finset ℕ) : Prop :=
  ∀ x y z, x ∈ A → y ∈ A → z ∈ A → x + y ≠ z

/-! ## Basic Properties -/

/-- The empty set is sum-free. -/
theorem empty_sum_free : IsSumFree (∅ : Finset ℕ) := by
  unfold IsSumFree
  intros x y z hx
  exact absurd hx (Finset.not_mem_empty x)

/-- A singleton {a} with a ≠ 0 is sum-free. (For a = 0 it fails: 0 + 0 = 0.) -/
theorem singleton_sum_free {a : ℕ} (ha : a ≠ 0) : IsSumFree ({a} : Finset ℕ) := by
  unfold IsSumFree
  intros x y z hx hy hz hsum
  simp at hx hy hz
  subst x
  subst y
  subst z
  -- goal: a + a ≠ a, i.e. 2a ≠ a, which follows from a ≠ 0
  omega

/-- Sum-free is hereditary: subsets of sum-free sets are sum-free. -/
theorem sum_free_subset {A B : Finset ℕ} (hA : IsSumFree A) (hB : B ⊆ A) : IsSumFree B := by
  unfold IsSumFree at *
  intros x y z hx hy hz
  exact hA x y z (hB hx) (hB hy) (hB hz)

/-! ## Residue Classes Mod 3 -/

/-- Filter S to elements ≡ 0 (mod 3). -/
def residueClass0Mod3 (S : Finset ℕ) : Finset ℕ :=
  S.filter (fun x => x % 3 = 0)

/-- Filter S to elements ≡ 1 (mod 3). -/
def residueClass1Mod3 (S : Finset ℕ) : Finset ℕ :=
  S.filter (fun x => x % 3 = 1)

/-- Filter S to elements ≡ 2 (mod 3). -/
def residueClass2Mod3 (S : Finset ℕ) : Finset ℕ :=
  S.filter (fun x => x % 3 = 2)

/-! ## Sum-Free Property of ≡1 and ≡2 Residue Classes -/

/-- Elements ≡ 1 mod 3 form a sum-free set.
    Proof: x ≡ 1, y ≡ 1 ⟹ x+y ≡ 2 (mod 3) ≠ 1, so x+y ∉ class. -/
theorem residueClass1_sum_free (S : Finset ℕ) : IsSumFree (residueClass1Mod3 S) := by
  unfold IsSumFree residueClass1Mod3
  intros x y z hx hy hz hsum
  simp at hx hy hz
  obtain ⟨_, hx1⟩ := hx
  obtain ⟨_, hy1⟩ := hy
  obtain ⟨_, hz1⟩ := hz
  have h_sum_mod : (x + y) % 3 = 2 := by
    calc (x + y) % 3
        = (x % 3 + y % 3) % 3 := Nat.add_mod x y 3
      _ = (1 + 1) % 3         := by rw [hx1, hy1]
      _ = 2                   := by norm_num
  rw [hsum] at h_sum_mod
  rw [hz1] at h_sum_mod
  omega

/-- Elements ≡ 2 mod 3 form a sum-free set.
    Proof: x ≡ 2, y ≡ 2 ⟹ x+y ≡ 4 ≡ 1 (mod 3) ≠ 2, so x+y ∉ class. -/
theorem residueClass2_sum_free (S : Finset ℕ) : IsSumFree (residueClass2Mod3 S) := by
  unfold IsSumFree residueClass2Mod3
  intros x y z hx hy hz hsum
  simp at hx hy hz
  obtain ⟨_, hx2⟩ := hx
  obtain ⟨_, hy2⟩ := hy
  obtain ⟨_, hz2⟩ := hz
  have h_sum_mod : (x + y) % 3 = 1 := by
    calc (x + y) % 3
        = (x % 3 + y % 3) % 3 := Nat.add_mod x y 3
      _ = (2 + 2) % 3         := by rw [hx2, hy2]
      _ = 1                   := by norm_num
  rw [hsum] at h_sum_mod
  rw [hz2] at h_sum_mod
  omega

/-! ## Helper Lemmas for the Modulo-3 Case -/

/-- The three residue classes partition S. -/
lemma mod3_partition (S : Finset ℕ) :
    (residueClass0Mod3 S).card + (residueClass1Mod3 S).card + (residueClass2Mod3 S).card
    = S.card := by
  unfold residueClass0Mod3 residueClass1Mod3 residueClass2Mod3
  -- Every element has x % 3 ∈ {0,1,2}; the classes are pairwise disjoint and cover S.
  have hcover : S = (S.filter (fun x => x % 3 = 0) ∪ S.filter (fun x => x % 3 = 1) ∪
                     S.filter (fun x => x % 3 = 2)) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hx
      have hr : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 := by omega
      rcases hr with h0 | h1 | h2
      · exact Or.inl (Or.inl ⟨hx, h0⟩)
      · exact Or.inl (Or.inr ⟨hx, h1⟩)
      · exact Or.inr ⟨hx, h2⟩
    · rintro (((⟨hx, _⟩ | ⟨hx, _⟩)) | ⟨hx, _⟩) <;> exact hx
  -- count: since the three filters are pairwise disjoint and union to S
  let A := S.filter (fun x => x % 3 = 0)
  let B := S.filter (fun x => x % 3 = 1)
  let C := S.filter (fun x => x % 3 = 2)
  have hun : (A ∪ B ∪ C) = S := by
    simpa [A, B, C] using hcover.symm
  have hdAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hx0 hx1
    simp [A, B] at hx0 hx1
    omega
  have hdAC : Disjoint A C := by
    rw [Finset.disjoint_left]
    intro x hx0 hx2
    simp [A, C] at hx0 hx2
    omega
  have hdBC : Disjoint B C := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp [B, C] at hx1 hx2
    omega
  have hAB : (A ∪ B).card = A.card + B.card := Finset.card_union_of_disjoint hdAB
  have hdABC : Disjoint (A ∪ B) C := by
    rw [Finset.disjoint_union_left]
    exact ⟨hdAC, hdBC⟩
  have h2 : (A ∪ B ∪ C).card = (A ∪ B).card + C.card := Finset.card_union_of_disjoint hdABC
  calc
    A.card + B.card + C.card = (A ∪ B).card + C.card := by rw [hAB]
    _ = (A ∪ B ∪ C).card := by rw [h2]
    _ = S.card := by rw [hun]

/-- If both C₁ and C₂ are smaller than n/3, then |C₀|*3 ≥ n. -/
lemma large_C0_of_small_C1_C2 (S : Finset ℕ)
    (h1 : (residueClass1Mod3 S).card * 3 < S.card)
    (h2 : (residueClass2Mod3 S).card * 3 < S.card) :
    (residueClass0Mod3 S).card * 3 ≥ S.card := by
  -- |C0| = n - |C1| - |C2|, so 3|C0| = 3n - 3|C1| - 3|C2| > 3n - n - n = n
  have hp := mod3_partition S
  nlinarith

/-! ## Main Theorem -/

/-!
**Theorem** (Erdős 1965): Every finite set S of positive integers contains a sum-free
subset A with |A| * 3 ≥ |S|.

The modulo-3 residue classes C₁ and C₂ handle the case when one is large.
The remaining case (|C₀| > n/3) needs the Erdős Z_p averaging argument,
which is the documented open gap tracked as OPE-14.1 / OPE-23.
-/
theorem sum_free_subset_bound (S : Finset ℕ) (hS : 0 ∉ S) :
    ∃ A : Finset ℕ, A ⊆ S ∧ IsSumFree A ∧ A.card * 3 ≥ S.card := by
  -- If C₁ is large enough, use it
  by_cases h1 : (residueClass1Mod3 S).card * 3 ≥ S.card
  · exact ⟨residueClass1Mod3 S, Finset.filter_subset _ S,
           residueClass1_sum_free S, h1⟩
  -- If C₂ is large enough, use it
  · by_cases h2 : (residueClass2Mod3 S).card * 3 ≥ S.card
    · exact ⟨residueClass2Mod3 S, Finset.filter_subset _ S,
             residueClass2_sum_free S, h2⟩
    -- Otherwise |C₀| > n/3; this branch needs the Erdős averaging argument
    -- over ℤ_p (ope-14.1 / OPE-23).  Until then it is an honest gap.
    · push_neg at h1 h2
      sorry

/-! ## Verified Examples -/

example : IsSumFree ({1, 5, 7} : Finset ℕ) := by
  unfold IsSumFree
  intros x y z hx hy hz
  simp at hx hy hz
  rcases hx with rfl | rfl | rfl <;>
  rcases hy with rfl | rfl | rfl <;>
  rcases hz with rfl | rfl | rfl <;>
  omega

example : ¬IsSumFree ({1, 2, 3} : Finset ℕ) := by
  unfold IsSumFree
  push_neg
  exact ⟨1, 2, 3, by simp, by simp, by simp, by norm_num⟩

/-- {3, 6, 9, 12, 15} has sum-free subset {3, 12} of size 2 ≥ 5/3. -/
example : IsSumFree ({3, 12} : Finset ℕ) ∧
          ({3, 12} : Finset ℕ) ⊆ ({3, 6, 9, 12, 15} : Finset ℕ) ∧
          ({3, 12} : Finset ℕ).card * 3 ≥ ({3, 6, 9, 12, 15} : Finset ℕ).card := by
  refine ⟨?_, ?_, ?_⟩
  · unfold IsSumFree
    intros x y z hx hy hz
    simp at hx hy hz
    rcases hx with rfl | rfl <;>
    rcases hy with rfl | rfl <;>
    rcases hz with rfl | rfl <;>
    omega
  · decide
  · decide

end ProofLab.SumFree
