/-
Erdős–Ko–Rado (k-uniform intersecting families)

Formalization of: if `n ≥ 2k` and `1 ≤ k`, every intersecting family of
`k`-subsets of an `n`-set has size at most `Nat.choose (n-1) (k-1)`,
achieved by a star.  (Erdős–Ko–Rado 1961.)

status: known-classical, formalize-only, **no novelty claim**.
         Mathlib v4.10.0 has only the non-uniform bound
         `Set.Intersecting.card_le` (size ≤ 2^{n-1}); this file is the
         k-uniform bound and must not be cited as that theorem.

Level A (this PR): definitions + star meets the bound + `n = 2k`
complementary pairing. Zero `sorry`.
Level B (residual): Katona cycle double-count for the full `n ≥ 2k` bound.

Pin: `catalog/problems/erdos-ko-rado/STATEMENT.md` (OPE-534 / Scout OPE-533).
Encoding: ground set `Fin n`; members are `Finset (Fin n)` of `card = k`.
-/

import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

open Finset

namespace ProofLab.ErdosKoRado

/-!
# Erdős–Ko–Rado (k-uniform intersecting families)

## Main definitions

* `Intersecting F` — every two members of `F` have nonempty intersection
* `IsKUniform F k` — every member has cardinality `k`
* `star n k i` — all `k`-subsets of `Fin n` that contain `i`

## Main results (zero `sorry`)

* `star_meets_bound` — a star has size `Nat.choose (n-1) (k-1)`
* `star_intersecting` / `star_kUniform` — a star is an intersecting k-family
* `erdos_ko_rado_of_eq` — the bound when `n = 2k` (complementary pairing)

The full `n ≥ 2k` Katona bound is **not** in this Level A ship.
Do not cite `Set.Intersecting.card_le` as this theorem.
Known-classical formalize-only; **no novelty claim**.
-/

/-- A family is intersecting when every two members meet. Matches STATEMENT.md. -/
def Intersecting {α : Type*} [DecidableEq α] (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, A ∩ B ≠ ∅

/-- A family is k-uniform when every member has cardinality `k`. -/
def IsKUniform {α : Type*} (F : Finset (Finset α)) (k : ℕ) : Prop :=
  ∀ A ∈ F, A.card = k

/-- The star of `i`: all `k`-subsets of `Fin n` containing `i`. -/
def star (n k : ℕ) (i : Fin n) : Finset (Finset (Fin n)) :=
  ((univ : Finset (Fin n)).powersetCard k).filter (fun A => i ∈ A)

/-! ## Star: membership, intersecting, uniformity -/

lemma mem_star {n k : ℕ} {i : Fin n} {A : Finset (Fin n)} :
    A ∈ star n k i ↔ A.card = k ∧ i ∈ A := by
  simp [star, mem_powersetCard]

lemma star_kUniform (n k : ℕ) (i : Fin n) : IsKUniform (star n k i) k := by
  intro A hA
  exact (mem_star.mp hA).1

lemma star_intersecting (n k : ℕ) (i : Fin n) : Intersecting (star n k i) := by
  intro A hA B hB hdisj
  have hiA : i ∈ A := (mem_star.mp hA).2
  have hiB : i ∈ B := (mem_star.mp hB).2
  have : i ∈ A ∩ B := mem_inter.mpr ⟨hiA, hiB⟩
  rw [hdisj] at this
  exact not_mem_empty i this

lemma injOn_insert_erase {α : Type*} [DecidableEq α] (i : α) (s : Finset (Finset α))
    (hs : ∀ A ∈ s, i ∉ A) : Set.InjOn (insert i) (s : Set (Finset α)) := by
  intro A hA B hB hEq
  have hA' : i ∉ A := hs A (by simpa using hA)
  have hB' : i ∉ B := hs B (by simpa using hB)
  simpa [erase_insert hA', erase_insert hB'] using congrArg (fun t => t.erase i) hEq

lemma star_eq_image {n m : ℕ} (i : Fin n) :
    star n (m + 1) i = ((univ.erase i).powersetCard m).image (insert i) := by
  ext A
  constructor
  · intro hA
    obtain ⟨hcard, hi⟩ := mem_star.mp hA
    refine mem_image.mpr ⟨A.erase i, ?_, insert_erase hi⟩
    refine mem_powersetCard.mpr ⟨?_, ?_⟩
    · intro x hx
      exact mem_erase.mpr ⟨ne_of_mem_erase hx, mem_univ x⟩
    · rw [card_erase_of_mem hi, hcard, Nat.add_sub_cancel]
  · intro hA
    rcases mem_image.mp hA with ⟨B, hB, rfl⟩
    obtain ⟨hBsub, hBcard⟩ := mem_powersetCard.mp hB
    have hiB : i ∉ B := fun h => (mem_erase.mp (hBsub h)).1 rfl
    refine mem_star.mpr ⟨?_, mem_insert_self i B⟩
    rw [card_insert_of_not_mem hiB, hBcard]

/-- A star has cardinality `C(n-1, k-1)`. Requires `1 ≤ k` so the right-hand
index is well-defined as `k-1`. The inhabitant `i : Fin n` forces `n ≥ 1`. -/
theorem star_meets_bound (n k : ℕ) (i : Fin n) (hk : 1 ≤ k) :
    (star n k i).card = Nat.choose (n - 1) (k - 1) := by
  cases k with
  | zero => exact (Nat.not_succ_le_zero 0 hk).elim
  | succ m =>
    rw [star_eq_image i]
    have hinj : Set.InjOn (insert i) (((univ.erase i).powersetCard m : Set (Finset (Fin n)))) :=
      injOn_insert_erase i _ (fun A hA => by
        have hsub : A ⊆ univ.erase i := (mem_powersetCard.mp hA).1
        exact fun hi => (mem_erase.mp (hsub hi)).1 rfl)
    rw [card_image_of_injOn hinj, card_powersetCard, card_erase_of_mem (mem_univ i),
      card_univ, Fintype.card_fin]
    rfl

/-! ## Level A: complementary pairing when `n = 2k` -/

lemma kUniform_subset_powersetCard {n k : ℕ} {F : Finset (Finset (Fin n))}
    (hU : IsKUniform F k) : F ⊆ univ.powersetCard k := by
  intro A hA
  exact mem_powersetCard.mpr ⟨subset_univ A, hU A hA⟩

lemma intersecting_not_compl_mem {n : ℕ} {F : Finset (Finset (Fin n))}
    (hI : Intersecting F) {A : Finset (Fin n)} (hA : A ∈ F) : Aᶜ ∉ F := by
  intro hc
  have hmeet : A ∩ Aᶜ ≠ ∅ := hI A hA Aᶜ hc
  simp at hmeet

lemma compl_card_of_two_mul {n k : ℕ} {A : Finset (Fin n)}
    (hA : A.card = k) (hn : n = 2 * k) : Aᶜ.card = k := by
  rw [card_compl, Fintype.card_fin, hA, hn, Nat.two_mul, Nat.add_sub_cancel]

lemma image_compl_subset_powersetCard {n k : ℕ} {F : Finset (Finset (Fin n))}
    (hn : n = 2 * k) (hU : IsKUniform F k) :
    F.image (compl : Finset (Fin n) → Finset (Fin n)) ⊆ univ.powersetCard k := by
  intro A hA
  rcases mem_image.mp hA with ⟨B, hB, rfl⟩
  exact mem_powersetCard.mpr ⟨subset_univ _, compl_card_of_two_mul (hU B hB) hn⟩

lemma disjoint_image_compl {n : ℕ} {F : Finset (Finset (Fin n))}
    (hI : Intersecting F) :
    Disjoint F (F.image (compl : Finset (Fin n) → Finset (Fin n))) := by
  rw [disjoint_left]
  intro A hA hAc
  rcases mem_image.mp hAc with ⟨B, hB, rfl⟩
  exact intersecting_not_compl_mem hI hB hA

/-- Pascal identity specialised: `C(2k, k) = 2 · C(2k-1, k-1)` for `k ≥ 1`. -/
lemma choose_two_mul_eq_two_choose (k : ℕ) (hk : 1 ≤ k) :
    Nat.choose (2 * k) k = 2 * Nat.choose (2 * k - 1) (k - 1) := by
  have h := Nat.succ_mul_choose_eq (2 * k - 1) (k - 1)
  have hs1 : Nat.succ (2 * k - 1) = 2 * k := by omega
  have hs2 : Nat.succ (k - 1) = k := by omega
  rw [hs1, hs2] at h
  have hkpos : 0 < k := hk
  apply Nat.eq_of_mul_eq_mul_right hkpos
  calc
    Nat.choose (2 * k) k * k
        = 2 * k * Nat.choose (2 * k - 1) (k - 1) := by
          rw [Nat.mul_comm, h, Nat.mul_comm]
    _ = 2 * Nat.choose (2 * k - 1) (k - 1) * k := by
          rw [Nat.mul_assoc, Nat.mul_comm k, Nat.mul_assoc,
            Nat.mul_comm (Nat.choose _ _) k]

/-- Level A: when `n = 2k`, an intersecting k-family takes at most one of each
complementary pair, hence has size at most `C(n-1, k-1)`.

The hypothesis `n = 2k` is a special case of the load-bearing `n ≥ 2k`.
The full range `2 * k ≤ n` is the Level B (Katona) residual. -/
theorem erdos_ko_rado_of_eq {n k : ℕ} {F : Finset (Finset (Fin n))}
    (hn : n = 2 * k) (hk : 1 ≤ k)
    (hU : IsKUniform F k) (hI : Intersecting F) :
    F.card ≤ Nat.choose (n - 1) (k - 1) := by
  have hdisj := disjoint_image_compl (n := n) hI
  have hsub : F ∪ F.image (compl : Finset (Fin n) → Finset (Fin n)) ⊆
      univ.powersetCard k :=
    union_subset (kUniform_subset_powersetCard hU) (image_compl_subset_powersetCard hn hU)
  have hcard_image : (F.image (compl : Finset (Fin n) → Finset (Fin n))).card = F.card :=
    card_image_of_injective F compl_injective
  have hle : 2 * F.card ≤ Nat.choose n k := by
    have hcard := card_le_card hsub
    rw [card_union_of_disjoint hdisj, hcard_image, card_powersetCard, card_univ,
      Fintype.card_fin] at hcard
    rw [Nat.two_mul]
    exact hcard
  have hid : Nat.choose n k = 2 * Nat.choose (n - 1) (k - 1) := by
    subst hn
    simpa [Nat.two_mul, Nat.add_sub_cancel] using choose_two_mul_eq_two_choose k hk
  have hkpos : 0 < 2 := by decide
  have h2 : 2 * F.card ≤ 2 * Nat.choose (n - 1) (k - 1) := by
    rw [← hid]; exact hle
  exact Nat.le_of_mul_le_mul_left h2 hkpos

end ProofLab.ErdosKoRado
