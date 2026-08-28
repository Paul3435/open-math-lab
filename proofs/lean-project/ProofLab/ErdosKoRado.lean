/-
Erdős–Ko–Rado (k-uniform intersecting families)

Formalization of: if `n ≥ 2k` and `1 ≤ k`, every intersecting family of
`k`-subsets of an `n`-set has size at most `Nat.choose (n-1) (k-1)`,
achieved by a star.  (Erdős–Ko–Rado 1961.)

status: known-classical, formalize-only, **no novelty claim**.
         Mathlib v4.10.0 has only the non-uniform bound
         `Set.Intersecting.card_le` (size ≤ 2^{n-1}); this file is the
         k-uniform bound and must not be cited as that theorem.

Level A: definitions + star meets the bound + `n = 2k` complementary pairing.
Level B (this PR): Katona cycle double-count for the full `n ≥ 2k` bound.
Zero `sorry`. Uniqueness of stars is out of v1.

Pin: `catalog/problems/erdos-ko-rado/STATEMENT.md` (OPE-541 / OPE-534 / Scout OPE-533).
Encoding: ground set `Fin n`; members are `Finset (Fin n)` of `card = k`.
          No `Sym` encoding. Cyclic orders are `Equiv.Perm (Fin n)`.
-/

import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

open Finset Equiv

namespace ProofLab.ErdosKoRado

/-!
# Erdős–Ko–Rado (k-uniform intersecting families)

## Main definitions

* `Intersecting F` — every two members of `F` have nonempty intersection
* `IsKUniform F k` — every member has cardinality `k`
* `star n k i` — all `k`-subsets of `Fin n` that contain `i`
* `cycleInterval k hk s` — the cyclic k-arc on `Fin n` starting at `s`

## Main results (zero `sorry`)

* `star_meets_bound` — a star has size `Nat.choose (n-1) (k-1)`
* `star_intersecting` / `star_kUniform` — a star is an intersecting k-family
* `erdos_ko_rado_of_eq` — the bound when `n = 2k` (complementary pairing)
* `erdos_ko_rado` — the bound when `2 * k ≤ n` (Katona cycle method)

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

The hypothesis `n = 2k` is a special case of the load-bearing `n ≥ 2k`. -/
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

/-! ## Level B: Katona cycle method for `n ≥ 2k`

Cyclic k-arcs on `Fin n`, circular packing (at most `k` arcs from an
intersecting family), then double-count pairs `(σ, s)` over
`Equiv.Perm (Fin n)`. Encoding stays `Finset (Fin n)`; no `Sym`.
-/

lemma k_lt_n_of {n k : ℕ} (hk : 1 ≤ k) (hn : 2 * k ≤ n) : k < n := by
  have : k + k ≤ n := by simpa [Nat.two_mul] using hn
  exact Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right hk) this

lemma two_k_le_n_k {n k : ℕ} (hn : 2 * k ≤ n) : k ≤ n - k := by omega

/-- Offset `i` steps from `s` on the cycle `Fin n`. -/
def cycleShift {n : ℕ} {k : ℕ} (hk : k ≤ n) (s : Fin n) (i : Fin k) : Fin n :=
  s + i.castLE hk

lemma cycleShift_injective {n k : ℕ} (hk : k ≤ n) (s : Fin n) :
    Function.Injective (cycleShift hk s) :=
  fun _ _ h => Fin.castLE_injective hk (add_right_injective s h)

/-- The k consecutive residues on the cycle `Fin n` starting at `s`. -/
def cycleInterval {n : ℕ} (k : ℕ) (hk : k ≤ n) (s : Fin n) : Finset (Fin n) :=
  (univ : Finset (Fin k)).map ⟨cycleShift hk s, cycleShift_injective hk s⟩

lemma card_cycleInterval {n k : ℕ} (hk : k ≤ n) (s : Fin n) :
    (cycleInterval k hk s).card = k := by
  simp [cycleInterval, card_univ, Fintype.card_fin]

lemma val_add_of_add_lt {n : ℕ} {a b : Fin n} (h : a.val + b.val < n) :
    (a + b).val = a.val + b.val := by
  rw [Fin.val_add, Nat.mod_eq_of_lt h]

lemma val_sub_eq {n : ℕ} [NeZero n] (a b : Fin n) :
    (a - b).val = (a.val + n - b.val) % n := by
  rw [sub_eq_add_neg, Fin.val_add]
  have hneg : (-b).val = (n - b.val) % n := by
    simp [Fin.neg_def]
  rw [hneg, Nat.add_mod_mod]
  have hb : b.val ≤ n := Nat.le_of_lt b.isLt
  rw [Nat.add_sub_assoc hb]

lemma sub_eq_sub_sub {n : ℕ} [NeZero n] (t1 t2 s0 : Fin n) :
    t1 - t2 = (t1 - s0) - (t2 - s0) :=
  (sub_sub_sub_cancel_right t1 t2 s0).symm

lemma mem_cycleInterval {n k : ℕ} [NeZero n] (hk : k ≤ n) (s x : Fin n) :
    x ∈ cycleInterval k hk s ↔ (x - s).val < k := by
  constructor
  · intro hx
    rcases mem_map.mp hx with ⟨i, _, hix⟩
    -- `hix : cycleShift hk s i = x`
    have hx' : x = s + i.castLE hk := hix.symm
    have hcancel : s + i.castLE hk - s = i.castLE hk := add_sub_cancel_left s _
    have hval : (i.castLE hk).val = i.val := rfl
    rw [hx', hcancel, hval]
    exact i.isLt
  · intro h
    refine mem_map.mpr ⟨⟨(x - s).val, h⟩, mem_univ _, ?_⟩
    change s + (⟨(x - s).val, h⟩ : Fin k).castLE hk = x
    have hcast : (⟨(x - s).val, h⟩ : Fin k).castLE hk = x - s := by
      ext
      rfl
    rw [hcast, add_comm, sub_add_cancel]

lemma cycleInterval_disjoint_of_dist {n k : ℕ} [NeZero n] (hk : k ≤ n)
    (hk1 : 1 ≤ k) {a b : Fin n}
    (hd : k ≤ (b - a).val) (hd' : (b - a).val ≤ n - k) :
    cycleInterval k hk a ∩ cycleInterval k hk b = ∅ := by
  ext x
  simp only [mem_inter, mem_cycleInterval hk, not_mem_empty, iff_false, not_and]
  intro hxa hxb
  have hxab : x - a = (x - b) + (b - a) := by
    simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, add_left_neg, add_zero]
  have hsum : (x - b).val + (b - a).val < n := by
    have : (x - b).val + (b - a).val ≤ (k - 1) + (n - k) :=
      Nat.add_le_add (Nat.le_pred_of_lt hxb) hd'
    have : (k - 1) + (n - k) = n - 1 := by omega
    omega
  have hval : (x - a).val = (x - b).val + (b - a).val := by
    rw [hxab, val_add_of_add_lt hsum]
  have : k ≤ (x - a).val := by
    rw [hval]
    exact Nat.le_trans hd (Nat.le_add_left _ _)
  exact Nat.not_lt.mpr this hxa

lemma cycle_dist_of_intersect {n k : ℕ} [NeZero n] (hk : k ≤ n) (hk1 : 1 ≤ k)
    {a b : Fin n} (hne : cycleInterval k hk a ∩ cycleInterval k hk b ≠ ∅) :
    (b - a).val < k ∨ n - k < (b - a).val := by
  by_contra h
  push_neg at h
  exact hne (cycleInterval_disjoint_of_dist hk hk1 h.1 h.2)

/-- Katona packing key: offset of `t` from `s0`, folded so intersecting
starts land in `{0, …, k-1}`. -/
def packVal {n : ℕ} (k : ℕ) (s0 t : Fin n) : ℕ :=
  let d := (t - s0).val
  if d < k then d else k + d - n

lemma packVal_lt {n k : ℕ} [NeZero n] {s0 t : Fin n}
    (hk : k ≤ n) (hk1 : 1 ≤ k) (_hn : 2 * k ≤ n)
    (hmeet : cycleInterval k hk s0 ∩ cycleInterval k hk t ≠ ∅) :
    packVal k s0 t < k := by
  have hdist := cycle_dist_of_intersect hk hk1 hmeet
  dsimp [packVal]
  split_ifs with h
  · exact h
  · have : n - k < (t - s0).val := hdist.resolve_left h
    omega

lemma packVal_inj {n k : ℕ} [NeZero n] {F : Finset (Finset (Fin n))} {s0 : Fin n}
    (hk : k ≤ n) (hk1 : 1 ≤ k) (hn : 2 * k ≤ n) (hI : Intersecting F)
    (hs0 : cycleInterval k hk s0 ∈ F) :
    Set.InjOn (packVal k s0)
      {s : Fin n | cycleInterval k hk s ∈ F} := by
  intro t1 ht1 t2 ht2 heq
  have hmeet1 : cycleInterval k hk s0 ∩ cycleInterval k hk t1 ≠ ∅ :=
    hI _ hs0 _ ht1
  have hmeet2 : cycleInterval k hk s0 ∩ cycleInterval k hk t2 ≠ ∅ :=
    hI _ hs0 _ ht2
  have hd1 := cycle_dist_of_intersect hk hk1 hmeet1
  have hd2 := cycle_dist_of_intersect hk hk1 hmeet2
  have klt : k < n := k_lt_n_of hk1 hn
  have knk : k ≤ n - k := two_k_le_n_k hn
  dsimp [packVal] at heq
  have ht : t1 - s0 = t2 - s0 → t1 = t2 := fun h => sub_left_inj.mp h
  by_cases h1 : (t1 - s0).val < k
  · by_cases h2 : (t2 - s0).val < k
    · simp [h1, h2] at heq
      exact ht (Fin.ext heq)
    · simp [h1, h2] at heq
      have hd2gt : n - k < (t2 - s0).val := hd2.resolve_left h2
      have hval : (t1 - t2).val = k := by
        rw [sub_eq_sub_sub t1 t2 s0, val_sub_eq]
        have : (t1 - s0).val + n - (t2 - s0).val = k := by omega
        rw [this, Nat.mod_eq_of_lt klt]
      have hdisj :=
        cycleInterval_disjoint_of_dist (a := t2) (b := t1) hk hk1
          (by omega) (by simpa [hval] using knk)
      exact (hI _ ht2 _ ht1 hdisj).elim
  · by_cases h2 : (t2 - s0).val < k
    · simp [h1, h2] at heq
      have hd1gt : n - k < (t1 - s0).val := hd1.resolve_left h1
      have hval : (t2 - t1).val = k := by
        rw [sub_eq_sub_sub t2 t1 s0, val_sub_eq]
        have : (t2 - s0).val + n - (t1 - s0).val = k := by omega
        rw [this, Nat.mod_eq_of_lt klt]
      have hdisj :=
        cycleInterval_disjoint_of_dist (a := t1) (b := t2) hk hk1
          (by omega) (by simpa [hval] using knk)
      exact (hI _ ht1 _ ht2 hdisj).elim
    · simp [h1, h2] at heq
      have hd1gt : n - k < (t1 - s0).val := hd1.resolve_left h1
      have hd2gt : n - k < (t2 - s0).val := hd2.resolve_left h2
      have : (t1 - s0).val = (t2 - s0).val := by omega
      exact ht (Fin.ext this)

/-- Katona packing: on one cycle, an intersecting family contains at most
`k` of the `n` cyclic k-arcs. Load-bearing `n ≥ 2k`. -/
lemma circular_packing {n k : ℕ} [NeZero n] {F : Finset (Finset (Fin n))}
    (hk : k ≤ n) (hk1 : 1 ≤ k) (hn : 2 * k ≤ n) (hI : Intersecting F) :
    (univ.filter (fun s : Fin n => cycleInterval k hk s ∈ F)).card ≤ k := by
  set S := univ.filter (fun s : Fin n => cycleInterval k hk s ∈ F)
  by_cases hne : S.Nonempty
  · obtain ⟨s0, hs0⟩ := hne
    have hs0F : cycleInterval k hk s0 ∈ F := (mem_filter.mp hs0).2
    have himg : S.image (packVal k s0) ⊆ range k := by
      intro y hy
      rcases mem_image.mp hy with ⟨t, ht, rfl⟩
      have htF : cycleInterval k hk t ∈ F := (mem_filter.mp ht).2
      exact mem_range.mpr
        (packVal_lt hk hk1 hn (hI _ hs0F _ htF))
    have hinj : Set.InjOn (packVal k s0) (S : Set (Fin n)) := by
      intro t1 ht1 t2 ht2 heq
      have ht1F : cycleInterval k hk t1 ∈ F := (mem_filter.mp ht1).2
      have ht2F : cycleInterval k hk t2 ∈ F := (mem_filter.mp ht2).2
      exact packVal_inj hk hk1 hn hI hs0F ht1F ht2F heq
    have hcard := (card_image_of_injOn hinj).symm
    have : (S.image (packVal k s0)).card ≤ (range k).card := card_le_card himg
    simpa [hcard, card_range] using this
  · have : S = ∅ := not_nonempty_iff_eq_empty.mp hne
    simp [this]

lemma map_map_toEmbedding {α : Type*} [DecidableEq α] (σ : Perm α) (A : Finset α) :
    (A.map σ.symm.toEmbedding).map σ.toEmbedding = A := by
  rw [map_map]
  ext x
  simp

lemma map_map_toEmbedding_symm {α : Type*} [DecidableEq α] (σ : Perm α) (A : Finset α) :
    (A.map σ.toEmbedding).map σ.symm.toEmbedding = A := by
  rw [map_map]
  ext x
  simp

lemma map_inter_embedding {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α ↪ β) (A B : Finset α) :
    (A ∩ B).map f = A.map f ∩ B.map f := by
  ext y
  simp [mem_map, mem_inter, and_assoc]
  constructor
  · rintro ⟨x, hxA, hxB, rfl⟩
    exact ⟨⟨x, hxA, rfl⟩, ⟨x, hxB, rfl⟩⟩
  · rintro ⟨⟨x, hxA, hx⟩, ⟨z, hzB, hz⟩⟩
    have : x = z := f.injective (hx.trans hz.symm)
    subst this
    exact ⟨x, hxA, hzB, hx⟩

lemma pull_intersecting {n : ℕ} {F : Finset (Finset (Fin n))}
    (hI : Intersecting F) (σ : Perm (Fin n)) :
    Intersecting (F.image fun A => A.map σ.symm.toEmbedding) := by
  intro A hA B hB hdisj
  rcases mem_image.mp hA with ⟨A0, hA0, rfl⟩
  rcases mem_image.mp hB with ⟨B0, hB0, rfl⟩
  have hmeet : A0 ∩ B0 ≠ ∅ := hI A0 hA0 B0 hB0
  have himg : (A0 ∩ B0).map σ.symm.toEmbedding ≠ ∅ := by
    intro hempty
    exact hmeet (map_eq_empty.mp hempty)
  have : (A0 ∩ B0).map σ.symm.toEmbedding =
      A0.map σ.symm.toEmbedding ∩ B0.map σ.symm.toEmbedding :=
    map_inter_embedding _ _ _
  rw [this] at himg
  exact himg hdisj

lemma mem_pull {n : ℕ} {F : Finset (Finset (Fin n))} {σ : Perm (Fin n)}
    {B : Finset (Fin n)} :
    B ∈ F.image (fun A => A.map σ.symm.toEmbedding) ↔
      B.map σ.toEmbedding ∈ F := by
  constructor
  · intro h
    rcases mem_image.mp h with ⟨A, hA, rfl⟩
    simpa [map_map_toEmbedding] using hA
  · intro h
    refine mem_image.mpr ⟨B.map σ.toEmbedding, h, map_map_toEmbedding_symm σ B⟩

lemma packing_on_perm {n k : ℕ} [NeZero n] {F : Finset (Finset (Fin n))}
    (hk : k ≤ n) (hk1 : 1 ≤ k) (hn : 2 * k ≤ n) (hI : Intersecting F)
    (σ : Perm (Fin n)) :
    (univ.filter (fun s : Fin n =>
      (cycleInterval k hk s).map σ.toEmbedding ∈ F)).card ≤ k := by
  let F' := F.image fun A => A.map σ.symm.toEmbedding
  have hI' : Intersecting F' := pull_intersecting hI σ
  have hpack := circular_packing (F := F') hk hk1 hn hI'
  have hfilter :
      univ.filter (fun s : Fin n => (cycleInterval k hk s).map σ.toEmbedding ∈ F) =
        univ.filter (fun s : Fin n => cycleInterval k hk s ∈ F') := by
    ext s
    simp only [mem_filter, mem_univ, true_and]
    exact (mem_pull (F := F) (σ := σ) (B := cycleInterval k hk s)).symm
  rwa [hfilter]

/-! ### Counting permutations that send one k-set onto another -/

lemma subtypeCongr_apply_mem {α : Type*} [DecidableEq α]
    {S T : Finset α} (e : { x // x ∈ S } ≃ { x // x ∈ T })
    (f : { x // x ∉ S } ≃ { x // x ∉ T }) {x : α} (hx : x ∈ S) :
    Equiv.subtypeCongr e f x = (e ⟨x, hx⟩ : α) := by
  simp [Equiv.subtypeCongr, Equiv.trans_apply,
    Equiv.sumCompl_apply_symm_of_pos (fun y => y ∈ S) x hx]

lemma subtypeCongr_apply_not_mem {α : Type*} [DecidableEq α]
    {S T : Finset α} (e : { x // x ∈ S } ≃ { x // x ∈ T })
    (f : { x // x ∉ S } ≃ { x // x ∉ T }) {x : α} (hx : x ∉ S) :
    Equiv.subtypeCongr e f x = (f ⟨x, hx⟩ : α) := by
  simp [Equiv.subtypeCongr, Equiv.trans_apply,
    Equiv.sumCompl_apply_symm_of_neg (fun y => y ∈ S) x hx]

lemma mem_iff_of_map {α : Type*} [DecidableEq α]
    {S T : Finset α} {σ : Perm α} (h : S.map σ.toEmbedding = T) (x : α) :
    x ∈ S ↔ σ x ∈ T := by
  constructor
  · intro hx
    have : σ x ∈ S.map σ.toEmbedding := mem_map.mpr ⟨x, hx, rfl⟩
    rwa [h] at this
  · intro hx
    have : σ x ∈ S.map σ.toEmbedding := by rwa [h]
    rcases mem_map.mp this with ⟨z, hz, heq⟩
    have : z = x := σ.injective heq
    rwa [← this]

/-- Permutations sending `S` onto `T` are pairs of bijections `S ≃ T` and
`Sᶜ ≃ Tᶜ`. Used to count `k! · (n-k)!` placements of a k-set. -/
def equivPermsMapsTo {α : Type*} [DecidableEq α] [Fintype α]
    (S T : Finset α) :
    {σ : Perm α // S.map σ.toEmbedding = T} ≃
      (({ x // x ∈ S } ≃ { x // x ∈ T }) × ({ x // x ∉ S } ≃ { x // x ∉ T })) where
  toFun := fun ⟨σ, hσ⟩ =>
    ⟨σ.subtypeEquiv (fun a => mem_iff_of_map hσ a),
      σ.subtypeEquiv (fun a => (mem_iff_of_map hσ a).not)⟩
  invFun := fun ⟨e, f⟩ =>
    ⟨Equiv.subtypeCongr e f, by
      apply eq_of_subset_of_card_le
      · intro y hy
        rcases mem_map.mp hy with ⟨x, hx, hxy⟩
        have : Equiv.subtypeCongr e f x = y := hxy
        rw [← this, subtypeCongr_apply_mem e f hx]
        exact (e ⟨x, hx⟩).property
      · rw [card_map]
        exact Nat.le_of_eq <|
          ((Fintype.card_coe S).symm.trans <|
            (Fintype.card_congr e).trans (Fintype.card_coe T)).symm⟩
  left_inv := by
    rintro ⟨σ, hσ⟩
    apply Subtype.ext
    ext x
    by_cases hx : x ∈ S
    · simp [subtypeCongr_apply_mem _ _ hx, Equiv.subtypeEquiv_apply]
    · simp [subtypeCongr_apply_not_mem _ _ hx, Equiv.subtypeEquiv_apply]
  right_inv := by
    rintro ⟨e, f⟩
    refine Prod.ext ?_ ?_
    · ext x
      simp [Equiv.subtypeEquiv_apply, subtypeCongr_apply_mem e f x.property]
    · ext x
      simp [Equiv.subtypeEquiv_apply, subtypeCongr_apply_not_mem e f x.property]

lemma card_subtype_not_mem {α : Type*} [DecidableEq α] [Fintype α] (S : Finset α) :
    Fintype.card { x // x ∉ S } = Fintype.card α - S.card := by
  rw [Fintype.card_subtype]
  have : univ.filter (fun x : α => x ∉ S) = Sᶜ := by
    ext x; simp
  rw [this, card_compl]

lemma card_equiv_of_card_eq {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (h : Fintype.card α = Fintype.card β) :
    Fintype.card (α ≃ β) = (Fintype.card α).factorial :=
  Fintype.card_equiv (Fintype.equivOfCardEq h)

lemma card_perms_maps_to {α : Type*} [DecidableEq α] [Fintype α]
    (S T : Finset α) (hST : S.card = T.card) :
    Fintype.card {σ : Perm α // S.map σ.toEmbedding = T} =
      S.card.factorial * (Fintype.card α - S.card).factorial := by
  rw [Fintype.card_congr (equivPermsMapsTo S T), Fintype.card_prod]
  have hS : Fintype.card { x // x ∈ S } = S.card := Fintype.card_coe S
  have hT : Fintype.card { x // x ∈ T } = T.card := Fintype.card_coe T
  have hSc : Fintype.card { x // x ∉ S } = Fintype.card α - S.card :=
    card_subtype_not_mem S
  have hTc : Fintype.card { x // x ∉ T } = Fintype.card α - T.card :=
    card_subtype_not_mem T
  have h1 : Fintype.card ({ x // x ∈ S } ≃ { x // x ∈ T }) = S.card.factorial := by
    rw [card_equiv_of_card_eq (hS.trans (hST.trans hT.symm)), hS]
  have h2 : Fintype.card ({ x // x ∉ S } ≃ { x // x ∉ T }) =
      (Fintype.card α - S.card).factorial := by
    have : Fintype.card α - S.card = Fintype.card α - T.card := by rw [hST]
    rw [card_equiv_of_card_eq (hSc.trans (this.trans hTc.symm)), hSc]
  rw [h1, h2]

lemma card_fiber_interval {n k : ℕ} [NeZero n] (hk : k ≤ n)
    {A : Finset (Fin n)} (hA : A.card = k) :
    Fintype.card
      {p : Perm (Fin n) × Fin n //
        (cycleInterval k hk p.2).map p.1.toEmbedding = A} =
      n * k.factorial * (n - k).factorial := by
  let e :
      {p : Perm (Fin n) × Fin n //
        (cycleInterval k hk p.2).map p.1.toEmbedding = A} ≃
      (s : Fin n) × {σ : Perm (Fin n) //
        (cycleInterval k hk s).map σ.toEmbedding = A} :=
    { toFun := fun ⟨p, hp⟩ => ⟨p.2, ⟨p.1, hp⟩⟩
      invFun := fun ⟨s, σ⟩ => ⟨(σ.1, s), σ.2⟩
      left_inv := fun ⟨p, _⟩ => by cases p; rfl
      right_inv := fun ⟨_, σ⟩ => by cases σ; rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  have : ∀ s : Fin n,
      Fintype.card {σ : Perm (Fin n) //
        (cycleInterval k hk s).map σ.toEmbedding = A} =
        k.factorial * (n - k).factorial := by
    intro s
    simpa [card_cycleInterval hk s, Fintype.card_fin, hA] using
      card_perms_maps_to (cycleInterval k hk s) A
        (by rw [card_cycleInterval hk s, hA])
  simp [this, Fintype.card_fin, mul_comm, mul_left_comm, mul_assoc]

lemma card_pairs_in_F {n k : ℕ} [NeZero n] {F : Finset (Finset (Fin n))}
    (hk : k ≤ n) (hU : IsKUniform F k) :
    Fintype.card
      {p : Perm (Fin n) × Fin n //
        (cycleInterval k hk p.2).map p.1.toEmbedding ∈ F} =
      F.card * n * k.factorial * (n - k).factorial := by
  let f : Perm (Fin n) × Fin n → Finset (Fin n) := fun p =>
    (cycleInterval k hk p.2).map p.1.toEmbedding
  -- Fiberwise count over members of F.
  have hsum :
      (univ.filter (fun p : Perm (Fin n) × Fin n => f p ∈ F)).card =
        ∑ A ∈ F, (univ.filter (fun p : Perm (Fin n) × Fin n => f p = A)).card := by
    have hall : ∀ p ∈ univ.filter (fun p : Perm (Fin n) × Fin n => f p ∈ F),
        f p ∈ F := fun p hp => (mem_filter.mp hp).2
    have h :=
      card_eq_sum_card_fiberwise (s := univ.filter (fun p => f p ∈ F))
        (t := F) (f := f) hall
    refine h.trans (sum_congr rfl fun A hA => congrArg card ?_)
    ext p
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · exact And.right
    · intro heq
      exact ⟨heq ▸ hA, heq⟩
  -- Identify subtype card with the filtered univ.
  have hleft :
      Fintype.card {p : Perm (Fin n) × Fin n // f p ∈ F} =
        (univ.filter (fun p : Perm (Fin n) × Fin n => f p ∈ F)).card :=
    Fintype.card_subtype _
  have hfiber : ∀ A ∈ F,
      (univ.filter (fun p : Perm (Fin n) × Fin n => f p = A)).card =
        n * k.factorial * (n - k).factorial := by
    intro A hA
    have := card_fiber_interval (A := A) hk (hU A hA)
    simpa [f, Fintype.card_subtype] using this
  calc
    Fintype.card {p : Perm (Fin n) × Fin n // f p ∈ F}
        = (univ.filter (fun p : Perm (Fin n) × Fin n => f p ∈ F)).card := hleft
    _ = ∑ A ∈ F, (univ.filter (fun p : Perm (Fin n) × Fin n => f p = A)).card := hsum
    _ = ∑ _A ∈ F, n * k.factorial * (n - k).factorial :=
          sum_congr rfl fun A hA => hfiber A hA
    _ = F.card * (n * k.factorial * (n - k).factorial) := by
          simp [sum_const, nsmul_eq_mul]
    _ = F.card * n * k.factorial * (n - k).factorial := by ring

lemma card_pairs_le {n k : ℕ} [NeZero n] {F : Finset (Finset (Fin n))}
    (hk : k ≤ n) (hk1 : 1 ≤ k) (hn : 2 * k ≤ n) (hI : Intersecting F) :
    Fintype.card
      {p : Perm (Fin n) × Fin n //
        (cycleInterval k hk p.2).map p.1.toEmbedding ∈ F} ≤
      k * n.factorial := by
  let e :
      {p : Perm (Fin n) × Fin n //
        (cycleInterval k hk p.2).map p.1.toEmbedding ∈ F} ≃
      (σ : Perm (Fin n)) ×
        {s : Fin n // (cycleInterval k hk s).map σ.toEmbedding ∈ F} :=
    { toFun := fun ⟨p, hp⟩ => ⟨p.1, ⟨p.2, hp⟩⟩
      invFun := fun ⟨σ, s⟩ => ⟨(σ, s.1), s.2⟩
      left_inv := fun ⟨p, _⟩ => by cases p; rfl
      right_inv := fun ⟨_, s⟩ => by cases s; rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  have hpack : ∀ σ : Perm (Fin n),
      Fintype.card {s : Fin n // (cycleInterval k hk s).map σ.toEmbedding ∈ F} ≤ k := by
    intro σ
    have := packing_on_perm (F := F) hk hk1 hn hI σ
    rwa [Fintype.card_subtype]
  calc
    ∑ σ : Perm (Fin n),
        Fintype.card {s : Fin n //
          (cycleInterval k hk s).map σ.toEmbedding ∈ F}
        ≤ ∑ _σ : Perm (Fin n), k :=
      Finset.sum_le_sum fun σ _ => hpack σ
    _ = Fintype.card (Perm (Fin n)) * k := by
          simp [sum_const, card_univ]
    _ = n.factorial * k := by
          rw [Fintype.card_perm, Fintype.card_fin]
    _ = k * n.factorial := by ring

/-- Level B: Katona cycle proof of the k-uniform EKR bound for `n ≥ 2k`.

Known-classical (Katona 1972 / EKR 1961). **No novelty claim.**
Do not cite `Set.Intersecting.card_le`. Uniqueness of stars is out of v1. -/
theorem erdos_ko_rado {n k : ℕ} {F : Finset (Finset (Fin n))}
    (hn : 2 * k ≤ n) (hk : 1 ≤ k)
    (hU : IsKUniform F k) (hI : Intersecting F) :
    F.card ≤ Nat.choose (n - 1) (k - 1) := by
  have npos : 0 < n := lt_of_le_of_lt (Nat.zero_le k) (k_lt_n_of hk hn)
  haveI : NeZero n := ⟨ne_of_gt npos⟩
  have hk_le : k ≤ n :=
    Nat.le_trans (Nat.le_mul_of_pos_left k (by decide : 0 < 2)) hn
  have hcount := card_pairs_in_F (F := F) hk_le hU
  have hle := card_pairs_le (F := F) hk_le hk hn hI
  have hineq :
      F.card * n * k.factorial * (n - k).factorial ≤ k * n.factorial := by
    simpa [hcount] using hle
  have hkfac : k.factorial = k * (k - 1).factorial :=
    (Nat.mul_factorial_pred (Nat.pos_iff_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp hk))).symm
  have hnfac : n.factorial = n * (n - 1).factorial :=
    (Nat.mul_factorial_pred npos).symm
  have hineq' :
      F.card * (k - 1).factorial * (n - k).factorial ≤ (n - 1).factorial := by
    have hpos_n : 0 < n := npos
    have hpos_k : 0 < k := hk
    have hexp : F.card * n * (k * (k - 1).factorial) * (n - k).factorial ≤
        k * (n * (n - 1).factorial) := by
      simpa [hkfac, hnfac, Nat.mul_assoc] using hineq
    have hrearr :
        n * k * (F.card * (k - 1).factorial * (n - k).factorial) ≤
          n * k * (n - 1).factorial := by
      convert hexp using 1 <;> ring
    exact Nat.le_of_mul_le_mul_left hrearr (Nat.mul_pos hpos_n hpos_k)
  have hchoosefac :
      Nat.choose (n - 1) (k - 1) * (k - 1).factorial * (n - k).factorial =
        (n - 1).factorial := by
    have hle' : k - 1 ≤ n - 1 := Nat.sub_le_sub_right hk_le 1
    have := Nat.choose_mul_factorial_mul_factorial hle'
    have hsub : n - 1 - (k - 1) = n - k := by omega
    simpa [hsub] using this
  have hpos : 0 < (k - 1).factorial * (n - k).factorial :=
    Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
  have :
      F.card * ((k - 1).factorial * (n - k).factorial) ≤
        Nat.choose (n - 1) (k - 1) * ((k - 1).factorial * (n - k).factorial) := by
    calc
      F.card * ((k - 1).factorial * (n - k).factorial)
          = F.card * (k - 1).factorial * (n - k).factorial := by ring
      _ ≤ (n - 1).factorial := hineq'
      _ = Nat.choose (n - 1) (k - 1) * (k - 1).factorial * (n - k).factorial :=
            hchoosefac.symm
      _ = Nat.choose (n - 1) (k - 1) *
            ((k - 1).factorial * (n - k).factorial) := by ring
  exact Nat.le_of_mul_le_mul_right this hpos

end ProofLab.ErdosKoRado
