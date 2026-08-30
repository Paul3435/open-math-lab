/-
Erdős–Rado sunflower lemma (1960): an `r`-uniform family larger than
`r! (k-1)^r` contains a sunflower with `k` petals.

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 has `Finset` / `Nat.factorial` / `Nat.pow` and ZERO sunflower /
Δ-system / `IsSunflower` / Erdős–Rado sunflower ident.

Pin: `catalog/problems/sunflower-erdos-rado/STATEMENT.md` (OPE-722; Scout
OPE-717 prime; Director OPE-721). Encoding: ground type `α` with `DecidableEq`;
family `𝒜 : Finset (Finset α)`; uniformity `s.card = r`. Sunflower / Δ-system:
pairwise intersections equal a common core. Empty core allowed. `|𝒜| ≤ 1` is
vacuously a sunflower (no pairs). Zero `sorry`. Do not import `Archive.*`.

This is **not** the sunflower conjecture (open, out of v1) and **not** ALWZ 2021.
This is **not** EKR (`ProofLab/ErdosKoRado.lean`).
This is **not** Oddtown / Eventown / Fisher / BIBD.
This is **not** Kruskal–Katona / Sperner / LYM / Sauer–Shelah.
This is **not** Hilton–Milner. This is **not** combinatorial Nullstellensatz.
Petal count `k`, uniformity `r`. `1 ≤ k` is load-bearing for `ℕ` subtraction.
`r = 0` is allowed (only `∅` has card 0).

Level A: `k = 1`; `r = 0`; `r = 1` singletons; empty family. Zero sorry.
Not labelled Erdős–Rado.
Level B: namesake `erdos_rado_sunflower` by induction on `r` (popular point →
traces; otherwise a maximum pairwise-disjoint subfamily yields `k` empty-core
petals, or else the degree bound contradicts the strict cardinality hypothesis).
-/
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

set_option maxHeartbeats 800000

open Finset

noncomputable section
open Classical

namespace ProofLab.Sunflower

variable {α : Type*} [DecidableEq α]

/-! ## Predicate (STATEMENT pin) -/

/-- Pairwise intersections equal a common core. Empty core allowed (pairwise
disjoint petals). `|𝒜| ≤ 1` is vacuously a sunflower (no pairs). -/
def IsSunflower (𝒜 : Finset (Finset α)) : Prop :=
  ∃ core : Finset α, ∀ ⦃s t⦄, s ∈ 𝒜 → t ∈ 𝒜 → s ≠ t → s ∩ t = core

/-- Pairwise empty intersections. Engine for empty-core sunflowers. -/
def PairwiseDisjointSets (𝒜 : Finset (Finset α)) : Prop :=
  ∀ ⦃s t⦄, s ∈ 𝒜 → t ∈ 𝒜 → s ≠ t → s ∩ t = (∅ : Finset α)

/-! ## Level A: empty / card ≤ 1 / `k = 1` / `r = 0` / `r = 1` (not labelled Erdős–Rado) -/

/-- A family of cardinality at most 1 is a sunflower (no pairs). Glue. -/
theorem isSunflower_of_card_le_one {𝒜 : Finset (Finset α)} (h : 𝒜.card ≤ 1) :
    IsSunflower 𝒜 := by
  refine ⟨∅, ?_⟩
  intro s t hs ht hne
  exact (hne ((card_le_one.mp h) s hs t ht)).elim

/-- The empty family is a sunflower. Glue. -/
theorem isSunflower_empty : IsSunflower (∅ : Finset (Finset α)) :=
  isSunflower_of_card_le_one (by simp)

/-- A singleton family is a sunflower. Glue. -/
theorem isSunflower_singleton (s : Finset α) : IsSunflower ({s} : Finset (Finset α)) :=
  isSunflower_of_card_le_one (by simp)

/-- Pairwise-disjoint families are empty-core sunflowers. Glue. -/
theorem isSunflower_of_pairwise_disjoint {𝒜 : Finset (Finset α)}
    (h : PairwiseDisjointSets 𝒜) : IsSunflower 𝒜 :=
  ⟨∅, h⟩

/-- The empty family is pairwise disjoint. Glue. -/
theorem pairwiseDisjoint_empty : PairwiseDisjointSets (∅ : Finset (Finset α)) := by
  intro s t hs _ht _hne
  exact (not_mem_empty s hs).elim

/-- From a nonempty family, take a 1-petal (vacuous) sunflower. Glue for `k = 1`. -/
theorem exists_petal_one {𝒜 : Finset (Finset α)} (h𝒜 : 𝒜.Nonempty) :
    ∃ 𝒮 ⊆ 𝒜, 𝒮.card = 1 ∧ IsSunflower 𝒮 := by
  obtain ⟨s, hs⟩ := h𝒜
  exact ⟨{s}, singleton_subset_iff.mpr hs, by simp, isSunflower_singleton s⟩

/-- The empty family's card cannot beat any bound. Glue. -/
theorem empty_family_bound_unsat {r k : ℕ}
    (hcard : Nat.factorial r * (k - 1) ^ r < (∅ : Finset (Finset α)).card) : False := by
  simp at hcard

/-- A 0-uniform family is contained in `{∅}`. Glue. -/
theorem r_zero_subset_empty {𝒜 : Finset (Finset α)}
    (hr : ∀ s ∈ 𝒜, s.card = 0) : 𝒜 ⊆ {∅} := by
  intro s hs
  simp [card_eq_zero.mp (hr s hs)]

/-- A 0-uniform family has size at most 1. Glue. -/
theorem r_zero_card_le_one {𝒜 : Finset (Finset α)}
    (hr : ∀ s ∈ 𝒜, s.card = 0) : 𝒜.card ≤ 1 :=
  (card_le_card (r_zero_subset_empty hr)).trans (by simp)

/-- `r = 0`: the bound is `0! (k-1)^0 = 1`, so `1 < |𝒜|` cannot hold. Glue. -/
theorem r_zero_bound_unsat {k : ℕ} {𝒜 : Finset (Finset α)}
    (hr : ∀ s ∈ 𝒜, s.card = 0)
    (hcard : Nat.factorial 0 * (k - 1) ^ 0 < 𝒜.card) : False := by
  have : 𝒜.card ≤ 1 := r_zero_card_le_one hr
  simp [Nat.factorial_zero, pow_zero] at hcard
  omega

/-- `k = 1`: if `r = 0` the bound cannot fire; if `r ≥ 1` then `0^r = 0` so the
family is nonempty and a singleton subfamily works. Glue, not Erdős–Rado. -/
theorem sunflower_k_one {r : ℕ} {𝒜 : Finset (Finset α)}
    (hr : ∀ s ∈ 𝒜, s.card = r)
    (hcard : Nat.factorial r * (1 - 1) ^ r < 𝒜.card) :
    ∃ 𝒮 ⊆ 𝒜, 𝒮.card = 1 ∧ IsSunflower 𝒮 := by
  cases r with
  | zero =>
    exact (r_zero_bound_unsat (k := 1) hr (by simpa using hcard)).elim
  | succ r =>
    have hpos : 0 < 𝒜.card := by
      simpa [Nat.sub_self, pow_succ, mul_zero] using hcard
    exact exists_petal_one (card_pos.mp hpos)

/-- Distinct singletons are disjoint. Glue. -/
theorem singleton_inter_eq_empty {a b : α} (h : a ≠ b) :
    ({a} : Finset α) ∩ {b} = ∅ :=
  singleton_inter_of_not_mem (by simpa using h)

/-- An `r = 1` family is pairwise disjoint. Glue. -/
theorem r_one_pairwise_disjoint {𝒜 : Finset (Finset α)}
    (hr : ∀ s ∈ 𝒜, s.card = 1) : PairwiseDisjointSets 𝒜 := by
  intro s t hs ht hne
  obtain ⟨a, rfl⟩ := card_eq_one.mp (hr s hs)
  obtain ⟨b, rfl⟩ := card_eq_one.mp (hr t ht)
  have hab : a ≠ b := fun h => hne (by rw [h])
  exact singleton_inter_eq_empty hab

/-- `r = 1`: more than `k - 1` distinct singletons yields `k` pairwise disjoint
petals. Glue, not Erdős–Rado. -/
theorem sunflower_r_one {k : ℕ} {𝒜 : Finset (Finset α)}
    (hr : ∀ s ∈ 𝒜, s.card = 1)
    (hk : 1 ≤ k)
    (hcard : Nat.factorial 1 * (k - 1) ^ 1 < 𝒜.card) :
    ∃ 𝒮 ⊆ 𝒜, 𝒮.card = k ∧ IsSunflower 𝒮 := by
  have hkA : k ≤ 𝒜.card := by
    simp only [Nat.factorial_one, pow_one, one_mul] at hcard
    omega
  obtain ⟨𝒮, hsub, h𝒮⟩ := exists_subset_card_eq hkA
  refine ⟨𝒮, hsub, h𝒮, isSunflower_of_pairwise_disjoint ?_⟩
  intro s t hs ht hne
  exact r_one_pairwise_disjoint hr (hsub hs) (hsub ht) hne

/-! ## Engine: degree, traces, maximum disjoint subfamily -/

/-- Number of members of `𝒜` containing `x`. -/
def degree (𝒜 : Finset (Finset α)) (x : α) : ℕ :=
  (𝒜.filter (fun s => x ∈ s)).card

/-- Traces of members through `x`: `{s \ {x} | x ∈ s ∈ 𝒜}`. -/
def traces (𝒜 : Finset (Finset α)) (x : α) : Finset (Finset α) :=
  (𝒜.filter (fun s => x ∈ s)).image (fun s => s.erase x)

lemma mem_traces {𝒜 : Finset (Finset α)} {x : α} {t : Finset α} :
    t ∈ traces 𝒜 x ↔ ∃ s ∈ 𝒜, x ∈ s ∧ s.erase x = t := by
  simp [traces, mem_image, mem_filter, and_assoc]

lemma not_mem_of_mem_traces {𝒜 : Finset (Finset α)} {x : α} {t : Finset α}
    (ht : t ∈ traces 𝒜 x) : x ∉ t := by
  obtain ⟨s, _, _, rfl⟩ := mem_traces.mp ht
  exact not_mem_erase x s

lemma traces_insert_mem {𝒜 : Finset (Finset α)} {x : α} {t : Finset α}
    (ht : t ∈ traces 𝒜 x) : insert x t ∈ 𝒜 := by
  obtain ⟨s, hs, hx, rfl⟩ := mem_traces.mp ht
  rwa [insert_erase hx]

lemma traces_card (𝒜 : Finset (Finset α)) (x : α) :
    (traces 𝒜 x).card = degree 𝒜 x := by
  rw [traces, degree]
  apply Finset.card_image_of_injOn
  intro s hs t ht he
  have hs' : s ∈ 𝒜.filter (fun u => x ∈ u) := mem_coe.mp hs
  have ht' : t ∈ 𝒜.filter (fun u => x ∈ u) := mem_coe.mp ht
  simp only [mem_filter] at hs' ht'
  calc
    s = insert x (s.erase x) := (insert_erase hs'.2).symm
    _ = insert x (t.erase x) := congrArg (insert x) he
    _ = t := insert_erase ht'.2

lemma traces_uniform {r : ℕ} {𝒜 : Finset (Finset α)} {x : α}
    (hr : ∀ s ∈ 𝒜, s.card = r + 1) :
    ∀ t ∈ traces 𝒜 x, t.card = r := by
  intro t ht
  obtain ⟨s, hs, hx, rfl⟩ := mem_traces.mp ht
  rw [card_erase_of_mem hx, hr s hs, add_tsub_cancel_right]

lemma insert_inter_insert (x : α) (s t : Finset α) :
    insert x s ∩ insert x t = insert x (s ∩ t) := by
  ext y
  simp only [mem_inter, mem_insert]
  constructor
  · rintro ⟨hyL, hyR⟩
    rcases hyL with rfl | hys
    · exact Or.inl rfl
    · rcases hyR with rfl | hyt
      · exact Or.inl rfl
      · exact Or.inr ⟨hys, hyt⟩
  · rintro (rfl | hy)
    · exact ⟨Or.inl rfl, Or.inl rfl⟩
    · exact ⟨Or.inr hy.1, Or.inr hy.2⟩

lemma insert_injOn_not_mem (x : α) {𝒮 : Finset (Finset α)}
    (hx : ∀ t ∈ 𝒮, x ∉ t) :
    Set.InjOn (insert x) (𝒮 : Set (Finset α)) := by
  intro t₁ ht₁ t₂ ht₂ h
  have := congrArg (fun u : Finset α => u.erase x) h
  simpa [erase_insert (hx t₁ ht₁), erase_insert (hx t₂ ht₂)] using this

lemma image_insert_card {x : α} {𝒮 : Finset (Finset α)}
    (hx : ∀ t ∈ 𝒮, x ∉ t) :
    (𝒮.image (insert x)).card = 𝒮.card :=
  Finset.card_image_of_injOn (insert_injOn_not_mem x hx)

lemma image_insert_subset_of_traces {𝒜 : Finset (Finset α)} {x : α}
    {𝒮 : Finset (Finset α)} (hS : 𝒮 ⊆ traces 𝒜 x) :
    𝒮.image (insert x) ⊆ 𝒜 := by
  intro s hs
  obtain ⟨t, ht, rfl⟩ := mem_image.mp hs
  exact traces_insert_mem (hS ht)

/-- Lifting a sunflower of traces through `x` adds `x` to the core. -/
lemma isSunflower_image_insert {x : α} {𝒮 : Finset (Finset α)}
    (hS : IsSunflower 𝒮) :
    IsSunflower (𝒮.image (insert x)) := by
  obtain ⟨core, hcore⟩ := hS
  refine ⟨insert x core, ?_⟩
  intro s t hs ht hne
  obtain ⟨s₀, hs₀, rfl⟩ := mem_image.mp hs
  obtain ⟨t₀, ht₀, rfl⟩ := mem_image.mp ht
  have hne₀ : s₀ ≠ t₀ := fun h => hne (by rw [h])
  rw [insert_inter_insert, hcore hs₀ ht₀ hne₀]

lemma pairwiseDisjoint_mono {𝒮 𝒟 : Finset (Finset α)} (hsub : 𝒮 ⊆ 𝒟)
    (h : PairwiseDisjointSets 𝒟) : PairwiseDisjointSets 𝒮 := by
  intro s t hs ht hne
  exact h (hsub hs) (hsub ht) hne

/-- A maximum-cardinality pairwise-disjoint subfamily exists (empty is one). -/
lemma exists_max_pairwise_disjoint (𝒜 : Finset (Finset α)) :
    ∃ 𝒟, 𝒟 ⊆ 𝒜 ∧ PairwiseDisjointSets 𝒟 ∧
      ∀ ℰ, ℰ ⊆ 𝒜 → PairwiseDisjointSets ℰ → ℰ.card ≤ 𝒟.card := by
  let candidates := 𝒜.powerset.filter PairwiseDisjointSets
  have hne : candidates.Nonempty :=
    ⟨∅, mem_filter.mpr ⟨empty_mem_powerset _, pairwiseDisjoint_empty⟩⟩
  obtain ⟨𝒟, h𝒟, hmax⟩ := candidates.exists_max_image Finset.card hne
  have hmem := mem_filter.mp h𝒟
  refine ⟨𝒟, mem_powerset.mp hmem.1, hmem.2, ?_⟩
  intro ℰ hsub hp
  exact hmax ℰ (mem_filter.mpr ⟨mem_powerset.mpr hsub, hp⟩)

lemma biUnion_card_le_card_mul {r : ℕ} {𝒟 : Finset (Finset α)}
    (hr : ∀ s ∈ 𝒟, s.card = r) :
    (𝒟.biUnion id).card ≤ 𝒟.card * r := by
  calc
    (𝒟.biUnion id).card ≤ ∑ s ∈ 𝒟, (id s).card := card_biUnion_le
    _ = ∑ _t ∈ 𝒟, r := sum_congr rfl fun t ht => hr t ht
    _ = 𝒟.card * r := by simp [sum_const, nsmul_eq_mul, mul_comm]

/-- Every member of `𝒜` meets the union of a maximum pairwise-disjoint subfamily,
provided members are nonempty. -/
lemma max_disjoint_meets_union {𝒜 𝒟 : Finset (Finset α)}
    (hsub : 𝒟 ⊆ 𝒜) (hpd : PairwiseDisjointSets 𝒟)
    (hmax : ∀ ℰ, ℰ ⊆ 𝒜 → PairwiseDisjointSets ℰ → ℰ.card ≤ 𝒟.card)
    {t : Finset α} (ht : t ∈ 𝒜) (hne : t.Nonempty) :
    (t ∩ 𝒟.biUnion id).Nonempty := by
  by_contra hempty
  have htU : t ∩ 𝒟.biUnion id = ∅ := not_nonempty_iff_eq_empty.mp hempty
  have hdisj : ∀ s ∈ 𝒟, s ∩ t = ∅ := by
    intro s hs
    ext x
    simp only [mem_inter, not_mem_empty, iff_false, not_and]
    intro hxs hxt
    have hxU : x ∈ 𝒟.biUnion id := mem_biUnion.mpr ⟨s, hs, hxs⟩
    have hx : x ∈ t ∩ 𝒟.biUnion id := mem_inter.mpr ⟨hxt, hxU⟩
    rw [htU] at hx
    exact (not_mem_empty x) hx
  by_cases htD : t ∈ 𝒟
  · have ht_sub : t ⊆ 𝒟.biUnion id := subset_biUnion_of_mem id htD
    have : t ∩ 𝒟.biUnion id = t := inter_eq_left.mpr ht_sub
    rw [this] at htU
    simp [htU] at hne
  · have hinsertPD : PairwiseDisjointSets (insert t 𝒟) := by
      intro s u hs hu hne'
      rw [mem_insert] at hs hu
      rcases hs with rfl | hs <;> rcases hu with rfl | hu
      · exact (hne' rfl).elim
      · have := hdisj u hu
        rwa [inter_comm] at this
      · exact hdisj s hs
      · exact hpd hs hu hne'
    have hinsertSub : insert t 𝒟 ⊆ 𝒜 := insert_subset ht hsub
    have hcard : (insert t 𝒟).card = 𝒟.card + 1 := card_insert_of_not_mem htD
    have : (insert t 𝒟).card ≤ 𝒟.card := hmax _ hinsertSub hinsertPD
    omega

/-- If every member meets `U` and each point of `U` lies in at most `Δ` members,
then `|𝒜| ≤ |U| Δ`. -/
lemma card_le_card_mul_degree {𝒜 : Finset (Finset α)} {U : Finset α} {Δ : ℕ}
    (hmeet : ∀ s ∈ 𝒜, (s ∩ U).Nonempty)
    (hdeg : ∀ x ∈ U, degree 𝒜 x ≤ Δ) :
    𝒜.card ≤ U.card * Δ := by
  have hsum :
      ∑ x ∈ U, degree 𝒜 x = ∑ s ∈ 𝒜, (s ∩ U).card := by
    simp only [degree]
    calc
      ∑ x ∈ U, (𝒜.filter (fun s => x ∈ s)).card
          = ∑ x ∈ U, ∑ s ∈ 𝒜, if x ∈ s then 1 else 0 := by
            refine sum_congr rfl fun x _ => ?_
            rw [card_eq_sum_ones, sum_filter]
      _ = ∑ s ∈ 𝒜, ∑ x ∈ U, if x ∈ s then 1 else 0 := sum_comm
      _ = ∑ s ∈ 𝒜, (U.filter (fun x => x ∈ s)).card := by
            refine sum_congr rfl fun s _ => ?_
            rw [← sum_filter, card_eq_sum_ones]
      _ = ∑ s ∈ 𝒜, (s ∩ U).card := by
            refine sum_congr rfl fun s _ => ?_
            rw [filter_mem_eq_inter, inter_comm]
  have hge : 𝒜.card ≤ ∑ s ∈ 𝒜, (s ∩ U).card := by
    rw [card_eq_sum_ones]
    refine sum_le_sum fun s hs => ?_
    have : 0 < (s ∩ U).card := card_pos.mpr (hmeet s hs)
    omega
  have hle : ∑ x ∈ U, degree 𝒜 x ≤ U.card * Δ := by
    calc
      ∑ x ∈ U, degree 𝒜 x ≤ ∑ _x ∈ U, Δ :=
        sum_le_sum fun y hy => hdeg y hy
      _ = U.card * Δ := by simp [sum_const, nsmul_eq_mul]
  calc
    𝒜.card ≤ ∑ s ∈ 𝒜, (s ∩ U).card := hge
    _ = ∑ x ∈ U, degree 𝒜 x := hsum.symm
    _ ≤ U.card * Δ := hle

/-- Unpopular case: if no element is too popular and a maximum disjoint subfamily
has fewer than `k` petals, the cardinality cannot beat `(r+1)! (k-1)^{r+1}`. -/
lemma unpopular_card_le {r k : ℕ} {𝒜 𝒟 : Finset (Finset α)}
    (hr : ∀ s ∈ 𝒜, s.card = r + 1)
    (_hk : 1 ≤ k)
    (hdeg : ∀ x : α, degree 𝒜 x ≤ Nat.factorial r * (k - 1) ^ r)
    (hsub : 𝒟 ⊆ 𝒜) (hpd : PairwiseDisjointSets 𝒟)
    (hmax : ∀ ℰ, ℰ ⊆ 𝒜 → PairwiseDisjointSets ℰ → ℰ.card ≤ 𝒟.card)
    (hDk : 𝒟.card < k) :
    𝒜.card ≤ Nat.factorial (r + 1) * (k - 1) ^ (r + 1) := by
  have hDle : 𝒟.card ≤ k - 1 := Nat.le_sub_one_of_lt hDk
  let U := 𝒟.biUnion id
  have hUcard : U.card ≤ 𝒟.card * (r + 1) :=
    biUnion_card_le_card_mul (fun s hs => hr s (hsub hs))
  have hUle : U.card ≤ (k - 1) * (r + 1) :=
    hUcard.trans (Nat.mul_le_mul_right (r + 1) hDle)
  have hmeet : ∀ s ∈ 𝒜, (s ∩ U).Nonempty := by
    intro s hs
    have hsne : s.Nonempty := by
      have hpos : 0 < s.card := by
        rw [hr s hs]
        exact Nat.succ_pos _
      exact card_pos.mp hpos
    exact max_disjoint_meets_union hsub hpd hmax hs hsne
  have hΔ : ∀ x ∈ U, degree 𝒜 x ≤ Nat.factorial r * (k - 1) ^ r :=
    fun x _ => hdeg x
  have hmain : 𝒜.card ≤ U.card * (Nat.factorial r * (k - 1) ^ r) :=
    card_le_card_mul_degree hmeet hΔ
  have hbound :
      U.card * (Nat.factorial r * (k - 1) ^ r) ≤
        Nat.factorial (r + 1) * (k - 1) ^ (r + 1) := by
    have h1 := Nat.mul_le_mul_right (Nat.factorial r * (k - 1) ^ r) hUle
    refine h1.trans (le_of_eq ?_)
    rw [Nat.factorial_succ, pow_succ]
    ac_rfl
  exact hmain.trans hbound

/-! ## Level B: namesake Erdős–Rado factorial bound -/

/-- Classical Erdős–Rado 1960 sunflower / Δ-system bound. Formalize-only; **not**
the open sunflower conjecture; **no novelty claim**. -/
theorem erdos_rado_sunflower {r k : ℕ} {𝒜 : Finset (Finset α)}
    (hr : ∀ s ∈ 𝒜, s.card = r)
    (hk : 1 ≤ k)
    (hcard : Nat.factorial r * (k - 1) ^ r < 𝒜.card) :
    ∃ 𝒮 ⊆ 𝒜, 𝒮.card = k ∧ IsSunflower 𝒮 := by
  suffices h :
      ∀ (n k : ℕ) (ℬ : Finset (Finset α)),
        (∀ s ∈ ℬ, s.card = n) →
        1 ≤ k →
        Nat.factorial n * (k - 1) ^ n < ℬ.card →
        ∃ 𝒮 ⊆ ℬ, 𝒮.card = k ∧ IsSunflower 𝒮 from
    h r k 𝒜 hr hk hcard
  intro n
  induction n with
  | zero =>
    intro k ℬ hr' _hk hcard'
    exact (r_zero_bound_unsat hr' hcard').elim
  | succ n ih =>
    intro k ℬ hr' hk' hcard'
    by_cases hpop : ∃ x : α, Nat.factorial n * (k - 1) ^ n < degree ℬ x
    · obtain ⟨x, hx⟩ := hpop
      have hTunif := traces_uniform (r := n) (𝒜 := ℬ) (x := x) hr'
      have hTcard : (traces ℬ x).card = degree ℬ x := traces_card ℬ x
      have hTbound : Nat.factorial n * (k - 1) ^ n < (traces ℬ x).card := by
        rwa [hTcard]
      obtain ⟨𝒮, hsub, h𝒮card, hsun⟩ := ih k (traces ℬ x) hTunif hk' hTbound
      have hxS : ∀ t ∈ 𝒮, x ∉ t := fun t ht => not_mem_of_mem_traces (hsub ht)
      refine ⟨𝒮.image (insert x), image_insert_subset_of_traces hsub, ?_,
        isSunflower_image_insert hsun⟩
      rw [image_insert_card hxS, h𝒮card]
    · push_neg at hpop
      obtain ⟨𝒟, hsub, hpd, hmax⟩ := exists_max_pairwise_disjoint ℬ
      rcases lt_or_ge 𝒟.card k with hlt | hge
      · have hle := unpopular_card_le hr' hk' hpop hsub hpd hmax hlt
        exact (not_lt_of_le hle hcard').elim
      · obtain ⟨𝒮, h𝒮sub, h𝒮card⟩ := exists_subset_card_eq (hge : k ≤ 𝒟.card)
        refine ⟨𝒮, h𝒮sub.trans hsub, h𝒮card,
          isSunflower_of_pairwise_disjoint (pairwiseDisjoint_mono h𝒮sub hpd)⟩

end ProofLab.Sunflower
