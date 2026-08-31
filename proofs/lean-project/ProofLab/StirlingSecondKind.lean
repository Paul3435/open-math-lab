/-
Stirling numbers of the second kind: set-partition count S(n,k).

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 has `Finpartition` / `Setoid.IsPartition` / `Fintype` and
ZERO combinatorics `stirlingSecond` / `stirling_second` / `Nat.bell`
(the only `Stirling` file is `Analysis/SpecialFunctions/Stirling.lean`
`stirlingSeq`, the **n!** approximation — name collision only). Completing
the namesake is the gap.

Pin: `catalog/problems/stirling-second-kind/STATEMENT.md` (OPE-765; Scout
OPE-754 leftover slot #2; Director OPE-764). Encoding: recursive
`stirlingSecond : ℕ → ℕ → ℕ` plus `Finpartition (univ : Finset (Fin n))`
with `parts.card = k`. Zero `sorry`. Do not import `Archive.*`.

This is **not** Stirling's formula for `n!` (already upstream).
This is **not** Catalan (already upstream; OPE-25 demotion).
This is **not** integer partitions (`Nat.Partition` / pentagonal / Euler
odd=distinct / Schur — consumed or Archive-wrong-theorem).
This is **not** Szemerédi regularity (`Finpartition` is the carrier;
counting `parts.card = k` is the gap).
This is **not** Stirling first kind (signed cycle numbers; out of v1).
This is **not** inclusion-exclusion / Bell EGF (out of v1).
This is **not** Moore / cages / KST / Turán / sunflower / CNS /
Kruskal–Katona / Oddtown / EKR / Cayley / Havel / Menger / greedy /
Brooks / König / Dirac / Eulerian / Dilworth.

Level A: recursive `def` plus `S(n,1) = 1` (`n ≥ 1`), `S(n,n) = 1`,
`S(n,2) = 2^{n-1} - 1` (`n ≥ 1`), and the recurrence as `rfl`.
**Not** labelled `stirling_second`. Zero sorry. `S(n,0)` / `S(0,k)`
landmines.
Level B residual (not sorry-ed): namesake `stirling_second` by isolating
the block containing `Fin.last n` (singleton remainder vs insert-into-block).
Engine landed this heartbeat: `embed` / `restrict` / `mapEmbed` /
`addSingleton` / `insertLastInto` / `mapRestrict`. Cap two levels.
Do **not** sorry-in the namesake.
-/
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sum
import Mathlib.Order.Partition.Finpartition
import Mathlib.Tactic

set_option maxHeartbeats 800000
set_option linter.unusedVariables false

open Finset Finpartition

noncomputable section
open Classical

namespace ProofLab.StirlingSecondKind

/-! ## STATEMENT pin — numeric (not labelled as the counting theorem) -/

/-- Stirling numbers of the second kind, recursive pin. Not labelled
`stirling_second`. `S(0,0) = 1`; `S(n,0) = 0` for `n > 0`; `S(0,k) = 0`
for `k > 0`. -/
def stirlingSecond : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, k + 1 => 0
  | n + 1, 0 => 0
  | n + 1, k + 1 =>
      (k + 1) * stirlingSecond n (k + 1) + stirlingSecond n k

/-! ## Level A — recurrence and closed values (not labelled Stirling) -/

@[simp] theorem stirlingSecond_zero_zero : stirlingSecond 0 0 = 1 := rfl

@[simp] theorem stirlingSecond_zero_succ (k : ℕ) : stirlingSecond 0 (k + 1) = 0 := rfl

@[simp] theorem stirlingSecond_succ_zero (n : ℕ) : stirlingSecond (n + 1) 0 = 0 := rfl

/-- Recurrence as a `ℕ` computation. Not labelled `stirling_second`. -/
theorem stirlingSecond_succ (n k : ℕ) :
    stirlingSecond (n + 1) (k + 1) =
      (k + 1) * stirlingSecond n (k + 1) + stirlingSecond n k :=
  rfl

/-- `S(n,k) = 0` when `k > n`. Landmine glue, not labelled Stirling. -/
theorem stirlingSecond_eq_zero_of_lt : ∀ {n k : ℕ}, n < k → stirlingSecond n k = 0
  | 0, 0, h => by cases h
  | 0, k + 1, _ => rfl
  | n + 1, 0, h => by cases h
  | n + 1, k + 1, h => by
    rw [stirlingSecond_succ, stirlingSecond_eq_zero_of_lt (Nat.lt_of_succ_lt_succ h),
      stirlingSecond_eq_zero_of_lt (lt_trans (Nat.lt_succ_self n) h)]
    simp

/-- `S(n,n) = 1`. Not labelled `stirling_second`. -/
theorem stirlingSecond_self : ∀ n, stirlingSecond n n = 1
  | 0 => rfl
  | n + 1 => by
    rw [stirlingSecond_succ, stirlingSecond_eq_zero_of_lt (Nat.lt_succ_self n),
      stirlingSecond_self n]
    simp

/-- `S(n+1, 1) = 1`. Engine for `S(n,1)` with `n ≥ 1`. -/
theorem stirlingSecond_succ_one : ∀ n, stirlingSecond (n + 1) 1 = 1
  | 0 => rfl
  | n + 1 => by
    rw [stirlingSecond_succ, stirlingSecond_succ_one n, stirlingSecond_succ_zero n]

/-- `S(n,1) = 1` for `n ≥ 1`. Not labelled `stirling_second`. -/
theorem stirlingSecond_one {n : ℕ} (hn : 1 ≤ n) : stirlingSecond n 1 = 1 := by
  cases n with
  | zero => cases hn
  | succ n => exact stirlingSecond_succ_one n

/-- `2 * (2^n - 1) + 1 = 2^{n+1} - 1`. Engine, not labelled Stirling. -/
theorem two_mul_two_pow_sub_one (n : ℕ) :
    2 * (2 ^ n - 1) + 1 = 2 ^ (n + 1) - 1 := by
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
  rw [Nat.mul_sub_left_distrib, Nat.mul_one, pow_succ']
  omega

/-- `S(n+1, 2) = 2^n - 1`. Engine for `S(n,2)`. -/
theorem stirlingSecond_succ_two : ∀ n, stirlingSecond (n + 1) 2 = 2 ^ n - 1
  | 0 => rfl
  | n + 1 => by
    rw [stirlingSecond_succ, stirlingSecond_succ_two n, stirlingSecond_succ_one n]
    exact two_mul_two_pow_sub_one n

/-- `S(n,2) = 2^{n-1} - 1` for `n ≥ 1`. Not labelled `stirling_second`. -/
theorem stirlingSecond_two {n : ℕ} (hn : 1 ≤ n) :
    stirlingSecond n 2 = 2 ^ (n - 1) - 1 := by
  cases n with
  | zero => cases hn
  | succ n =>
    change stirlingSecond (n + 1) 2 = 2 ^ n - 1
    exact stirlingSecond_succ_two n

/-! ## Counting pin -/

/-- Set-partitions of `Fin n` into exactly `k` unlabeled nonempty blocks. -/
abbrev StirlingPartition (n k : ℕ) :=
  { P : Finpartition (univ : Finset (Fin n)) // P.parts.card = k }

instance instFintypeStirlingPartition (n k : ℕ) : Fintype (StirlingPartition n k) :=
  Subtype.fintype _

/-! ## Level B engine — `Fin n` ↔ drop `Fin.last n` -/

theorem castSucc_ne_last {n : ℕ} (i : Fin n) : i.castSucc ≠ Fin.last n :=
  Fin.ne_of_val_ne (by
    have : (i.castSucc : ℕ) = (i : ℕ) := Fin.coe_castSucc i
    have : (Fin.last n : ℕ) = n := Fin.val_last n
    omega)

/-- Embed a block of `Fin n` as a block of `Fin (n+1)` not containing `last`. -/
def embed {n : ℕ} (s : Finset (Fin n)) : Finset (Fin (n + 1)) :=
  s.map Fin.castSuccEmb

theorem mem_embed {n : ℕ} {s : Finset (Fin n)} {i : Fin (n + 1)} :
    i ∈ embed s ↔ ∃ j ∈ s, j.castSucc = i := by
  constructor
  · intro h
    rcases mem_map.mp h with ⟨j, hj, heq⟩
    refine ⟨j, hj, ?_⟩
    simpa [Fin.castSuccEmb] using heq
  · rintro ⟨j, hj, rfl⟩
    exact mem_map.mpr ⟨j, hj, rfl⟩

theorem mem_embed_castSucc {n : ℕ} {s : Finset (Fin n)} {j : Fin n} :
    j.castSucc ∈ embed s ↔ j ∈ s := by
  constructor
  · intro h
    rcases (mem_embed.mp h) with ⟨j', hj', heq⟩
    rwa [← Fin.castSucc_inj.mp heq]
  · intro hj
    exact mem_embed.mpr ⟨j, hj, rfl⟩

theorem last_not_mem_embed {n : ℕ} (s : Finset (Fin n)) : Fin.last n ∉ embed s := by
  intro h
  rcases mem_embed.mp h with ⟨j, _, hj⟩
  exact castSucc_ne_last j hj

theorem embed_eq_empty {n : ℕ} {s : Finset (Fin n)} : embed s = ∅ ↔ s = ∅ := by
  constructor
  · intro h
    ext j
    constructor
    · intro hj
      have : j.castSucc ∈ embed s := mem_embed_castSucc.mpr hj
      rw [h] at this
      exact absurd this (not_mem_empty _)
    · intro hj
      exact absurd hj (not_mem_empty _)
  · rintro rfl
    simp [embed]

theorem embed_injective {n : ℕ} :
    Function.Injective (embed : Finset (Fin n) → Finset (Fin (n + 1))) := by
  intro s t h
  ext j
  rw [← mem_embed_castSucc, h, mem_embed_castSucc]

/-- Restrict a block of `Fin (n+1)` by dropping `last` (via `castSucc`). -/
def restrict {n : ℕ} (s : Finset (Fin (n + 1))) : Finset (Fin n) :=
  univ.filter fun i => i.castSucc ∈ s

theorem mem_restrict {n : ℕ} {s : Finset (Fin (n + 1))} {j : Fin n} :
    j ∈ restrict s ↔ j.castSucc ∈ s := by
  simp [restrict]

theorem restrict_embed {n : ℕ} (s : Finset (Fin n)) : restrict (embed s) = s := by
  ext j
  simp [mem_restrict, mem_embed_castSucc]

theorem embed_restrict_of_not_mem_last {n : ℕ} {s : Finset (Fin (n + 1))}
    (h : Fin.last n ∉ s) : embed (restrict s) = s := by
  ext i
  constructor
  · intro hi
    rcases mem_embed.mp hi with ⟨j, hj, rfl⟩
    exact mem_restrict.mp hj
  · intro hi
    have hine : i ≠ Fin.last n := fun hie => h (hie ▸ hi)
    obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq_of_ne_last hine
    exact mem_embed.mpr ⟨j, mem_restrict.mpr hi, rfl⟩

theorem embed_univ {n : ℕ} :
    embed (univ : Finset (Fin n)) = (univ : Finset (Fin (n + 1))).erase (Fin.last n) := by
  ext i
  constructor
  · intro hi
    rcases mem_embed.mp hi with ⟨j, _, rfl⟩
    exact mem_erase.mpr ⟨castSucc_ne_last j, mem_univ _⟩
  · intro hi
    have hine : i ≠ Fin.last n := (mem_erase.mp hi).1
    obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq_of_ne_last hine
    exact mem_embed.mpr ⟨j, mem_univ _, rfl⟩

theorem disjoint_embed {n : ℕ} {s t : Finset (Fin n)} :
    Disjoint (embed s) (embed t) ↔ Disjoint s t := by
  constructor
  · intro h
    rw [disjoint_iff_inter_eq_empty] at h ⊢
    ext j
    constructor
    · intro hj
      have : j.castSucc ∈ embed s ∩ embed t := by
        exact mem_inter.mpr ⟨mem_embed_castSucc.mpr (mem_of_mem_inter_left hj),
          mem_embed_castSucc.mpr (mem_of_mem_inter_right hj)⟩
      rw [h] at this
      exact (not_mem_empty _ this).elim
    · intro hj
      exact (not_mem_empty _ hj).elim
  · intro h
    rw [disjoint_iff_inter_eq_empty] at h ⊢
    ext i
    constructor
    · intro hi
      rcases mem_embed.mp (mem_of_mem_inter_left hi) with ⟨j, hj, rfl⟩
      have hjt : j ∈ t := mem_embed_castSucc.mp (mem_of_mem_inter_right hi)
      have : j ∈ s ∩ t := mem_inter.mpr ⟨hj, hjt⟩
      rw [h] at this
      exact (not_mem_empty _ this).elim
    · intro hi
      exact (not_mem_empty _ hi).elim

theorem embed_union {n : ℕ} (s t : Finset (Fin n)) :
    embed (s ∪ t) = embed s ∪ embed t := by
  ext i
  constructor
  · intro hi
    rcases mem_embed.mp hi with ⟨j, hj, rfl⟩
    rcases mem_union.mp hj with hjs | hjt
    · exact mem_union.mpr (Or.inl (mem_embed_castSucc.mpr hjs))
    · exact mem_union.mpr (Or.inr (mem_embed_castSucc.mpr hjt))
  · intro hi
    rcases mem_union.mp hi with h | h
    · rcases mem_embed.mp h with ⟨j, hj, rfl⟩
      exact mem_embed.mpr ⟨j, mem_union.mpr (Or.inl hj), rfl⟩
    · rcases mem_embed.mp h with ⟨j, hj, rfl⟩
      exact mem_embed.mpr ⟨j, mem_union.mpr (Or.inr hj), rfl⟩

theorem embed_sup {n : ℕ} (S : Finset (Finset (Fin n))) :
    S.sup embed = embed (S.sup id) := by
  ext i
  constructor
  · intro hi
    rcases mem_sup.mp hi with ⟨b, hb, hib⟩
    rcases mem_embed.mp hib with ⟨j, hj, rfl⟩
    exact mem_embed.mpr ⟨j, mem_sup.mpr ⟨b, hb, hj⟩, rfl⟩
  · intro hi
    rcases mem_embed.mp hi with ⟨j, hj, rfl⟩
    rcases mem_sup.mp hj with ⟨b, hb, hj'⟩
    exact mem_sup.mpr ⟨b, hb, mem_embed_castSucc.mpr hj'⟩

/-! ### Map a partition of `Fin n` along `castSucc` -/

def mapEmbed {n : ℕ} (P : Finpartition (univ : Finset (Fin n))) :
    Finpartition (embed (univ : Finset (Fin n))) where
  parts := P.parts.image embed
  supIndep := by
    rw [supIndep_iff_pairwiseDisjoint]
    intro a ha b hb hne
    rcases mem_image.mp (mem_coe.mp ha) with ⟨a', ha', rfl⟩
    rcases mem_image.mp (mem_coe.mp hb) with ⟨b', hb', rfl⟩
    have hne' : a' ≠ b' := fun h => hne (congrArg embed h)
    exact (disjoint_embed.2 (P.disjoint ha' hb' hne'))
  sup_parts := by
    rw [sup_image]
    change P.parts.sup embed = embed univ
    rw [embed_sup, P.sup_parts]
  not_bot_mem := by
    intro h
    rcases mem_image.mp h with ⟨t, ht, ht'⟩
    have hempty : embed t = ⊥ := ht'
    have : t = ∅ := embed_eq_empty.1 (by simpa [bot_eq_empty] using hempty)
    rw [this] at ht
    exact P.not_bot_mem (by simpa [bot_eq_empty] using ht)

theorem card_mapEmbed {n : ℕ} (P : Finpartition (univ : Finset (Fin n))) :
    (mapEmbed P).parts.card = P.parts.card :=
  card_image_of_injective _ embed_injective

theorem mem_mapEmbed {n : ℕ} {P : Finpartition (univ : Finset (Fin n))}
    {t : Finset (Fin n)} (ht : t ∈ P.parts) : embed t ∈ (mapEmbed P).parts :=
  mem_image_of_mem _ ht

/-- Add `{last}` as a new singleton block. The `S(n,k)` summand, shifted. -/
def addSingleton {n : ℕ} (P : Finpartition (univ : Finset (Fin n))) :
    Finpartition (univ : Finset (Fin (n + 1))) :=
  ((mapEmbed P).copy embed_univ).extend
    (by simp [bot_eq_empty] : ({Fin.last n} : Finset (Fin (n + 1))) ≠ ⊥)
    (disjoint_singleton_right.2 (not_mem_erase _ _))
    (by
      simp [sup_eq_union]
      rw [union_comm]
      exact insert_erase (mem_univ (Fin.last n)))

theorem card_addSingleton {n : ℕ} (P : Finpartition (univ : Finset (Fin n))) :
    (addSingleton P).parts.card = P.parts.card + 1 := by
  unfold addSingleton
  rw [card_extend, copy_parts, card_mapEmbed]

theorem mem_parts_addSingleton_last {n : ℕ} (P : Finpartition (univ : Finset (Fin n))) :
    {Fin.last n} ∈ (addSingleton P).parts := by
  unfold addSingleton
  simp [extend_parts]

theorem part_last_addSingleton {n : ℕ} (P : Finpartition (univ : Finset (Fin n))) :
    (addSingleton P).part (Fin.last n) = {Fin.last n} :=
  part_eq_of_mem _ (mem_parts_addSingleton_last P) (by simp)

/-- Insert `last` into an existing block `t`. One of the `k+1` choices. -/
def insertLastInto {n : ℕ} (P : Finpartition (univ : Finset (Fin n)))
    (t : Finset (Fin n)) (ht : t ∈ P.parts) :
    Finpartition (univ : Finset (Fin (n + 1))) where
  parts := insert (insert (Fin.last n) (embed t)) ((P.parts.erase t).image embed)
  supIndep := by
    rw [supIndep_iff_pairwiseDisjoint, coe_insert]
    have hs :
        ((P.parts.erase t).image embed : Set (Finset (Fin (n + 1)))).PairwiseDisjoint
          (id : Finset (Fin (n + 1)) → Finset (Fin (n + 1))) := by
      intro a ha b hb hne
      rcases mem_image.mp (mem_coe.mp ha) with ⟨a', ha', rfl⟩
      rcases mem_image.mp (mem_coe.mp hb) with ⟨b', hb', rfl⟩
      have hne' : a' ≠ b' := fun h => hne (congrArg embed h)
      exact disjoint_embed.2
        (P.disjoint (mem_of_mem_erase ha') (mem_of_mem_erase hb') hne')
    refine hs.insert ?_
    intro b hb _
    rcases mem_image.mp (mem_coe.mp hb) with ⟨t', ht', rfl⟩
    change Disjoint (insert (Fin.last n) (embed t)) (embed t')
    rw [disjoint_insert_left]
    exact ⟨last_not_mem_embed t',
      disjoint_embed.2 (P.disjoint ht (mem_of_mem_erase ht') (ne_of_mem_erase ht').symm)⟩
  sup_parts := by
    rw [sup_insert, id_eq, sup_image]
    change insert (Fin.last n) (embed t) ⊔ (P.parts.erase t).sup embed = univ
    rw [embed_sup]
    have hsplit : (P.parts.erase t).sup id ⊔ t = univ := by
      conv_rhs => rw [← P.sup_parts, ← insert_erase ht, sup_insert]
      simp [sup_comm]
    rw [sup_eq_union, insert_union, ← embed_union]
    have : t ∪ (P.parts.erase t).sup id = univ := by
      simpa [union_comm, sup_eq_union] using hsplit
    rw [this, embed_univ]
    exact insert_erase (mem_univ (Fin.last n))
  not_bot_mem := by
    intro h
    rw [mem_insert, bot_eq_empty] at h
    rcases h with h | h
    · exact insert_ne_empty _ _ h.symm
    · rcases mem_image.mp h with ⟨u, hu, hu'⟩
      have : u = ∅ := embed_eq_empty.1 hu'
      have huP : u ∈ P.parts := mem_of_mem_erase hu
      rw [this] at huP
      exact P.not_bot_mem (by simpa [bot_eq_empty] using huP)

theorem card_insertLastInto {n : ℕ} (P : Finpartition (univ : Finset (Fin n)))
    {t : Finset (Fin n)} (ht : t ∈ P.parts) :
    (insertLastInto P t ht).parts.card = P.parts.card := by
  unfold insertLastInto
  have hpos : 0 < P.parts.card := card_pos.mpr ⟨t, ht⟩
  rw [card_insert_of_not_mem, card_image_of_injective _ embed_injective, card_erase_of_mem ht]
  · omega
  · intro h
    rcases mem_image.mp h with ⟨u, hu, hu'⟩
    have : Fin.last n ∈ insert (Fin.last n) (embed t) := mem_insert_self _ _
    rw [← hu'] at this
    exact last_not_mem_embed _ this

theorem mem_parts_insertLastInto {n : ℕ} (P : Finpartition (univ : Finset (Fin n)))
    {t : Finset (Fin n)} (ht : t ∈ P.parts) :
    insert (Fin.last n) (embed t) ∈ (insertLastInto P t ht).parts :=
  mem_insert_self _ _

theorem part_last_insertLastInto {n : ℕ} (P : Finpartition (univ : Finset (Fin n)))
    {t : Finset (Fin n)} (ht : t ∈ P.parts) :
    (insertLastInto P t ht).part (Fin.last n) = insert (Fin.last n) (embed t) :=
  part_eq_of_mem _ (mem_parts_insertLastInto P ht) (mem_insert_self _ _)

theorem part_last_insertLastInto_ne_singleton {n : ℕ}
    (P : Finpartition (univ : Finset (Fin n))) {t : Finset (Fin n)} (ht : t ∈ P.parts) :
    (insertLastInto P t ht).part (Fin.last n) ≠ {Fin.last n} := by
  rw [part_last_insertLastInto]
  intro h
  obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts ht
  have : x.castSucc ∈ ({Fin.last n} : Finset (Fin (n + 1))) := by
    rw [← h]
    exact mem_insert_of_mem (mem_embed_castSucc.mpr hx)
  exact castSucc_ne_last x (mem_singleton.mp this)

/-! ### Drop `last` from a partition of `Fin (n+1)` -/

theorem restrict_union {n : ℕ} (s t : Finset (Fin (n + 1))) :
    restrict (s ∪ t) = restrict s ∪ restrict t := by
  ext j
  simp [mem_restrict, mem_union]

theorem restrict_erase_last {n : ℕ} :
    restrict ((univ : Finset (Fin (n + 1))).erase (Fin.last n)) = univ := by
  ext j
  simp [mem_restrict, castSucc_ne_last]

theorem restrict_sup {n : ℕ} (S : Finset (Finset (Fin (n + 1)))) :
    S.sup restrict = restrict (S.sup id) := by
  ext j
  constructor
  · intro hj
    rcases mem_sup.mp hj with ⟨b, hb, hj'⟩
    exact mem_restrict.mpr (mem_sup.mpr ⟨b, hb, mem_restrict.mp hj'⟩)
  · intro hj
    have : j.castSucc ∈ S.sup id := mem_restrict.mp hj
    rcases mem_sup.mp this with ⟨b, hb, hib⟩
    exact mem_sup.mpr ⟨b, hb, mem_restrict.mpr hib⟩

theorem last_not_mem_of_le_erase {n : ℕ} {s : Finset (Fin (n + 1))}
    (h : s ⊆ univ.erase (Fin.last n)) : Fin.last n ∉ s :=
  fun hx => not_mem_erase _ _ (h hx)

def mapRestrict {n : ℕ} (P : Finpartition ((univ : Finset (Fin (n + 1))).erase (Fin.last n))) :
    Finpartition (univ : Finset (Fin n)) where
  parts := P.parts.image restrict
  supIndep := by
    rw [supIndep_iff_pairwiseDisjoint]
    intro a ha b hb hne
    rcases mem_image.mp (mem_coe.mp ha) with ⟨a', ha', rfl⟩
    rcases mem_image.mp (mem_coe.mp hb) with ⟨b', hb', rfl⟩
    have hne' : a' ≠ b' := fun h => hne (congrArg restrict h)
    have hd : Disjoint a' b' := P.disjoint ha' hb' hne'
    change Disjoint (restrict a') (restrict b')
    rw [disjoint_iff_inter_eq_empty] at hd ⊢
    ext j
    constructor
    · intro hj
      have : j.castSucc ∈ a' ∩ b' :=
        mem_inter.mpr ⟨mem_restrict.mp (mem_of_mem_inter_left hj),
          mem_restrict.mp (mem_of_mem_inter_right hj)⟩
      rw [hd] at this
      exact (not_mem_empty _ this).elim
    · intro hj
      exact (not_mem_empty _ hj).elim
  sup_parts := by
    rw [sup_image]
    change P.parts.sup restrict = univ
    rw [restrict_sup, P.sup_parts, restrict_erase_last]
  not_bot_mem := by
    intro h
    rcases mem_image.mp h with ⟨t, ht, ht'⟩
    have hempty : restrict t = ∅ := by simpa [bot_eq_empty] using ht'
    obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts ht
    have hx_ne : x ≠ Fin.last n := ne_of_mem_erase (P.le ht hx)
    obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq_of_ne_last hx_ne
    have : j ∈ restrict t := mem_restrict.mpr hx
    rw [hempty] at this
    exact not_mem_empty _ this

end ProofLab.StirlingSecondKind
