/-
Kruskal–Katona (Kruskal 1963 / Katona 1968): among `r`-uniform families of a
given cardinality, the colexicographic initial segment has the smallest shadow.

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 has `Finset.shadow` / `Set.Sized` / `Finset.IsInitSeg` /
`Finset.initSeg` / `UV.card_shadow_compression_le` and ZERO Kruskal-Katona
theorem ident (Colex/UV mention the name only as motivation).

Pin: `catalog/problems/kruskal-katona/STATEMENT.md` (OPE-707; Scout OPE-702;
Director OPE-706). Encoding: ground set `Fin n`; members `Finset (Fin n)` of
card `r` (`Set.Sized r`). Colex pin: Mathlib `IsInitSeg` / `toColex` — **not**
lex. Shadow is Mathlib `Finset.shadow` (down-shadow to card `r-1`).
Zero `sorry`. Do not import `Archive.*`.

This is **not** Sperner (`IsAntichain.sperner` already in `LYM.lean`).
This is **not** LYM (`card_div_choose_le_card_shadow_div_choose` already
upstream). This is **not** Dilworth / EKR / Hilton–Milner / Oddtown /
Eventown. UV-compression glue is already upstream — used, not re-proved,
not labelled Kruskal–Katona. Finite only. Lovász ℝ-binomial form is out of v1.

Level A: empty family; singleton `r`-set (`|∂| = r`); `r = 0` or `r = 1`;
UV-compression already does not increase the shadow (glue). Zero sorry.
Level B: namesake `kruskal_katona` by UV-compressing until the family is
colex-compressed; a fully compressed `r`-uniform family is a colex initial
segment; compression does not increase `|∂|`.
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Colex
import Mathlib.Combinatorics.SetFamily.Compression.UV
import Mathlib.Tactic

set_option maxHeartbeats 800000

open Finset Function
open scoped FinsetFamily

noncomputable section
open Classical

namespace ProofLab.KruskalKatona

open Finset.Colex UV

variable {n r : ℕ}

/-! ## Level A: empty / singleton / `r ≤ 1` / UV glue (not labelled KK) -/

/-- The shadow of the empty family is empty. Glue, not Kruskal–Katona. -/
theorem shadow_empty_card :
    (shadow (∅ : Finset (Finset (Fin n)))).card = 0 := by
  simp [shadow_empty]

/-- Erasing distinct elements of `s` gives distinct sets. -/
lemma erase_injOn_self {α : Type*} [DecidableEq α] (s : Finset α) :
    Set.InjOn (erase s) (s : Set α) := by
  intro a ha b hb h
  have hsa : insert a (erase s a) = s := insert_erase ha
  have hsb : insert b (erase s b) = s := insert_erase hb
  have : insert a (erase s b) = insert b (erase s b) := by
    simpa [h] using hsa.trans hsb.symm
  have hb' : b ∈ insert a (erase s b) := by
    rw [this]; exact mem_insert_self _ _
  rcases mem_insert.mp hb' with rfl | hbe
  · rfl
  · exact (not_mem_erase _ _ hbe).elim

/-- The shadow of a singleton family `{s}` is `{s \ {a} | a ∈ s}`. -/
lemma shadow_singleton {α : Type*} [DecidableEq α] (s : Finset α) :
    shadow {s} = s.image (erase s) := by
  simp [shadow]

/-- Level A: a singleton `r`-set has shadow of cardinality `r`. Glue. -/
theorem shadow_singleton_card (s : Finset (Fin n)) :
    (shadow {s}).card = s.card := by
  rw [shadow_singleton, card_image_of_injOn (erase_injOn_self s)]

/-- A `0`-uniform family is contained in `{∅}`. -/
lemma sized_zero {𝒜 : Finset (Finset (Fin n))}
    (h𝒜 : (𝒜 : Set (Finset (Fin n))).Sized 0) : 𝒜 ⊆ {∅} := by
  intro s hs
  simpa [mem_singleton, card_eq_zero] using h𝒜 hs

/-- Level A: the shadow of a `0`-uniform family is empty. Glue. -/
theorem shadow_of_sized_zero {𝒜 : Finset (Finset (Fin n))}
    (h𝒜 : (𝒜 : Set (Finset (Fin n))).Sized 0) : shadow 𝒜 = ∅ := by
  have hsub : 𝒜 ⊆ {∅} := sized_zero h𝒜
  have hsh : shadow 𝒜 ⊆ shadow {∅} := shadow_monotone hsub
  have : shadow 𝒜 ⊆ ∅ := by simpa [shadow_singleton_empty] using hsh
  exact subset_empty.mp this

/-- Level A: a nonempty `1`-uniform family has shadow `{∅}`. Glue. -/
theorem shadow_of_sized_one {𝒜 : Finset (Finset (Fin n))}
    (h𝒜 : (𝒜 : Set (Finset (Fin n))).Sized 1) (hne : 𝒜.Nonempty) :
    shadow 𝒜 = {∅} := by
  ext t
  simp only [mem_singleton, mem_shadow_iff_insert_mem]
  constructor
  · rintro ⟨a, ha, hA⟩
    have hcard : (insert a t).card = 1 := h𝒜 hA
    have : t.card = 0 := by
      rw [card_insert_of_not_mem ha] at hcard
      omega
    exact card_eq_zero.mp this
  · rintro rfl
    obtain ⟨s, hs⟩ := hne
    have hs1 : s.card = 1 := h𝒜 hs
    obtain ⟨a, rfl⟩ := card_eq_one.mp hs1
    refine ⟨a, not_mem_empty a, ?_⟩
    simpa using hs

/-- Glue (not Kruskal–Katona): Mathlib `UV.card_shadow_compression_le`. -/
theorem card_shadow_uv_compression_le {α : Type*} [DecidableEq α]
    {𝒜 : Finset (Finset α)} (u v : Finset α)
    (huv : ∀ x ∈ u, ∃ y ∈ v, IsCompressed (u.erase x) (v.erase y) 𝒜) :
    (shadow (compression u v 𝒜)).card ≤ (shadow 𝒜).card :=
  UV.card_shadow_compression_le u v huv

/-- Level A: empty families (same card 0) have equal (zero) shadows. -/
theorem shadow_card_of_empty {𝒜 𝒞 : Finset (Finset (Fin n))}
    (h𝒜 : 𝒜 = ∅) (hcard : 𝒞.card = 𝒜.card) :
    (shadow 𝒞).card ≤ (shadow 𝒜).card := by
  subst h𝒜
  have : 𝒞 = ∅ := card_eq_zero.mp (by simpa using hcard)
  simp [this, shadow_empty]

/-- Level A: the comparison inequality when `r ≤ 1`. Not the namesake. -/
theorem shadow_card_le_of_r_le_one {𝒜 𝒞 : Finset (Finset (Fin n))}
    (hr : r ≤ 1) (h𝒜 : (𝒜 : Set (Finset (Fin n))).Sized r)
    (h𝒞 : IsInitSeg 𝒞 r) (hcard : 𝒞.card = 𝒜.card) :
    (shadow 𝒞).card ≤ (shadow 𝒜).card := by
  have h𝒞r : (𝒞 : Set (Finset (Fin n))).Sized r := h𝒞.1
  interval_cases r
  · have hA : shadow 𝒜 = ∅ := shadow_of_sized_zero h𝒜
    have hC : shadow 𝒞 = ∅ := shadow_of_sized_zero h𝒞r
    simp [hA, hC]
  · by_cases hne : 𝒜.Nonempty
    · have hneC : 𝒞.Nonempty := by
        rw [← card_pos, hcard, card_pos]
        exact hne
      have hA : shadow 𝒜 = {∅} := shadow_of_sized_one h𝒜 hne
      have hC : shadow 𝒞 = {∅} := shadow_of_sized_one h𝒞r hneC
      simp [hA, hC]
    · have hA0 : 𝒜 = ∅ := not_nonempty_iff_eq_empty.mp hne
      exact shadow_card_of_empty hA0 hcard

/-! ## Level B helpers: UV-compression until a colex initial segment -/

section UVColex
variable {α : Type*} [LinearOrder α] [DecidableEq α] {s U V : Finset α}

/-- Applying the compression makes the set smaller in colex, since a portion is
shifted down as `max U < max V`. -/
lemma toColex_compress_lt_toColex {hU : U.Nonempty} {hV : V.Nonempty}
    (h : max' U hU < max' V hV) (hA : compress U V s ≠ s) :
    toColex (compress U V s) < toColex s := by
  unfold compress at hA ⊢
  split_ifs at hA ⊢ with hcond
  · rw [toColex_lt_toColex_iff_exists_forall_lt]
    refine ⟨max' V hV, hcond.2 (max'_mem _ hV), ?_, ?_⟩
    · intro hmem
      have : max' V hV ∉ V := (mem_sdiff.mp hmem).2
      exact this (max'_mem _ hV)
    · intro b hb hbns
      have hbU : b ∈ U := (mem_union.mp (mem_sdiff.mp hb).1).resolve_left hbns
      exact (le_max' U b hbU).trans_lt h
  · exact (hA rfl).elim

/-- Compressions which decrease the colex measure of a family. -/
def UsefulCompression (U V : Finset α) : Prop :=
  Disjoint U V ∧ U.card = V.card ∧
    ∃ (HU : U.Nonempty) (HV : V.Nonempty), max' U HU < max' V HV

instance UsefulCompression.instDecidableRel :
    DecidableRel (α := Finset α) UsefulCompression :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

/-- A useful compression whose strictly smaller useful compressions already
leave `𝒜` fixed does not increase the shadow. Glue via Mathlib UV. -/
lemma compression_improved (𝒜 : Finset (Finset α)) (h₁ : UsefulCompression U V)
    (h₂ : ∀ ⦃U₁ V₁⦄, UsefulCompression U₁ V₁ → U₁.card < U.card →
      IsCompressed U₁ V₁ 𝒜) :
    (shadow (compression U V 𝒜)).card ≤ (shadow 𝒜).card := by
  obtain ⟨UVd, same_size, hU, hV, max_lt⟩ := h₁
  refine UV.card_shadow_compression_le _ _ fun x Hx => ⟨min' V hV, min'_mem _ _, ?_⟩
  obtain hU' | hU' := eq_or_lt_of_le (Nat.succ_le_iff.2 hU.card_pos)
  · rw [← hU'] at same_size
    have hUe : erase U x = ∅ := by
      rw [← card_eq_zero, card_erase_of_mem Hx, ← hU']
    have hVe : erase V (min' V hV) = ∅ := by
      rw [← card_eq_zero, card_erase_of_mem (min'_mem _ _), ← same_size]
    rw [hUe, hVe]
    exact isCompressed_self _ _
  · refine h₂ ⟨UVd.mono (erase_subset _ _) (erase_subset _ _), ?_, ?_, ?_, ?_⟩
      (card_erase_lt_of_mem Hx)
    · rw [card_erase_of_mem (min'_mem _ _), card_erase_of_mem Hx, same_size]
    · rwa [← card_pos, card_erase_of_mem Hx, tsub_pos_iff_lt]
    · rwa [← card_pos, card_erase_of_mem (min'_mem _ _), ← same_size, tsub_pos_iff_lt]
    · refine (max'_subset _ (erase_subset _ _)).trans_lt ?_
      refine max_lt.trans_le (le_max' _ _ ?_)
      refine mem_erase.2 ⟨?_, max'_mem _ _⟩
      have hVcard : 1 < V.card := by rwa [← same_size]
      exact (min'_lt_max'_of_card (s := V) hVcard).ne'

attribute [-instance] Fintype.decidableForallFintype

/-- If a family is compressed by every useful UV-pair, it is a colex initial
segment. Other key Kruskal–Katona part. -/
lemma isInitSeg_of_compressed {ℬ : Finset (Finset α)} {r : ℕ}
    (h₁ : (ℬ : Set (Finset α)).Sized r)
    (h₂ : ∀ U V, UsefulCompression U V → IsCompressed U V ℬ) :
    IsInitSeg ℬ r := by
  refine ⟨h₁, ?_⟩
  rintro A B hA ⟨hBA, sizeA⟩
  by_contra hB
  have hAB : A ≠ B := ne_of_mem_of_not_mem hA hB
  have hAB' : A.card = B.card := (h₁ hA).trans sizeA.symm
  have hU : (A \ B).Nonempty :=
    sdiff_nonempty.2 fun h => hAB <| eq_of_subset_of_card_le h hAB'.ge
  have hV : (B \ A).Nonempty :=
    sdiff_nonempty.2 fun h => hAB.symm <| eq_of_subset_of_card_le h hAB'.le
  have disj : Disjoint (B \ A) (A \ B) :=
    disjoint_left.2 fun x hxB hxA => (mem_sdiff.1 hxA).2 (mem_sdiff.1 hxB).1
  have smaller : max' _ hV < max' _ hU := by
    obtain hlt | heq | hgt := lt_trichotomy (max' _ hU) (max' _ hV)
    · have hAB'' : compress (A \ B) (B \ A) B ≠ B := by
        rw [compress_sdiff_sdiff A B]
        exact hAB
      have hBA' : toColex B < toColex A := hBA
      have : toColex (compress (A \ B) (B \ A) B) < toColex B :=
        toColex_compress_lt_toColex hlt hAB''
      rw [compress_sdiff_sdiff A B] at this
      exact (lt_asymm hBA' this).elim
    · exact (disjoint_right.1 disj (max'_mem _ hU) (heq.symm ▸ max'_mem _ hV)).elim
    · exact hgt
  refine hB ?_
  rw [← (h₂ _ _ ⟨disj, card_sdiff_comm hAB'.symm, hV, hU, smaller⟩).eq]
  exact mem_compression.2 (Or.inr ⟨hB, A, hA, compress_sdiff_sdiff _ _⟩)

end UVColex

/-- Rough compression-progress measure. Order-dependent; the namesake is not. -/
def familyMeasure (𝒜 : Finset (Finset (Fin n))) : ℕ :=
  ∑ A ∈ 𝒜, ∑ a ∈ A, 2 ^ (a : ℕ)

lemma fin_coe_strictMono {n : ℕ} : StrictMono (fun a : Fin n => (a : ℕ)) :=
  fun _ _ h => h

lemma geomSum_lt_of_toColex_lt {A B : Finset (Fin n)}
    (h : toColex A < toColex B) :
    (∑ a ∈ A, 2 ^ (a : ℕ)) < ∑ a ∈ B, 2 ^ (a : ℕ) := by
  have hA : ∑ a ∈ A, 2 ^ (a : ℕ) = ∑ k ∈ A.image Fin.val, 2 ^ k :=
    (sum_image fun _ _ _ _ hxy => Fin.val_injective hxy).symm
  have hB : ∑ a ∈ B, 2 ^ (a : ℕ) = ∑ k ∈ B.image Fin.val, 2 ^ k :=
    (sum_image fun _ _ _ _ hxy => Fin.val_injective hxy).symm
  rw [hA, hB, geomSum_lt_geomSum_iff_toColex_lt_toColex (le_rfl : 2 ≤ 2)]
  exact (toColex_image_lt_toColex_image fin_coe_strictMono).2 h

/-- A useful compression that actually moves the family strictly decreases
`familyMeasure`. -/
lemma familyMeasure_compression_lt {U V : Finset (Fin n)} {hU : U.Nonempty}
    {hV : V.Nonempty} (h : max' U hU < max' V hV)
    {𝒜 : Finset (Finset (Fin n))} (ha : compression U V 𝒜 ≠ 𝒜) :
    familyMeasure (compression U V 𝒜) < familyMeasure 𝒜 := by
  rw [compression] at ha ⊢
  have q : ∀ Q ∈ 𝒜.filter (fun A => compress U V A ∉ 𝒜), compress U V Q ≠ Q := by
    intro Q hQ hQQ
    have hQ' := mem_filter.1 hQ
    exact hQ'.2 (hQQ.symm ▸ hQ'.1)
  have uA :
      𝒜.filter (fun A => compress U V A ∈ 𝒜) ∪
        𝒜.filter (fun A => compress U V A ∉ 𝒜) = 𝒜 :=
    filter_union_filter_neg_eq _ _
  have ne₂ : (𝒜.filter (fun A => compress U V A ∉ 𝒜)).Nonempty := by
    contrapose! ha
    have hEmp : 𝒜.filter (fun A => compress U V A ∉ 𝒜) = ∅ :=
      not_nonempty_iff_eq_empty.1 ha
    rw [filter_image, hEmp, image_empty, union_empty]
    rwa [hEmp, union_empty] at uA
  rw [familyMeasure, familyMeasure, sum_union compress_disjoint]
  conv_rhs => rw [← uA]
  rw [sum_union (disjoint_filter_filter_neg _ _ _), add_lt_add_iff_left,
    filter_image, sum_image compress_injOn]
  refine sum_lt_sum_of_nonempty ne₂ fun A hA => ?_
  exact geomSum_lt_of_toColex_lt (toColex_compress_lt_toColex h (q _ hA))

/-- Keep applying a smallest useful compression until none remain. -/
lemma kruskal_katona_helper {r : ℕ} (𝒜 : Finset (Finset (Fin n)))
    (h : (𝒜 : Set (Finset (Fin n))).Sized r) :
    ∃ ℬ : Finset (Finset (Fin n)),
      (shadow ℬ).card ≤ (shadow 𝒜).card ∧ 𝒜.card = ℬ.card ∧
        (ℬ : Set (Finset (Fin n))).Sized r ∧
          ∀ U V, UsefulCompression U V → IsCompressed U V ℬ := by
  classical
  let usable : Finset (Finset (Fin n) × Finset (Fin n)) :=
    univ.filter fun t => UsefulCompression t.1 t.2 ∧ ¬ IsCompressed t.1 t.2 𝒜
  obtain husable | husable := usable.eq_empty_or_nonempty
  · refine ⟨𝒜, le_rfl, rfl, h, fun U V hUV => ?_⟩
    rw [eq_empty_iff_forall_not_mem] at husable
    by_contra hC
    exact husable ⟨U, V⟩ (mem_filter.2 ⟨mem_univ _, hUV, hC⟩)
  · obtain ⟨⟨U, V⟩, hUV, tmin⟩ := exists_min_image usable (fun t => t.1.card) husable
    rw [mem_filter] at hUV
    have h₂ : ∀ U₁ V₁, UsefulCompression U₁ V₁ → U₁.card < U.card →
        IsCompressed U₁ V₁ 𝒜 := by
      intro U₁ V₁ huseful hUcard
      by_contra hC
      exact (not_le_of_gt hUcard) (tmin ⟨U₁, V₁⟩ (mem_filter.2 ⟨mem_univ _, huseful, hC⟩))
    have p1 : (shadow (compression U V 𝒜)).card ≤ (shadow 𝒜).card :=
      compression_improved _ hUV.2.1 h₂
    obtain ⟨-, hUV', hu, hv, hmax⟩ := hUV.2.1
    have := familyMeasure_compression_lt hmax hUV.2.2
    obtain ⟨t, q1, q2, q3, q4⟩ :=
      kruskal_katona_helper (compression U V 𝒜) (h.uvCompression hUV')
    exact ⟨t, q1.trans p1, (card_compression _ _ _).symm.trans q2, q3, q4⟩
termination_by familyMeasure 𝒜

/-! ## Level B namesake -/

/-- **Kruskal–Katona** (Kruskal 1963 / Katona 1968).

Among `r`-uniform families of a given cardinality on `Fin n`, a colex
initial segment minimises the (down) shadow. Known-classical; **no novelty
claim**. Not Sperner, not LYM, not Dilworth, not EKR. -/
theorem kruskal_katona {n r : ℕ} {𝒜 𝒞 : Finset (Finset (Fin n))}
    (h𝒜 : (𝒜 : Set (Finset (Fin n))).Sized r)
    (h𝒞 : IsInitSeg 𝒞 r)
    (hcard : 𝒞.card = 𝒜.card) :
    (shadow 𝒞).card ≤ (shadow 𝒜).card := by
  obtain ⟨ℬ, hℬ𝒜, h𝒜ℬ, hℬr, hℬ⟩ := kruskal_katona_helper 𝒜 h𝒜
  have hcardB : ℬ.card = 𝒞.card := h𝒜ℬ.symm.trans hcard.symm
  have hInit : IsInitSeg ℬ r := isInitSeg_of_compressed hℬr hℬ
  obtain h𝒞ℬ | hℬ𝒞 := h𝒞.total hInit
  · have : 𝒞 = ℬ := eq_of_subset_of_card_le h𝒞ℬ hcardB.le
    subst this
    exact hℬ𝒜
  · have : ℬ = 𝒞 := eq_of_subset_of_card_le hℬ𝒞 hcardB.symm.le
    subst this
    exact hℬ𝒜

/-- Existence of a colex initial segment representing a nonempty `IsInitSeg`.
Named lemma, not a second theorem. Mathlib `IsInitSeg.exists_initSeg`. -/
lemma exists_initSeg {n r : ℕ} {𝒜 : Finset (Finset (Fin n))}
    (h𝒜 : IsInitSeg 𝒜 r) (h𝒜₀ : 𝒜.Nonempty) :
    ∃ s : Finset (Fin n), s.card = r ∧ 𝒜 = initSeg s :=
  h𝒜.exists_initSeg h𝒜₀

end ProofLab.KruskalKatona
