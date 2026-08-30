/-
Oddtown (Berlekamp 1969 / Babai–Frankl): a family of odd-cardinality subsets
of an `n`-set with even pairwise intersections has size at most `n`.

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 has `LinearIndependent`, `ZMod`, `Finset`, and graph
`incMatrix` (wrong matrix). ZERO Oddtown / Eventown / Berlekamp theorem ident.

Pin: `catalog/problems/oddtown/STATEMENT.md` (OPE-712; Scout OPE-702 leftover
slot #2; Director OPE-711). Encoding: ground set `Fin n`; family
`𝒜 : Finset (Finset (Fin n))`; engine `charVec` over `ZMod 2`.
Zero `sorry`. Do not import `Archive.*`. Do not import graph `incMatrix`.

This is **not** EKR (`ProofLab/ErdosKoRado.lean` already has `erdos_ko_rado`).
This is **not** Eventown (`m ≤ 2^{n-1}` even-town — out of v1).
This is **not** Fisher / BIBD / Hilton–Milner.
This is **not** Kruskal–Katona / Sperner / LYM (Kruskal consumed OPE-707).
Characteristic vectors over `ZMod 2`, not `ℝ`. Finite only.

Level A: empty family; `n = 0`; `n = 1` (at most `{ {0} }`); the `n`
singletons achieve tightness `m = n`. Zero sorry. Not labelled Oddtown.
Level B: namesake `oddtown` by linear independence of `charVec` over `ZMod 2`.
-/
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.ZMod.Parity
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.LinearIndependent
import Mathlib.Tactic

set_option maxHeartbeats 400000

open Finset Function FiniteDimensional

set_option linter.dupNamespace false

noncomputable section
open Classical

namespace ProofLab.Oddtown

variable {n : ℕ}

/-! ## Characteristic vectors and the Oddtown predicate -/

/-- Characteristic vector of a subset of `Fin n` over `GF(2)`. Engine, not a
second id. Not graph `incMatrix`. -/
def charVec (s : Finset (Fin n)) : Fin n → ZMod 2 :=
  fun i => if i ∈ s then 1 else 0

/-- Oddtown family: odd sizes, even pairwise intersections. -/
def Oddtown (𝒜 : Finset (Finset (Fin n))) : Prop :=
  (∀ s ∈ 𝒜, Odd s.card) ∧
  (∀ s ∈ 𝒜, ∀ t ∈ 𝒜, s ≠ t → Even (s ∩ t).card)

/-! ## Level A: empty / `n = 0` / `n = 1` / singleton tightness (not labelled Oddtown) -/

/-- The empty family has cardinality `0 ≤ n`. Glue, not Oddtown. -/
theorem empty_family_card_le : (∅ : Finset (Finset (Fin n))).card ≤ n := by
  simp

/-- On `Fin 0` every subset is empty. Glue. -/
lemma finset_fin_zero (s : Finset (Fin 0)) : s = ∅ := by
  ext x
  exact x.elim0

/-- On `Fin 0` there is no odd-cardinality subset. Glue. -/
theorem no_odd_subset_n_zero {s : Finset (Fin 0)} : ¬ Odd s.card := by
  rw [finset_fin_zero s]
  decide

/-- On `Fin 0`, a family of odd-cardinality sets is empty. Glue, not Oddtown. -/
theorem n_zero_odd_family_empty {𝒜 : Finset (Finset (Fin 0))}
    (h : ∀ s ∈ 𝒜, Odd s.card) : 𝒜 = ∅ := by
  ext s
  simp only [not_mem_empty, iff_false]
  intro hs
  exact no_odd_subset_n_zero (h s hs)

/-- On `Fin 0`, a family of odd-cardinality sets has size `0`. Glue. -/
theorem n_zero_card_le {𝒜 : Finset (Finset (Fin 0))}
    (h : ∀ s ∈ 𝒜, Odd s.card) : 𝒜.card ≤ 0 := by
  simp [n_zero_odd_family_empty h]

/-- Every subset of `Fin 1` is `∅` or `{0}`. Glue. -/
lemma finset_fin_one (s : Finset (Fin 1)) : s = ∅ ∨ s = {0} := by
  have : s ⊆ {0} := by
    intro x _
    simp [Fin.eq_zero x]
  exact subset_singleton_iff.mp this

/-- An odd-cardinality subset of `Fin 1` is `{0}`. Glue. -/
theorem n_one_odd_subset {s : Finset (Fin 1)} (hs : Odd s.card) : s = {0} := by
  rcases finset_fin_one s with rfl | rfl
  · simp at hs
  · rfl

/-- On `Fin 1`, a family of odd-cardinality sets is contained in `{ {0} }`. Glue. -/
theorem n_one_odd_family {𝒜 : Finset (Finset (Fin 1))}
    (h : ∀ s ∈ 𝒜, Odd s.card) : 𝒜 ⊆ {{0}} := by
  intro s hs
  simpa using n_one_odd_subset (h s hs)

/-- On `Fin 1`, a family of odd-cardinality sets has size at most `1`. Glue. -/
theorem n_one_card_le {𝒜 : Finset (Finset (Fin 1))}
    (h : ∀ s ∈ 𝒜, Odd s.card) : 𝒜.card ≤ 1 := by
  exact (card_le_card (n_one_odd_family h)).trans (by simp)

/-- The family of all singletons on `Fin n`. Glue, not Oddtown. -/
def singletons (n : ℕ) : Finset (Finset (Fin n)) :=
  univ.image fun i : Fin n => {i}

/-- There are exactly `n` singletons. Glue; tightness witness. -/
theorem singletons_card (n : ℕ) : (singletons n).card = n := by
  rw [singletons, card_image_of_injective _ singleton_injective, card_univ,
    Fintype.card_fin]

lemma mem_singletons {s : Finset (Fin n)} :
    s ∈ singletons n ↔ ∃ i, s = {i} := by
  simp [singletons, eq_comm]

/-- Each singleton has odd cardinality. Glue. -/
theorem singletons_odd {s : Finset (Fin n)} (hs : s ∈ singletons n) :
    Odd s.card := by
  obtain ⟨i, rfl⟩ := mem_singletons.mp hs
  simp

/-- Distinct singletons have empty (hence even) intersection. Glue. -/
theorem singletons_even_inter {s t : Finset (Fin n)}
    (hs : s ∈ singletons n) (ht : t ∈ singletons n) (hne : s ≠ t) :
    Even (s ∩ t).card := by
  obtain ⟨i, rfl⟩ := mem_singletons.mp hs
  obtain ⟨j, rfl⟩ := mem_singletons.mp ht
  have hij : i ≠ j := fun h => hne (by rw [h])
  rw [singleton_inter_of_not_mem (by simpa using hij)]
  simp

/-- The `n` singletons are odd, pairwise even-intersecting, and have size `n`.
Tightness. Not labelled Oddtown. -/
theorem singletons_tight (n : ℕ) :
    (∀ s ∈ singletons n, Odd s.card) ∧
      (∀ s ∈ singletons n, ∀ t ∈ singletons n, s ≠ t → Even (s ∩ t).card) ∧
        (singletons n).card = n :=
  ⟨fun _ hs => singletons_odd hs,
    fun _ hs _ ht hne => singletons_even_inter hs ht hne,
    singletons_card n⟩

/-! ## Engine: Gram form of `charVec` over `ZMod 2` -/

/-- Pointwise inner product over `GF(2)`. Not an `InnerProductSpace` (that is `ℝ`). -/
def gram (f g : Fin n → ZMod 2) : ZMod 2 :=
  ∑ i, f i * g i

lemma charVec_mul (s t : Finset (Fin n)) (i : Fin n) :
    charVec s i * charVec t i = charVec (s ∩ t) i := by
  simp only [charVec, mem_inter]
  split_ifs <;> simp_all

lemma filter_univ_mem (s : Finset (Fin n)) :
    univ.filter (· ∈ s) = s := by
  ext x
  simp

/-- `⟨charVec s, charVec t⟩ = |s ∩ t|` in `ZMod 2`. -/
lemma gram_charVec (s t : Finset (Fin n)) :
    gram (charVec s) (charVec t) = (s ∩ t).card := by
  simp only [gram]
  simp_rw [charVec_mul]
  simp only [charVec]
  rw [sum_boole, filter_univ_mem]

lemma gram_charVec_self {s : Finset (Fin n)} (hs : Odd s.card) :
    gram (charVec s) (charVec s) = 1 := by
  rw [gram_charVec, inter_self, ZMod.eq_one_iff_odd]
  exact hs

lemma gram_charVec_of_even {s t : Finset (Fin n)} (h : Even (s ∩ t).card) :
    gram (charVec s) (charVec t) = 0 := by
  rw [gram_charVec, ZMod.eq_zero_iff_even]
  exact h

lemma gram_zero (g : Fin n → ZMod 2) : gram 0 g = 0 := by
  simp [gram]

lemma gram_sum {ι : Type*} [Fintype ι] (v : ι → Fin n → ZMod 2)
    (c : ι → ZMod 2) (w : Fin n → ZMod 2) :
    gram (∑ i, c i • v i) w = ∑ i, c i * gram (v i) w := by
  simp only [gram]
  calc
    ∑ j, (∑ i, c i • v i) j * w j
      = ∑ j, (∑ i, (c i • v i) j) * w j := by
        simp [Finset.sum_apply]
    _ = ∑ j, (∑ i, c i * v i j) * w j := by
        simp [Pi.smul_apply, smul_eq_mul]
    _ = ∑ j, ∑ i, c i * v i j * w j := by
        simp [sum_mul]
    _ = ∑ i, ∑ j, c i * v i j * w j := by
        rw [sum_comm]
    _ = ∑ i, c i * ∑ j, v i j * w j := by
        simp [mul_assoc, mul_sum]

/-- Characteristic vectors of an Oddtown family are linearly independent over
`GF(2)`. Named engine, not a leftover id. -/
theorem charVec_linearIndependent {𝒜 : Finset (Finset (Fin n))} (h : Oddtown 𝒜) :
    LinearIndependent (ZMod 2) (fun s : 𝒜 => charVec (s : Finset (Fin n))) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg s
  have hgram :
      gram (∑ t : 𝒜, g t • charVec (t : Finset (Fin n)))
        (charVec (s : Finset (Fin n))) = 0 := by
    rw [hg]
    exact gram_zero _
  rw [gram_sum] at hgram
  have hsum :
      (∑ t : 𝒜, g t * gram (charVec (t : Finset (Fin n)))
        (charVec (s : Finset (Fin n)))) =
        g s * gram (charVec (s : Finset (Fin n)))
          (charVec (s : Finset (Fin n))) := by
    apply Fintype.sum_eq_single s
    intro t hts
    have hne : (t : Finset (Fin n)) ≠ (s : Finset (Fin n)) :=
      fun heq => hts (Subtype.ext heq)
    rw [gram_charVec_of_even (h.2 t.1 t.2 s.1 s.2 hne), mul_zero]
  rw [hsum, gram_charVec_self (h.1 s.1 s.2), mul_one] at hgram
  exact hgram

/-! ## Level B namesake -/

/-- **Oddtown** (Berlekamp 1969 / Babai–Frankl linear algebra method).

A family of odd-cardinality subsets of `Fin n` with even pairwise
intersections has size at most `n`. Known-classical; **no novelty claim**.
Not EKR, not Eventown, not Fisher, not Sperner/LYM, not Kruskal–Katona. -/
theorem oddtown {𝒜 : Finset (Finset (Fin n))} (h : Oddtown 𝒜) : 𝒜.card ≤ n := by
  have hli := charVec_linearIndependent h
  have hle : Fintype.card { x // x ∈ 𝒜 } ≤
      finrank (ZMod 2) (Fin n → ZMod 2) :=
    hli.fintype_card_le_finrank
  have hr : finrank (ZMod 2) (Fin n → ZMod 2) = Fintype.card (Fin n) :=
    FiniteDimensional.finrank_pi (R := ZMod 2)
  have hcoe : Fintype.card { x // x ∈ 𝒜 } = 𝒜.card := Fintype.card_coe 𝒜
  have hfin : Fintype.card (Fin n) = n := Fintype.card_fin n
  linarith

end ProofLab.Oddtown
