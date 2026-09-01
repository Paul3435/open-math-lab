/-
n-fold inclusion-exclusion (de Moivre / Whitney; Wiedijk 100 #96).

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 has `Finset.card` / `union` / `inter` / `biUnion`,
two-set `card_union` / `card_union_add_card_inter`
(`Data/Finset/Card.lean` — **already upstream; used, not re-proved**),
disjoint `card_biUnion` (pairwise-disjoint hyp — **different** theorem),
`card_biUnion_le` (union bound — **different**), `Finset.powerset` /
`erase`, and `Finset.inf'` (`Data/Finset/Lattice.lean`). ZERO named
n-fold inclusion-exclusion / `inclusion_exclusion` / PIE identity under
`Mathlib/` or `Archive/`. Wiedijk 100.yaml #96 lists only an external
Lean 3 link (Neil Strickland `lean_lib`) — **not** a Mathlib decl.
Completing the namesake is the gap.

Pin: `catalog/problems/n-fold-inclusion-exclusion/STATEMENT.md`
(OPE-827; Scout OPE-821 recommended prime; Director OPE-826).
Encoding: `Finset.biUnion` + `powerset.erase ∅` + `inf'` intersections
+ `ℤ` signs. Zero `sorry`. Do not import `Archive.*`.

This is **not** two-set `card_union` / `card_union_add_card_inter`.
This is **not** disjoint `card_biUnion`.
This is **not** Bonferroni / truncated PIE / sieve remainder.
This is **not** derangement / Catalan (already Mathlib
`numDerangements` / `catalan`).
This is **not** Stirling second kind (consumed PR #77).
This is **not** ballot / birthday (Archive-only; do not import).
This is **not** LLL (consumed #85) / Korselt (consumed #86).
Do **not** assume `[Fintype α]`. Leave OPE-403 alone.

Level A `card_union_three` is the three-set identity via two-set
`card_union` twice. **Not** labelled PIE.
Level B namesake `inclusion_exclusion` is induction on `s` (insert +
two-set split of the signed powerset sum). Empty index: both sides 0
(`biUnion` empty, nonempty-powerset sum empty). `s.powerset.erase ∅`
is load-bearing: the empty intersection would otherwise need a top
`univ` that `Finset α` does not have without `Fintype α`.

The STATEMENT.md `(by ...)` hole on `interOver` is filled by
`signedCard`: on `s.powerset.erase ∅` every index is nonempty, so
`signedCard t A = (-1)^{t.card+1} * (interOver t A h).card`.

Transcribed classical argument (de Moivre / Whitney; compact form
Wikipedia *Inclusion–exclusion principle*).
-/
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option maxHeartbeats 400000

open Finset

namespace ProofLab.InclusionExclusion

variable {ι α : Type*} [DecidableEq ι] [DecidableEq α]

/-! ## Pins (match STATEMENT.md) -/

/-- Intersection of `A j` over a nonempty index `t`. Uses `inf'` so we
do not need `Fintype α` / `univ`. -/
def interOver (t : Finset ι) (A : ι → Finset α) (h : t.Nonempty) : Finset α :=
  t.inf' h A

/-- Signed intersection cardinality. Empty index is `0` (no `univ`
without `Fintype α`). On `s.powerset.erase ∅` the `else` branch is
dead; it exists so the summand is a total function of `t`. -/
def signedCard (t : Finset ι) (A : ι → Finset α) : ℤ :=
  if h : t.Nonempty then
    (-1 : ℤ) ^ (t.card + 1) * (interOver t A h).card
  else
    0

/-! ## Glue -/

lemma mem_interOver {t : Finset ι} {A : ι → Finset α} (h : t.Nonempty) {x : α} :
    x ∈ interOver t A h ↔ ∀ i ∈ t, x ∈ A i := by
  constructor
  · intro hx i hi
    have hx' : {x} ≤ interOver t A h := singleton_subset_iff.mpr hx
    have : {x} ≤ A i := (le_inf'_iff (H := h) (f := A)).mp hx' i hi
    exact singleton_subset_iff.mp this
  · intro hx
    have : {x} ≤ t.inf' h A := by
      rw [le_inf'_iff]
      intro i hi
      exact singleton_subset_iff.mpr (hx i hi)
    exact singleton_subset_iff.mp this

lemma interOver_singleton (i : ι) (A : ι → Finset α) :
    interOver {i} A (singleton_nonempty i) = A i := by
  simp [interOver]

lemma interOver_insert (a : ι) {t : Finset ι} (ht : t.Nonempty) (A : ι → Finset α) :
    interOver (insert a t) A (insert_nonempty a t) = A a ∩ interOver t A ht := by
  simp only [interOver]
  exact inf'_insert (H := ht) (f := A)

lemma interOver_inter (t : Finset ι) (X : Finset α) (A : ι → Finset α) (h : t.Nonempty) :
    interOver t (fun j => X ∩ A j) h = X ∩ interOver t A h := by
  ext x
  simp only [mem_interOver, mem_inter]
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := h
    exact ⟨(hx i hi).1, fun j hj => (hx j hj).2⟩
  · intro hx i hi
    exact ⟨hx.1, hx.2 i hi⟩

lemma signedCard_empty (A : ι → Finset α) : signedCard (∅ : Finset ι) A = 0 := by
  simp [signedCard]

lemma signedCard_of_nonempty {t : Finset ι} (h : t.Nonempty) (A : ι → Finset α) :
    signedCard t A = (-1 : ℤ) ^ (t.card + 1) * (interOver t A h).card := by
  simp [signedCard, h]

lemma signedCard_singleton (a : ι) (A : ι → Finset α) :
    signedCard ({a} : Finset ι) A = (A a).card := by
  rw [signedCard_of_nonempty (singleton_nonempty a), interOver_singleton]
  simp

lemma nonempty_of_mem_powerset_erase_empty {s t : Finset ι}
    (ht : t ∈ s.powerset.erase (∅ : Finset ι)) : t.Nonempty :=
  nonempty_iff_ne_empty.2 (mem_erase.mp ht).1

lemma sum_signedCard_eq_erase (s : Finset ι) (A : ι → Finset α) :
    ∑ t ∈ s.powerset, signedCard t A =
      ∑ t ∈ s.powerset.erase (∅ : Finset ι), signedCard t A := by
  rw [sum_erase]
  exact signedCard_empty A

lemma signedCard_insert_nonempty (a : ι) {t : Finset ι} (ht : t.Nonempty)
    (ha : a ∉ t) (A : ι → Finset α) :
    signedCard (insert a t) A = - signedCard t (fun j => A a ∩ A j) := by
  have hins : (insert a t).Nonempty := insert_nonempty a t
  rw [signedCard_of_nonempty hins, signedCard_of_nonempty ht, interOver_insert a ht,
    interOver_inter, card_insert_of_not_mem ha]
  simp [pow_succ, mul_comm, mul_left_comm, neg_mul, mul_neg]

/-! ## Level A: three-set identity (not labelled PIE) -/

/-- Three-set union cardinality via two-set `card_union` twice.
Glue, **not** the n-fold namesake. -/
theorem card_union_three (A B C : Finset α) :
    ((A ∪ B ∪ C).card : ℤ) =
      (A.card : ℤ) + B.card + C.card
        - (A ∩ B).card - (A ∩ C).card - (B ∩ C).card
        + (A ∩ B ∩ C).card := by
  have hAB : ((A ∪ B).card : ℤ) = A.card + B.card - (A ∩ B).card :=
    cast_card_union
  have hABC : ((A ∪ B ∪ C).card : ℤ) =
      ((A ∪ B).card : ℤ) + C.card - ((A ∪ B) ∩ C).card :=
    cast_card_union
  have hcap : (A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C) := by
    rw [inter_comm, inter_union_distrib_left]
    simp [inter_comm]
  have hinter : (((A ∩ C) ∪ (B ∩ C)).card : ℤ) =
      ((A ∩ C).card : ℤ) + (B ∩ C).card - ((A ∩ C) ∩ (B ∩ C)).card :=
    cast_card_union
  have hinter2 : (A ∩ C) ∩ (B ∩ C) = A ∩ B ∩ C := by
    ext x; simp [and_comm, and_left_comm, and_assoc]
  rw [hABC, hAB, hcap, hinter, hinter2]
  ring

/-! ## Level B: namesake n-fold inclusion-exclusion -/

lemma inclusion_exclusion_sum (s : Finset ι) :
    ∀ (A : ι → Finset α), ((s.biUnion A).card : ℤ) = ∑ t ∈ s.powerset, signedCard t A := by
  refine Finset.induction_on s ?empty ?insert
  · intro A
    simp [signedCard]
  · intro a s ha ih A
    have hunion :
        (((insert a s).biUnion A).card : ℤ) =
          (A a).card + (s.biUnion A).card - (A a ∩ s.biUnion A).card := by
      rw [biUnion_insert, cast_card_union]
    have hinter :
        ((A a ∩ s.biUnion A).card : ℤ) =
          ((s.biUnion fun j => A a ∩ A j).card : ℤ) := by
      rw [inter_biUnion]
    rw [hunion, hinter, ih A, ih (fun j => A a ∩ A j)]
    rw [sum_powerset_insert ha]
    have hsplit :
        ∑ t ∈ s.powerset, signedCard (insert a t) A =
          (A a).card + ∑ t ∈ s.powerset.erase (∅ : Finset ι),
            signedCard (insert a t) A := by
      have hmem : (∅ : Finset ι) ∈ s.powerset := empty_mem_powerset s
      rw [← add_sum_erase _ _ hmem, insert_emptyc_eq, signedCard_singleton]
    have hneg :
        ∑ t ∈ s.powerset.erase (∅ : Finset ι), signedCard (insert a t) A =
          - ∑ t ∈ s.powerset.erase (∅ : Finset ι),
              signedCard t (fun j => A a ∩ A j) := by
      rw [← sum_neg_distrib]
      apply sum_congr rfl
      intro t ht
      have ht0 : t.Nonempty := nonempty_of_mem_powerset_erase_empty ht
      have hat : a ∉ t :=
        not_mem_of_mem_powerset_of_not_mem (mem_of_mem_erase ht) ha
      exact signedCard_insert_nonempty a ht0 hat A
    have hempty_rhs :
        ∑ t ∈ s.powerset, signedCard t (fun j => A a ∩ A j) =
          ∑ t ∈ s.powerset.erase (∅ : Finset ι),
            signedCard t (fun j => A a ∩ A j) :=
      sum_signedCard_eq_erase _ _
    rw [hsplit, hneg, hempty_rhs]
    ring

/-- Signed n-fold inclusion-exclusion. Empty index omitted via
`powerset.erase ∅` so we never need `Fintype α`. Unfolds to the
STATEMENT.md identity: on this range every `t` is nonempty, so
`signedCard t A = (-1)^{t.card+1} * (interOver t A h).card`. -/
theorem inclusion_exclusion (s : Finset ι) (A : ι → Finset α) :
    ((s.biUnion A).card : ℤ) =
      ∑ t ∈ s.powerset.erase (∅ : Finset ι), signedCard t A := by
  rw [inclusion_exclusion_sum, sum_signedCard_eq_erase]

/-- STATEMENT.md unfolding: the `signedCard` summand is the signed
`interOver` cardinality on every nonempty index. -/
theorem signedCard_eq_interOver {t : Finset ι} (h : t.Nonempty) (A : ι → Finset α) :
    signedCard t A = (-1 : ℤ) ^ (t.card + 1) * (interOver t A h).card :=
  signedCard_of_nonempty h A

end ProofLab.InclusionExclusion
