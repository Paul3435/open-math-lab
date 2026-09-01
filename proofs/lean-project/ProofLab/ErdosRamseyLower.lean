/-
Erdős probabilistic Ramsey lower bound (formalize-only).

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 has `SimpleGraph` / `IsNClique` / `cliqueFinset` /
`Fintype (SimpleGraph V)` / `Nat.choose`. ZERO named graph-Ramsey theorem
under `Mathlib/` or `Archive/` (Hindman / Hales–Jewett / homothetic VdW /
Turán are **different** theorems). Completing the first-moment / union-bound
lower bound is the gap. Wiedijk 100.yaml #31 infinite Ramsey is **external**
with **no Mathlib decl**. Do **not** import that file. Do **not** import
`Archive.*`. Do **not** prove infinite Ramsey.

Pin: `catalog/problems/erdos-ramsey-lower/STATEMENT.md` (OPE-858; Scout
OPE-853 prime; Director OPE-857). Encoding: ProofLab `RamseyUpper` /
`HasClique` (red graph `G : SimpleGraph (Fin n)`, blue `Gᶜ`). `n.choose k`
is Mathlib `Nat.choose`. `2 ^ (k / 2)` is `Nat` power of `Nat` division
(so `2 ^ ⌊k/2⌋`). That is the classical elementary bound, **not** the
`(√2)^k / e` sharpening. Zero `sorry`. Do not import `Archive.*`.

This is **not** `ramsey-r33` / `R(3,4)` / `R(4,4)` / `ramsey-r35` /
`ramsey-multicolor-r333` (consumed). Reuse `RamseyUpper` as encoding only.
This is **not** `R(4,6)=41`.
This is **not** infinite Ramsey / Wiedijk #31 external.
This is **not** finite Ramsey existence `∀ k l, ∃ n, RamseyUpper k l n`
(Cassini-class wrap of `ramseyUpper_add`).
This is **not** LLL / Chernoff / Markov / Azuma (union bound is the engine;
LLL consumed #85).
This is **not** Descartes / e-irrational / n-fold PIE / Wolstenholme
(consumed #91/#92/#88/#89).
Do **not** prove zsigmondy-theorem.
Leave OPE-403 alone.

v1 is the union-bound / first-moment criterion, plus the textbook
`2^(k/2)` corollary.

Level A `ramsey_union_bound` is **not** labelled Erdős.
Level B namesake `erdos_ramsey_lower`: `¬ RamseyUpper k k (2^(k/2))` for
`3 ≤ k` via `n.choose k * k! ≤ n^k`.

Transcribed classical argument (Erdős, Bull. AMS 53 (1947); Alon–Spencer
first-moment). No novelty claim.
-/
import ProofLab.Ramsey
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Sym.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

set_option maxHeartbeats 800000
set_option linter.unusedVariables false
set_option linter.dupNamespace false

open Finset SimpleGraph
open scoped BigOperators Nat
open Classical

noncomputable section

namespace ProofLab.ErdosRamseyLower

open ProofLab.Ramsey

/-! ## Glue: labelled graphs ↔ subsets of possible edges

Not labelled Erdős. `Fintype (SimpleGraph (Fin n))` is already Mathlib;
the card identity `= 2^(n.choose 2)` is in-scope glue. -/

/-- Unordered non-loop pairs on `Fin n`. Card `n.choose 2`. -/
abbrev PossibleEdge (n : ℕ) := { e : Sym2 (Fin n) // ¬e.IsDiag }

lemma card_possibleEdge (n : ℕ) : Fintype.card (PossibleEdge n) = n.choose 2 := by
  simpa [Fintype.card_fin] using (Sym2.card_subtype_not_diag (α := Fin n))

/-- Edges present in `G`, as a finset of possible edges. Glue, not namesake. -/
def graphEdges {n : ℕ} (G : SimpleGraph (Fin n)) : Finset (PossibleEdge n) :=
  (univ : Finset (PossibleEdge n)).filter fun e => e.val ∈ G.edgeSet

/-- Rebuild a graph from a set of possible edges. Glue, not namesake. -/
def graphOfEdges {n : ℕ} (s : Finset (PossibleEdge n)) : SimpleGraph (Fin n) :=
  fromEdgeSet (s.map ⟨Subtype.val, Subtype.val_injective⟩ : Finset (Sym2 (Fin n)))

lemma coe_graphEdges {n : ℕ} (G : SimpleGraph (Fin n)) :
    (graphEdges G).map ⟨Subtype.val, Subtype.val_injective⟩ =
      G.edgeSet.toFinset := by
  ext e
  simp only [mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coeFn_mk,
    Set.mem_toFinset, graphEdges]
  constructor
  · rintro ⟨⟨e', hnd⟩, he, rfl⟩
    exact he
  · intro he
    refine ⟨⟨e, G.not_isDiag_of_mem_edgeSet he⟩, he, rfl⟩

lemma graphOfEdges_graphEdges {n : ℕ} (G : SimpleGraph (Fin n)) :
    graphOfEdges (graphEdges G) = G := by
  rw [graphOfEdges, coe_graphEdges, Set.coe_toFinset, fromEdgeSet_edgeSet]

lemma graphEdges_graphOfEdges {n : ℕ} (s : Finset (PossibleEdge n)) :
    graphEdges (graphOfEdges s) = s := by
  ext e
  have hnd := e.property
  simp [graphEdges, graphOfEdges, edgeSet_fromEdgeSet, hnd]

/-- Equivalence: simple graphs on `n` labelled vertices ↔ subsets of the
`n.choose 2` possible edges. Glue, not labelled Erdős. -/
def graphEquiv (n : ℕ) : SimpleGraph (Fin n) ≃ Finset (PossibleEdge n) where
  toFun := graphEdges
  invFun := graphOfEdges
  left_inv := graphOfEdges_graphEdges
  right_inv := graphEdges_graphOfEdges

/-- There are `2^(n.choose 2)` simple graphs on `n` labelled vertices.
Glue, **not** labelled Erdős. -/
lemma card_simpleGraph (n : ℕ) :
    Fintype.card (SimpleGraph (Fin n)) = 2 ^ n.choose 2 := by
  rw [Fintype.card_congr (graphEquiv n), Fintype.card_finset, card_possibleEdge]

/-! ## Internal edges of a vertex set -/

/-- Possible edges with both endpoints in `s`. Glue, not namesake. -/
def internalEdges {n : ℕ} (s : Finset (Fin n)) : Finset (PossibleEdge n) :=
  (univ : Finset (PossibleEdge n)).filter fun e => e.val ∈ s.sym2

lemma mem_internalEdges {n : ℕ} {s : Finset (Fin n)} {e : PossibleEdge n} :
    e ∈ internalEdges s ↔ ∀ a ∈ e.val, a ∈ s := by
  simp [internalEdges, mem_sym2_iff]

lemma val_internalEdges {n : ℕ} (s : Finset (Fin n)) :
    (internalEdges s).map ⟨Subtype.val, Subtype.val_injective⟩ =
      s.offDiag.image fun p => Sym2.mk p := by
  ext e
  simp only [mem_map, mem_internalEdges, Function.Embedding.coeFn_mk, mem_image, mem_offDiag]
  constructor
  · rintro ⟨⟨e', hnd⟩, hmem, rfl⟩
    induction' e' with a b
    refine ⟨(a, b), ?_, rfl⟩
    have hne : a ≠ b := by
      intro h
      exact hnd (by simp [Sym2.mk_isDiag_iff, h])
    have ha : a ∈ s := hmem a (by simp)
    have hb : b ∈ s := hmem b (by simp)
    exact ⟨ha, hb, hne⟩
  · rintro ⟨⟨a, b⟩, ⟨ha, hb, hne⟩, rfl⟩
    refine ⟨⟨s(a, b), ?_⟩, ?_, rfl⟩
    · simpa [Sym2.mk_isDiag_iff] using hne
    · intro x hx
      simp only [Sym2.mem_iff] at hx
      rcases hx with rfl | rfl <;> assumption

lemma card_internalEdges {n : ℕ} (s : Finset (Fin n)) :
    (internalEdges s).card = s.card.choose 2 := by
  rw [← card_map ⟨Subtype.val, Subtype.val_injective⟩, val_internalEdges,
    Sym2.card_image_offDiag]

/-! ## Clique encoding via forced edges -/

lemma isClique_iff_internal {n : ℕ} (G : SimpleGraph (Fin n)) (s : Finset (Fin n)) :
    G.IsClique s ↔ internalEdges s ⊆ graphEdges G := by
  constructor
  · intro h e he
    obtain ⟨e, hnd⟩ := e
    simp only [graphEdges, mem_filter, mem_univ, true_and]
    induction' e with a b
    have hab : a ≠ b := by
      intro hlt
      exact hnd (by simp [Sym2.mk_isDiag_iff, hlt])
    have ha : a ∈ s := (mem_internalEdges.mp he) a (by simp)
    have hb : b ∈ s := (mem_internalEdges.mp he) b (by simp)
    simpa [mem_edgeSet] using h ha hb hab
  · intro h a ha b hb hne
    have hnd : ¬ (s(a, b) : Sym2 (Fin n)).IsDiag := by
      simpa [Sym2.mk_isDiag_iff] using hne
    have he : (⟨s(a, b), hnd⟩ : PossibleEdge n) ∈ internalEdges s := by
      rw [mem_internalEdges]
      intro x hx
      simp only [Sym2.mem_iff] at hx
      rcases hx with hxa | hxb
      · exact hxa ▸ ha
      · exact hxb ▸ hb
    have : s(a, b) ∈ G.edgeSet := by
      have := h he
      simpa [graphEdges] using this
    simpa [mem_edgeSet] using this

lemma isClique_compl_iff_disjoint {n : ℕ} (G : SimpleGraph (Fin n))
    (s : Finset (Fin n)) :
    Gᶜ.IsClique s ↔ Disjoint (internalEdges s) (graphEdges G) := by
  constructor
  · intro h
    rw [disjoint_iff_ne]
    intro e heIn e' heG hEq
    subst hEq
    obtain ⟨e, hnd⟩ := e
    induction' e with a b
    have hab : a ≠ b := by
      intro hlt
      exact hnd (by simp [Sym2.mk_isDiag_iff, hlt])
    have ha : a ∈ s := (mem_internalEdges.mp heIn) a (by simp)
    have hb : b ∈ s := (mem_internalEdges.mp heIn) b (by simp)
    have hAdj : G.Adj a b := by
      have : s(a, b) ∈ G.edgeSet := by
        simpa [graphEdges] using heG
      simpa [mem_edgeSet] using this
    have : Gᶜ.Adj a b := h ha hb hab
    simp [compl_adj, hab] at this
    exact this hAdj
  · intro hdis a ha b hb hne
    have hnd : ¬ (s(a, b) : Sym2 (Fin n)).IsDiag := by
      simpa [Sym2.mk_isDiag_iff] using hne
    have he : (⟨s(a, b), hnd⟩ : PossibleEdge n) ∈ internalEdges s := by
      rw [mem_internalEdges]
      intro x hx
      simp only [Sym2.mem_iff] at hx
      rcases hx with hxa | hxb
      · exact hxa ▸ ha
      · exact hxb ▸ hb
    have hnot : s(a, b) ∉ G.edgeSet := by
      intro hmem
      have heG : (⟨s(a, b), hnd⟩ : PossibleEdge n) ∈ graphEdges G := by
        simpa [graphEdges] using hmem
      exact (disjoint_iff_ne.mp hdis) _ he _ heG rfl
    simp [compl_adj, hne]
    simpa [mem_edgeSet] using hnot

lemma isNClique_iff_internal {n k : ℕ} (G : SimpleGraph (Fin n))
    (s : Finset (Fin n)) :
    G.IsNClique k s ↔ s.card = k ∧ internalEdges s ⊆ graphEdges G := by
  rw [isNClique_iff, isClique_iff_internal, and_comm]

lemma isNClique_compl_iff_disjoint {n k : ℕ} (G : SimpleGraph (Fin n))
    (s : Finset (Fin n)) :
    Gᶜ.IsNClique k s ↔ s.card = k ∧ Disjoint (internalEdges s) (graphEdges G) := by
  rw [isNClique_iff, isClique_compl_iff_disjoint, and_comm]

/-! ## Counting supersets / disjoint sets of edges -/

lemma card_supersets {α : Type*} [DecidableEq α] [Fintype α] (F : Finset α) :
    ((univ : Finset (Finset α)).filter fun s => F ⊆ s).card =
      2 ^ (Fintype.card α - F.card) := by
  let C := (univ : Finset α) \ F
  have hC : C.card = Fintype.card α - F.card := by
    rw [card_sdiff (subset_univ F), card_univ]
  have hbij :
      ((univ : Finset (Finset α)).filter fun s => F ⊆ s).card = C.powerset.card := by
    refine card_bij' (fun s _ => s \ F) (fun t _ => F ∪ t) ?_ ?_ ?_ ?_
    · intro s hs
      simp only [mem_filter, mem_univ, true_and] at hs
      simp only [mem_powerset, C]
      intro x hx
      simp only [mem_sdiff] at hx ⊢
      exact ⟨mem_univ x, hx.2⟩
    · intro t ht
      simp only [mem_powerset] at ht
      simp only [mem_filter, mem_univ, true_and, subset_union_left]
    · intro s hs
      simp only [mem_filter, mem_univ, true_and] at hs
      exact union_sdiff_of_subset hs
    · intro t ht
      simp only [mem_powerset] at ht
      have hdis : Disjoint F t := by
        rw [disjoint_left]
        intro x hxF hxT
        have : x ∈ C := ht hxT
        simp only [C, mem_sdiff] at this
        exact this.2 hxF
      exact union_sdiff_cancel_left hdis
  rw [hbij, card_powerset, hC]

lemma card_disjoint_from {α : Type*} [DecidableEq α] [Fintype α] (F : Finset α) :
    ((univ : Finset (Finset α)).filter fun s => Disjoint F s).card =
      2 ^ (Fintype.card α - F.card) := by
  let C := (univ : Finset α) \ F
  have hC : C.card = Fintype.card α - F.card := by
    rw [card_sdiff (subset_univ F), card_univ]
  have hbij :
      ((univ : Finset (Finset α)).filter fun s => Disjoint F s).card = C.powerset.card := by
    refine card_bij' (fun s _ => s) (fun t _ => t) ?_ ?_ ?_ ?_
    · intro s hs
      simp only [mem_filter, mem_univ, true_and] at hs
      simp only [mem_powerset, C, subset_sdiff]
      exact ⟨subset_univ _, hs.symm⟩
    · intro t ht
      simp only [mem_powerset, C, subset_sdiff] at ht
      simp only [mem_filter, mem_univ, true_and, ht.2.symm]
    · intro s _; rfl
    · intro t _; rfl
  rw [hbij, card_powerset, hC]

lemma card_graphs_supset {n : ℕ} (F : Finset (PossibleEdge n)) :
    ((univ : Finset (SimpleGraph (Fin n))).filter
        fun G => F ⊆ graphEdges G).card =
      2 ^ (n.choose 2 - F.card) := by
  have :
      ((univ : Finset (SimpleGraph (Fin n))).filter fun G => F ⊆ graphEdges G).card =
        ((univ : Finset (Finset (PossibleEdge n))).filter fun s => F ⊆ s).card := by
    refine card_bij' (fun G _ => graphEdges G) (fun s _ => graphOfEdges s) ?_ ?_ ?_ ?_
    · intro G hG
      simp only [mem_filter, mem_univ, true_and] at hG ⊢
      exact hG
    · intro s hs
      simp only [mem_filter, mem_univ, true_and] at hs ⊢
      simpa [graphEdges_graphOfEdges] using hs
    · intro G _; exact graphOfEdges_graphEdges G
    · intro s _; exact graphEdges_graphOfEdges s
  rw [this, card_supersets F, card_possibleEdge]

lemma card_graphs_disjoint {n : ℕ} (F : Finset (PossibleEdge n)) :
    ((univ : Finset (SimpleGraph (Fin n))).filter
        fun G => Disjoint F (graphEdges G)).card =
      2 ^ (n.choose 2 - F.card) := by
  have :
      ((univ : Finset (SimpleGraph (Fin n))).filter
          fun G => Disjoint F (graphEdges G)).card =
        ((univ : Finset (Finset (PossibleEdge n))).filter
          fun s => Disjoint F s).card := by
    refine card_bij' (fun G _ => graphEdges G) (fun s _ => graphOfEdges s) ?_ ?_ ?_ ?_
    · intro G hG
      simp only [mem_filter, mem_univ, true_and] at hG ⊢
      exact hG
    · intro s hs
      simp only [mem_filter, mem_univ, true_and] at hs ⊢
      simpa [graphEdges_graphOfEdges] using hs
    · intro G _; exact graphOfEdges_graphEdges G
    · intro s _; exact graphEdges_graphOfEdges s
  rw [this, card_disjoint_from F, card_possibleEdge]

lemma card_red_clique_graphs {n k : ℕ} {s : Finset (Fin n)} (hs : s.card = k) :
    ((univ : Finset (SimpleGraph (Fin n))).filter
        fun G => G.IsNClique k s).card =
      2 ^ (n.choose 2 - k.choose 2) := by
  have hEq :
      (univ.filter fun G : SimpleGraph (Fin n) => G.IsNClique k s) =
        univ.filter fun G => internalEdges s ⊆ graphEdges G := by
    ext G
    simp [isNClique_iff_internal, hs]
  rw [hEq, card_graphs_supset, card_internalEdges, hs]

lemma card_blue_clique_graphs {n k : ℕ} {s : Finset (Fin n)} (hs : s.card = k) :
    ((univ : Finset (SimpleGraph (Fin n))).filter
        fun G => Gᶜ.IsNClique k s).card =
      2 ^ (n.choose 2 - k.choose 2) := by
  have hEq :
      (univ.filter fun G : SimpleGraph (Fin n) => Gᶜ.IsNClique k s) =
        univ.filter fun G => Disjoint (internalEdges s) (graphEdges G) := by
    ext G
    simp [isNClique_compl_iff_disjoint, hs]
  rw [hEq, card_graphs_disjoint, card_internalEdges, hs]

/-! ## Level A: union-bound / first-moment criterion (not labelled Erdős) -/

lemma ramseyUpper_subset_biUnion {k n : ℕ} (hR : RamseyUpper k k n) :
    (univ : Finset (SimpleGraph (Fin n))) ⊆
      ((univ : Finset (Fin n)).powersetCard k).biUnion fun s =>
        univ.filter (fun G : SimpleGraph (Fin n) => G.IsNClique k s) ∪
          univ.filter (fun G : SimpleGraph (Fin n) => Gᶜ.IsNClique k s) := by
  intro G _
  rcases hR G with h | h
  · obtain ⟨s, hs⟩ := h
    have hsMem : s ∈ (univ : Finset (Fin n)).powersetCard k := by
      exact mem_powersetCard.mpr ⟨subset_univ _, hs.card_eq⟩
    refine mem_biUnion.mpr ⟨s, hsMem, ?_⟩
    exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨mem_univ _, hs⟩))
  · obtain ⟨s, hs⟩ := h
    have hsMem : s ∈ (univ : Finset (Fin n)).powersetCard k := by
      exact mem_powersetCard.mpr ⟨subset_univ _, hs.card_eq⟩
    refine mem_biUnion.mpr ⟨s, hsMem, ?_⟩
    exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨mem_univ _, hs⟩))

/-- If every colouring of `K_n` has a monochromatic `K_k`, then counting
pairs `(G, s)` forces
`2^(n.choose 2) ≤ n.choose k * 2 * 2^(n.choose 2 - k.choose 2)`.
Engine for Level A; **not** labelled Erdős. -/
lemma ramseyUpper_card_le {k n : ℕ} (hR : RamseyUpper k k n) :
    2 ^ n.choose 2 ≤ n.choose k * 2 * 2 ^ (n.choose 2 - k.choose 2) := by
  have hsub := ramseyUpper_subset_biUnion hR
  have hcard := card_le_card hsub
  have hfib : ∀ s ∈ (univ : Finset (Fin n)).powersetCard k,
      ((univ.filter fun G : SimpleGraph (Fin n) => G.IsNClique k s) ∪
          univ.filter (fun G : SimpleGraph (Fin n) => Gᶜ.IsNClique k s)).card ≤
        2 * 2 ^ (n.choose 2 - k.choose 2) := by
    intro s hs
    have hsc : s.card = k := (mem_powersetCard.mp hs).2
    have hred := card_red_clique_graphs (s := s) hsc
    have hblue := card_blue_clique_graphs (s := s) hsc
    have hle := card_union_le
      (univ.filter fun G : SimpleGraph (Fin n) => G.IsNClique k s)
      (univ.filter (fun G : SimpleGraph (Fin n) => Gᶜ.IsNClique k s))
    have h2 : (univ.filter fun G : SimpleGraph (Fin n) => G.IsNClique k s).card +
        (univ.filter (fun G : SimpleGraph (Fin n) => Gᶜ.IsNClique k s)).card =
          2 * 2 ^ (n.choose 2 - k.choose 2) := by
      rw [hred, hblue, two_mul]
    exact hle.trans h2.le
  have hbi := card_biUnion_le_card_mul
    ((univ : Finset (Fin n)).powersetCard k)
    (fun s => univ.filter (fun G : SimpleGraph (Fin n) => G.IsNClique k s) ∪
      univ.filter (fun G : SimpleGraph (Fin n) => Gᶜ.IsNClique k s))
    (2 * 2 ^ (n.choose 2 - k.choose 2)) hfib
  have hpc : ((univ : Finset (Fin n)).powersetCard k).card = n.choose k := by
    simpa [Fintype.card_fin] using (card_powersetCard k (univ : Finset (Fin n)))
  have : (univ : Finset (SimpleGraph (Fin n))).card ≤
      n.choose k * 2 * 2 ^ (n.choose 2 - k.choose 2) := by
    calc
      (univ : Finset (SimpleGraph (Fin n))).card ≤
          (((univ : Finset (Fin n)).powersetCard k).biUnion fun s =>
              univ.filter (fun G : SimpleGraph (Fin n) => G.IsNClique k s) ∪
                univ.filter (fun G : SimpleGraph (Fin n) => Gᶜ.IsNClique k s)).card := hcard
      _ ≤ ((univ : Finset (Fin n)).powersetCard k).card *
            (2 * 2 ^ (n.choose 2 - k.choose 2)) := hbi
      _ = n.choose k * (2 * 2 ^ (n.choose 2 - k.choose 2)) := by rw [hpc]
      _ = n.choose k * 2 * 2 ^ (n.choose 2 - k.choose 2) := by ring
  simpa [card_univ, card_simpleGraph] using this

/-- Level A union-bound criterion. **Not** labelled `erdos_ramsey_lower`.
If `n.choose k * 2 < 2^(k.choose 2)`, then some red/blue colouring of `K_n`
has no monochromatic `K_k`. Empty/small `n < k` is allowed (`n.choose k = 0`). -/
theorem ramsey_union_bound {k n : ℕ} (hk : 2 ≤ k)
    (h : n.choose k * 2 < 2 ^ (k.choose 2)) :
    ¬ RamseyUpper k k n := by
  intro hR
  have hle := ramseyUpper_card_le hR
  -- `k.choose 2 ≤ n.choose 2` may fail when `k > n`; handle via the
  -- covering bound directly.
  by_cases hkn : k ≤ n
  · have h2le : k.choose 2 ≤ n.choose 2 := Nat.choose_le_choose 2 hkn
    have hpow :
        2 ^ n.choose 2 =
          2 ^ (n.choose 2 - k.choose 2) * 2 ^ (k.choose 2) := by
      rw [← pow_add, Nat.sub_add_cancel h2le]
    have hpos : 0 < 2 ^ (n.choose 2 - k.choose 2) := pow_pos (by norm_num) _
    have : 2 ^ (n.choose 2 - k.choose 2) * 2 ^ (k.choose 2) ≤
        2 ^ (n.choose 2 - k.choose 2) * (n.choose k * 2) := by
      simpa [hpow, mul_left_comm, mul_assoc, mul_comm] using hle
    have : 2 ^ (k.choose 2) ≤ n.choose k * 2 :=
      Nat.le_of_mul_le_mul_left this hpos
    exact (not_le_of_gt h) this
  · -- `n < k`: no `k`-set, covering is empty, but there is at least one graph.
    have hklt : n < k := Nat.lt_of_not_ge hkn
    have hz : n.choose k = 0 := Nat.choose_eq_zero_of_lt hklt
    have hle' : 2 ^ n.choose 2 ≤ 0 := by simpa [hz] using hle
    have hpos : 0 < 2 ^ n.choose 2 := pow_pos (by norm_num) _
    exact (not_le_of_gt hpos) hle'

/-! ## Level B namesake: `R(k,k) > 2^(k/2)` for `k ≥ 3` -/

lemma choose_mul_factorial_le_pow (n k : ℕ) : n.choose k * k ! ≤ n ^ k := by
  rw [Nat.mul_comm]
  simpa [Nat.descFactorial_eq_factorial_mul_choose] using n.descFactorial_le_pow k

lemma two_lt_factorial_of_three_le {k : ℕ} (hk : 3 ≤ k) : 2 < k ! :=
  lt_of_lt_of_le (by decide : 2 < 3 !) (Nat.factorial_le hk)

lemma two_pow_succ_lt_factorial_two_mul :
    ∀ m ≥ 2, 2 ^ (m + 1) < (2 * m) ! := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    have hfac : 2 * (2 * m) ! < (2 * (m + 1)) ! := by
      -- `(2m+2)! = (2m+2)(2m+1)(2m)!` and `(2m+2)(2m+1) ≥ 2`.
      rw [show 2 * (m + 1) = 2 * m + 2 by ring, Nat.factorial_succ, Nat.factorial_succ]
      have hpos : 0 < (2 * m) ! := Nat.factorial_pos _
      have hmul : 2 < (2 * m + 1 + 1) * (2 * m + 1) := by
        nlinarith
      calc
        2 * (2 * m) ! < (2 * m + 1 + 1) * (2 * m + 1) * (2 * m) ! :=
          Nat.mul_lt_mul_of_pos_right hmul hpos
        _ = (2 * m + 1 + 1) * ((2 * m + 1) * (2 * m) !) := by ring
    calc
      2 ^ (m + 1 + 1) = 2 ^ (m + 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (m + 1) := by rw [mul_comm]
      _ < 2 * (2 * m) ! := Nat.mul_lt_mul_of_pos_left ih (by norm_num)
      _ < (2 * (m + 1)) ! := hfac

lemma even_choose_two (m : ℕ) : (2 * m).choose 2 = m * (2 * m - 1) := by
  rw [Nat.choose_two_right]
  cases m with
  | zero => simp
  | succ m =>
    have h2 : 2 * (m + 1) * (2 * (m + 1) - 1) =
        2 * ((m + 1) * (2 * (m + 1) - 1)) := by ring
    rw [h2, Nat.mul_div_right _ (by norm_num : (0 : ℕ) < 2)]

lemma odd_choose_two (m : ℕ) : (2 * m + 1).choose 2 = m * (2 * m + 1) := by
  rw [Nat.choose_two_right]
  simp only [Nat.add_sub_cancel]
  have h2 : (2 * m + 1) * (2 * m) = 2 * (m * (2 * m + 1)) := by ring
  rw [h2, Nat.mul_div_right _ (by norm_num : (0 : ℕ) < 2)]

lemma two_mul_pow_lt_factorial_pow_choose {k : ℕ} (hk : 3 ≤ k) :
    2 * (2 ^ (k / 2)) ^ k < k ! * 2 ^ (k.choose 2) := by
  have hpow : 2 * (2 ^ (k / 2)) ^ k = 2 ^ (1 + k / 2 * k) := by
    rw [← pow_mul, add_comm, pow_succ']
  rw [hpow]
  rcases Nat.mod_two_eq_zero_or_one k with heven | hodd
  · let m := k / 2
    have hm : 2 ≤ m := by omega
    have hk2 : k = 2 * m := by omega
    have hexp : 1 + m * k = k.choose 2 + (m + 1) := by
      rw [hk2, even_choose_two]
      have h1 : 1 ≤ 2 * m := by omega
      have hdist : m * (2 * m - 1) = m * (2 * m) - m := by
        rw [Nat.mul_sub_left_distrib, Nat.mul_one]
      rw [hdist]
      have hle : m ≤ m * (2 * m) := Nat.le_mul_of_pos_right m h1
      rw [← add_assoc, Nat.sub_add_cancel hle]
      ring
    rw [show 1 + k / 2 * k = 1 + m * k from rfl, hexp, pow_add, mul_comm (k !)]
    have hlt : 2 ^ (m + 1) < k ! := by
      have := two_pow_succ_lt_factorial_two_mul m hm
      rwa [show 2 * m = k from hk2.symm] at this
    exact Nat.mul_lt_mul_of_pos_left hlt (pow_pos (by norm_num : (0 : ℕ) < 2) _)
  · let m := k / 2
    have hk2 : k = 2 * m + 1 := by omega
    have hexp : 1 + m * k = k.choose 2 + 1 := by
      rw [hk2, odd_choose_two]
      ring
    rw [show 1 + k / 2 * k = 1 + m * k from rfl, hexp, pow_succ, mul_comm (k !)]
    exact Nat.mul_lt_mul_of_pos_left (two_lt_factorial_of_three_le hk)
      (pow_pos (by norm_num : (0 : ℕ) < 2) _)

/-- Criterion at `n = 2^(k/2)`: the binomial test fires. Engine for the
namesake; **not** labelled Erdős. -/
lemma choose_two_pow_mul_two_lt {k : ℕ} (hk : 3 ≤ k) :
    (2 ^ (k / 2)).choose k * 2 < 2 ^ (k.choose 2) := by
  set n := 2 ^ (k / 2)
  by_cases hkn : k ≤ n
  · have hfac := choose_mul_factorial_le_pow n k
    have hlt := two_mul_pow_lt_factorial_pow_choose (k := k) hk
    have hle : n.choose k * 2 * k ! ≤ 2 * n ^ k := by
      calc
        n.choose k * 2 * k ! = 2 * (n.choose k * k !) := by ring
        _ ≤ 2 * n ^ k := Nat.mul_le_mul_left _ hfac
    have : n.choose k * 2 * k ! < k ! * 2 ^ (k.choose 2) :=
      lt_of_le_of_lt hle (by simpa [n] using hlt)
    have hrew : n.choose k * 2 * k ! = k ! * (n.choose k * 2) := by ring
    rw [hrew] at this
    exact Nat.lt_of_mul_lt_mul_left this
  · have hz : n.choose k = 0 := Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hkn)
    simp [hz]

/-- Namesake: classical Erdős 1947 first-moment bound
`R(k,k) > 2^(⌊k/2⌋)` for `k ≥ 3`. **No novelty claim.**
Not the `(√2)^k / e` sharpening. Not LLL. Not Spencer off-diagonal. -/
theorem erdos_ramsey_lower (k : ℕ) (hk : 3 ≤ k) :
    ¬ RamseyUpper k k (2 ^ (k / 2)) :=
  ramsey_union_bound (le_trans (by decide : 2 ≤ 3) hk) (choose_two_pow_mul_two_lt hk)

end ProofLab.ErdosRamseyLower
