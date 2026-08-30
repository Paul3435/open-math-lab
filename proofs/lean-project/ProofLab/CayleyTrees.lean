/-
Cayley's formula (Cayley 1889 / Prüfer 1918): the number of labelled
trees on `Fin n` is `n^{n-2}`.

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 has `IsTree` / `IsTree.card_edgeFinset` / `fromEdgeSet`
and ZERO Prüfer code / ZERO labelled-tree cardinality.

Pin: `catalog/problems/cayley-trees/STATEMENT.md` (OPE-688).
Encoding: edge-Finsets, **not** `{G : SimpleGraph (Fin n) // G.IsTree}`.
`fromEdgeSet` drops diagonals — `LabelledTree` therefore requires
`∀ e ∈ s, ¬ e.IsDiag` so looped Sym2's are not extra trees.
Zero `sorry`. Do not import `Archive.*`.

This is **not** group Cayley's theorem, **not** Cayley–Hamilton,
**not** the Cayley graph of a group, **not** Kirchhoff / matrix-tree,
**not** Tutte / Whitney / unlabelled A000055.

Level A: `n = 1` empty / `⊥`; `n = 2` `K₂`; `n = 3` three labelled
paths; glue `IsTree.card_edgeFinset` (`|E| = n-1`). Zero sorry.
Level B residual (not sorry-ed): namesake `cayley_formula` via Prüfer
bijection `LabelledTree n ≃ Fin (n-2) → Fin n` for `n ≥ 2` (or an
equivalent induction). Cap two levels. No matrix-tree / no Tutte /
no unlabelled count.
-/
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

open Finset Function SimpleGraph

noncomputable section
open Classical

namespace ProofLab.CayleyTrees

/-! ## Pinned encoding (load-bearing) -/

/-- Edge-sets of labelled trees on `Fin n`. Loops are excluded:
`fromEdgeSet` would drop them and over-count (landmine). -/
def LabelledTree (n : ℕ) : Type :=
  { s : Finset (Sym2 (Fin n)) //
      (∀ e ∈ s, ¬ e.IsDiag) ∧
        (SimpleGraph.fromEdgeSet (s : Set (Sym2 (Fin n)))).IsTree }

instance instFintypeLabelledTree (n : ℕ) : Fintype (LabelledTree n) :=
  Subtype.fintype _

def graphOf {n : ℕ} (s : Finset (Sym2 (Fin n))) : SimpleGraph (Fin n) :=
  fromEdgeSet (s : Set (Sym2 (Fin n)))

lemma nodiag_of (t : LabelledTree n) : ∀ e ∈ t.1, ¬ e.IsDiag := t.2.1

lemma isTree_of (t : LabelledTree n) : (graphOf t.1).IsTree := t.2.2

/-! ## Edge-Finset glue -/

lemma edgeFinset_graphOf {n : ℕ} {s : Finset (Sym2 (Fin n))}
    (hs : ∀ e ∈ s, ¬ e.IsDiag) : (graphOf s).edgeFinset = s := by
  ext e
  constructor
  · intro he
    have hmem : e ∈ (s : Set (Sym2 (Fin n))) \ {z | z.IsDiag} := by
      simpa [graphOf, mem_edgeFinset, edgeSet_fromEdgeSet] using he
    exact hmem.1
  · intro he
    have hmem : e ∈ (s : Set (Sym2 (Fin n))) \ {z | z.IsDiag} :=
      ⟨he, hs e he⟩
    simpa [graphOf, mem_edgeFinset, edgeSet_fromEdgeSet] using hmem

/-- Glue: a labelled tree on `Fin n` has `|E| = n-1`. -/
lemma labelledTree_card_edges {n : ℕ} (t : LabelledTree n) :
    t.1.card + 1 = n := by
  have hE := (isTree_of t).card_edgeFinset
  simpa [Fintype.card_fin, edgeFinset_graphOf (nodiag_of t)] using hE

/-! ## Acyclicity helpers -/

lemma isAcyclic_of_card_le_two {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hV : Fintype.card V ≤ 2) : G.IsAcyclic := by
  intro v p hp
  have hlen : 3 ≤ p.length := hp.three_le_length
  have hnil : ¬ p.Nil := hp.not_nil
  have htail : p.support.tail.length = p.length := by
    cases p with
    | nil => exact (hnil Walk.Nil.nil).elim
    | cons _ q =>
      simp [Walk.support_cons, Walk.length_cons, Walk.length_support]
  have : p.support.tail.length ≤ Fintype.card V :=
    List.Nodup.length_le_card hp.support_nodup
  omega

lemma isAcyclic_of_edgeFinset_card_le_two {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.edgeFinset.card ≤ 2) : G.IsAcyclic := by
  intro v p hp
  have hlen : 3 ≤ p.length := hp.three_le_length
  have hnodup : p.edges.Nodup := hp.toIsCircuit.toIsTrail.edges_nodup
  have hcard : p.edges.toFinset.card = p.edges.length :=
    List.toFinset_card_of_nodup hnodup
  have hlenE : p.edges.length = p.length := p.length_edges
  have hsub : p.edges.toFinset ⊆ G.edgeFinset := by
    intro e he
    exact mem_edgeFinset.mpr (p.edges_subset_edgeSet (List.mem_toFinset.mp he))
  have : p.edges.toFinset.card ≤ G.edgeFinset.card := card_le_card hsub
  omega

/-! ## Level A: n = 1 (empty / `⊥`) -/

lemma isDiag_sym2_fin_one (e : Sym2 (Fin 1)) : e.IsDiag := by
  refine e.ind (fun a b => ?_)
  simpa [Sym2.mk_isDiag_iff] using Subsingleton.elim a b

lemma isTree_bot_fin_one : (⊥ : SimpleGraph (Fin 1)).IsTree where
  isConnected := ⟨fun u v => by
    have : u = v := Subsingleton.elim u v
    subst this
    exact Reachable.refl _⟩
  IsAcyclic := isAcyclic_bot

lemma empty_nodiag_one : ∀ e ∈ (∅ : Finset (Sym2 (Fin 1))), ¬ e.IsDiag :=
  fun _ he => by cases he

def treeOne : LabelledTree 1 :=
  ⟨∅, empty_nodiag_one, by
    simpa [graphOf, fromEdgeSet_empty] using isTree_bot_fin_one⟩

lemma eq_treeOne (t : LabelledTree 1) : t = treeOne := by
  apply Subtype.ext
  ext e
  simp [treeOne]
  intro he
  exact (nodiag_of t e he) (isDiag_sym2_fin_one e)

lemma card_labelledTree_one : Fintype.card (LabelledTree 1) = 1 :=
  Fintype.card_eq_one_iff.mpr ⟨treeOne, eq_treeOne⟩

/-- Nat pin: `n = 1` gives `n - 2 = 0` and `1 ^ 0 = 1`. -/
theorem cayley_formula_one :
    Fintype.card (LabelledTree 1) = 1 ^ (1 - 2) := by
  rw [card_labelledTree_one]
  rfl

/-! ## Level A: n = 2 (`K₂`, one tree) -/

lemma eq_s01_of_nodiag {e : Sym2 (Fin 2)} (h : ¬ e.IsDiag) : e = s(0, 1) := by
  revert h
  refine e.ind (fun a b h => ?_)
  fin_cases a <;> fin_cases b <;> simp [Sym2.mk_isDiag_iff] at h ⊢

lemma isTree_k2 : (graphOf ({s(0, 1)} : Finset (Sym2 (Fin 2)))).IsTree where
  isConnected := ⟨fun u v => by
    have hadj : (graphOf ({s(0, 1)} : Finset (Sym2 (Fin 2)))).Adj 0 1 := by
      simp [graphOf, fromEdgeSet_adj]
    fin_cases u <;> fin_cases v
    · exact Reachable.refl _
    · exact hadj.reachable
    · exact hadj.symm.reachable
    · exact Reachable.refl _⟩
  IsAcyclic := isAcyclic_of_card_le_two _ (by simp [Fintype.card_fin])

def treeTwo : LabelledTree 2 :=
  ⟨{s(0, 1)},
    fun e he => by
      simp at he
      subst he
      simp [Sym2.mk_isDiag_iff],
    isTree_k2⟩

lemma eq_treeTwo (t : LabelledTree 2) : t = treeTwo := by
  apply Subtype.ext
  have hcard : t.1.card = 1 := by
    have := labelledTree_card_edges t
    omega
  have hsub : t.1 ⊆ {s(0, 1)} := by
    intro e he
    simpa using eq_s01_of_nodiag (nodiag_of t e he)
  exact eq_of_subset_of_card_le hsub (by simp [hcard, treeTwo])

lemma card_labelledTree_two : Fintype.card (LabelledTree 2) = 1 :=
  Fintype.card_eq_one_iff.mpr ⟨treeTwo, eq_treeTwo⟩

theorem cayley_formula_two :
    Fintype.card (LabelledTree 2) = 2 ^ (2 - 2) := by
  rw [card_labelledTree_two]
  rfl

/-! ## Level A: n = 3 (three labelled paths) -/

/-- The two edges incident to `i` on `Fin 3` — a path with middle `i`. -/
def starEdges (i : Fin 3) : Finset (Sym2 (Fin 3)) :=
  (univ.erase i).image fun j => s(i, j)

lemma mem_starEdges {i : Fin 3} {e : Sym2 (Fin 3)} :
    e ∈ starEdges i ↔ ∃ j : Fin 3, j ≠ i ∧ e = s(i, j) := by
  simp [starEdges, mem_image, mem_erase]
  constructor
  · rintro ⟨j, hj, h⟩
    exact ⟨j, hj, h.symm⟩
  · rintro ⟨j, hj, h⟩
    exact ⟨j, hj, h.symm⟩

lemma nodiag_starEdges (i : Fin 3) : ∀ e ∈ starEdges i, ¬ e.IsDiag := by
  intro e he
  obtain ⟨j, hji, rfl⟩ := (mem_starEdges (e := e)).mp he
  simp [Sym2.mk_isDiag_iff]
  exact Ne.symm hji

lemma card_starEdges (i : Fin 3) : (starEdges i).card = 2 := by
  refine (card_image_of_injOn ?_).trans ?_
  · intro a ha b hb h
    simp [Sym2.eq_iff] at h
    rcases h with ⟨_, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact ((mem_erase.mp ha).1 rfl).elim
  · simp [card_erase_of_mem (mem_univ i), card_univ]

lemma adj_star {i j : Fin 3} (h : j ≠ i) :
    (graphOf (starEdges i)).Adj i j := by
  rw [graphOf, fromEdgeSet_adj]
  exact ⟨mem_starEdges.mpr ⟨j, h, rfl⟩, Ne.symm h⟩

lemma reachable_eq_of {G : SimpleGraph (Fin 3)} {u v : Fin 3} (h : u = v) :
    G.Reachable u v := by
  subst h
  exact Reachable.refl _

lemma preconnected_star (i : Fin 3) : (graphOf (starEdges i)).Preconnected := by
  intro u v
  by_cases hu : u = i
  · by_cases hv : v = i
    · exact reachable_eq_of (hu.trans hv.symm)
    · exact (show (graphOf (starEdges i)).Adj u v from hu.symm ▸ adj_star hv).reachable
  · by_cases hv : v = i
    · exact (show (graphOf (starEdges i)).Adj v u from hv.symm ▸ adj_star hu).symm.reachable
    · exact ((adj_star hu).symm.reachable).trans (adj_star hv).reachable

lemma isTree_star (i : Fin 3) : (graphOf (starEdges i)).IsTree where
  isConnected := ⟨preconnected_star i⟩
  IsAcyclic := by
    have heq := edgeFinset_graphOf (nodiag_starEdges i)
    have hc := card_starEdges i
    exact isAcyclic_of_edgeFinset_card_le_two _
      (by rw [heq, hc])

def treeThree (i : Fin 3) : LabelledTree 3 :=
  ⟨starEdges i, nodiag_starEdges i, isTree_star i⟩

lemma nodiag_fin_three {e : Sym2 (Fin 3)} (h : ¬ e.IsDiag) :
    e = s(0, 1) ∨ e = s(0, 2) ∨ e = s(1, 2) := by
  revert h
  refine e.ind (fun a b h => ?_)
  fin_cases a <;> fin_cases b <;> simp [Sym2.mk_isDiag_iff] at h ⊢

lemma starEdges_zero : starEdges 0 = {s(0, 1), s(0, 2)} := by
  ext e
  constructor
  · intro he
    obtain ⟨j, hj, rfl⟩ := mem_starEdges.mp he
    fin_cases j <;> simp at hj ⊢
  · intro he
    simp only [mem_insert, mem_singleton] at he
    rcases he with rfl | rfl
    · exact mem_starEdges.mpr ⟨1, by decide, rfl⟩
    · exact mem_starEdges.mpr ⟨2, by decide, rfl⟩

lemma starEdges_one : starEdges 1 = {s(0, 1), s(1, 2)} := by
  ext e
  constructor
  · intro he
    obtain ⟨j, hj, rfl⟩ := mem_starEdges.mp he
    fin_cases j <;> simp at hj ⊢
  · intro he
    simp only [mem_insert, mem_singleton] at he
    rcases he with rfl | rfl
    · exact mem_starEdges.mpr ⟨0, by decide, Sym2.eq_swap⟩
    · exact mem_starEdges.mpr ⟨2, by decide, rfl⟩

lemma starEdges_two : starEdges 2 = {s(0, 2), s(1, 2)} := by
  ext e
  constructor
  · intro he
    obtain ⟨j, hj, rfl⟩ := mem_starEdges.mp he
    fin_cases j <;> simp at hj ⊢
  · intro he
    simp only [mem_insert, mem_singleton] at he
    rcases he with rfl | rfl
    · exact mem_starEdges.mpr ⟨0, by decide, Sym2.eq_swap⟩
    · exact mem_starEdges.mpr ⟨1, by decide, Sym2.eq_swap⟩

lemma exists_eq_treeThree (t : LabelledTree 3) : ∃ i, t = treeThree i := by
  have hcard : t.1.card = 2 := by
    have := labelledTree_card_edges t
    omega
  obtain ⟨a, b, hne, hs⟩ := card_eq_two.mp hcard
  have ha := nodiag_fin_three (nodiag_of t a (by simp [hs]))
  have hb := nodiag_fin_three (nodiag_of t b (by simp [hs]))
  have : t.1 = starEdges 0 ∨ t.1 = starEdges 1 ∨ t.1 = starEdges 2 := by
    rw [starEdges_zero, starEdges_one, starEdges_two, hs]
    rcases ha with ha' | ha' | ha' <;> rcases hb with hb' | hb' | hb'
    · exact (hne (ha'.trans hb'.symm)).elim
    · subst ha'; subst hb'; exact Or.inl rfl
    · subst ha'; subst hb'; exact Or.inr (Or.inl rfl)
    · subst ha'; subst hb'; exact Or.inl (pair_comm _ _)
    · exact (hne (ha'.trans hb'.symm)).elim
    · subst ha'; subst hb'; exact Or.inr (Or.inr rfl)
    · subst ha'; subst hb'; exact Or.inr (Or.inl (pair_comm _ _))
    · subst ha'; subst hb'; exact Or.inr (Or.inr (pair_comm _ _))
    · exact (hne (ha'.trans hb'.symm)).elim
  rcases this with h | h | h
  · exact ⟨0, Subtype.ext h⟩
  · exact ⟨1, Subtype.ext h⟩
  · exact ⟨2, Subtype.ext h⟩

lemma exists_third {i j : Fin 3} (h : i ≠ j) : ∃ k : Fin 3, k ≠ i ∧ k ≠ j := by
  fin_cases i <;> fin_cases j
  · exact (h rfl).elim
  · exact ⟨2, by decide, by decide⟩
  · exact ⟨1, by decide, by decide⟩
  · exact ⟨2, by decide, by decide⟩
  · exact (h rfl).elim
  · exact ⟨0, by decide, by decide⟩
  · exact ⟨1, by decide, by decide⟩
  · exact ⟨0, by decide, by decide⟩
  · exact (h rfl).elim

lemma treeThree_injective : Injective treeThree := by
  intro i j h
  have hij : starEdges i = starEdges j := congrArg Subtype.val h
  by_contra hne
  obtain ⟨k, hki, hkj⟩ := exists_third hne
  have hk : s(i, k) ∈ starEdges i := mem_starEdges.mpr ⟨k, hki, rfl⟩
  have hk' : s(i, k) ∈ starEdges j := hij ▸ hk
  obtain ⟨x, hxj, heq⟩ := mem_starEdges.mp hk'
  simp [Sym2.eq_iff] at heq
  rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hne rfl
  · exact hkj rfl

lemma card_labelledTree_three : Fintype.card (LabelledTree 3) = 3 := by
  refine le_antisymm ?upper ?lower
  · have hsurj : Surjective treeThree := by
      intro t
      obtain ⟨i, hi⟩ := exists_eq_treeThree t
      exact ⟨i, hi.symm⟩
    have := Fintype.card_le_of_surjective treeThree hsurj
    simpa [Fintype.card_fin] using this
  · have := Fintype.card_le_of_injective treeThree treeThree_injective
    simpa [Fintype.card_fin] using this

theorem cayley_formula_three :
    Fintype.card (LabelledTree 3) = 3 ^ (3 - 2) := by
  rw [card_labelledTree_three]
  rfl

/-! ## Level A bundled specials -/

/-- Level A cardinality for the three STATEMENT specials. Not the namesake. -/
theorem cayley_formula_of_le_three {n : ℕ} (hn : 1 ≤ n) (hle : n ≤ 3) :
    Fintype.card (LabelledTree n) = n ^ (n - 2) := by
  interval_cases n
  · exact cayley_formula_one
  · exact cayley_formula_two
  · exact cayley_formula_three

end ProofLab.CayleyTrees
