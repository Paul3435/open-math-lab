/-
Greedy colouring: every finite simple graph is (Δ+1)-colourable.

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 has `Colorable` / `Coloring` / `chromaticNumber` /
`maxDegree` but no `Colorable (maxDegree + 1)` and no Brooks.

Pin: `catalog/problems/greedy-chromatic/STATEMENT.md` (OPE-645).
Encoding: Mathlib `Coloring.mk` on `Fin (G.maxDegree + 1)`.
Zero `sorry`. Do not import `Archive.*`.
This is **not** Brooks (`χ ≤ Δ` except `⊤` and odd cycles).
This is **not** Vizing (edge-chromatic). This is **not** 4CT/5CT.

Level A: empty / edgeless / complete / `card = 1` + `degree_le_maxDegree`.
Level B: namesake `greedy_colorable` by induction on `Fintype.card V`
(delete a vertex; ≤Δ neighbours leave one colour). Any order;
Welsh–Powell is not the theorem.
-/
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Tactic

open Finset Function SimpleGraph

noncomputable section

namespace ProofLab.GreedyChromatic

section LevelA

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## Degree glue -/

lemma degree_le_maxDegree_succ (v : V) :
    G.degree v + 1 ≤ G.maxDegree + 1 :=
  Nat.succ_le_succ (G.degree_le_maxDegree v)

lemma maxDegree_bot : (⊥ : SimpleGraph V).maxDegree = 0 := by
  refine le_antisymm ?_ (Nat.zero_le _)
  exact (⊥ : SimpleGraph V).maxDegree_le_of_forall_degree_le 0 fun v =>
    (bot_degree v).le

lemma maxDegree_top [Nonempty V] :
    (⊤ : SimpleGraph V).maxDegree = Fintype.card V - 1 := by
  obtain ⟨v, hv⟩ := (⊤ : SimpleGraph V).exists_maximal_degree_vertex
  rw [hv, complete_graph_degree]

/-! ## Level A specials -/

/-- Empty vertex type: `Colorable (maxDegree + 1)` (also `Colorable 0`). -/
lemma greedy_colorable_of_isEmpty [IsEmpty V] :
    G.Colorable (G.maxDegree + 1) :=
  colorable_of_isEmpty _ _

lemma colorable_zero_of_isEmpty [IsEmpty V] : G.Colorable 0 :=
  colorable_of_isEmpty _ _

/-- Edgeless graph: `maxDegree = 0`, hence `Colorable 1`. -/
lemma greedy_colorable_bot :
    (⊥ : SimpleGraph V).Colorable ((⊥ : SimpleGraph V).maxDegree + 1) := by
  rw [maxDegree_bot]
  refine ⟨Coloring.mk (fun _ => 0) ?_⟩
  intro v w h
  exact (bot_adj v w).mp h |>.elim

/-- One vertex: no edges, `Colorable (maxDegree + 1)`. -/
lemma greedy_colorable_card_one (h : Fintype.card V = 1) :
    G.Colorable (G.maxDegree + 1) :=
  Colorable.mono (by
    rw [h]
    exact Nat.succ_le_succ (Nat.zero_le _)) G.colorable_of_fintype

/-- Complete graph: reuse `colorable_of_fintype` + degree of `⊤`. -/
lemma greedy_colorable_top :
    (⊤ : SimpleGraph V).Colorable ((⊤ : SimpleGraph V).maxDegree + 1) := by
  by_cases hV : Nonempty V
  · haveI := hV
    have hΔ : (⊤ : SimpleGraph V).maxDegree = Fintype.card V - 1 := maxDegree_top
    have hc := (⊤ : SimpleGraph V).colorable_of_fintype
    convert hc
    rw [hΔ]
    exact Nat.sub_add_cancel Fintype.card_pos
  · haveI : IsEmpty V := not_nonempty_iff.mp hV
    exact colorable_of_isEmpty _ _

/-- Stretch tightness on nonempty complete graphs: `χ = Δ+1`. Not Brooks. -/
lemma chromaticNumber_top_eq_maxDegree_add_one [Nonempty V] :
    (⊤ : SimpleGraph V).chromaticNumber =
      ((⊤ : SimpleGraph V).maxDegree + 1 : ℕ) := by
  rw [chromaticNumber_top, maxDegree_top]
  norm_cast
  exact (Nat.sub_add_cancel Fintype.card_pos).symm

/-! ## Induced-subgraph degree bound -/

lemma degree_induce_le {s : Set V} [DecidablePred (· ∈ s)] (w : s) :
    (G.induce s).degree w ≤ G.degree (w : V) := by
  let f : s ↪ V := Embedding.subtype s
  have hsub :
      ((G.induce s).neighborFinset w).map f ⊆ G.neighborFinset (w : V) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
    rw [mem_neighborFinset] at hy ⊢
    exact hy
  rw [degree, degree, ← card_map f]
  exact card_le_card hsub

lemma maxDegree_induce_le (s : Set V) [DecidablePred (· ∈ s)] :
    (G.induce s).maxDegree ≤ G.maxDegree := by
  exact (G.induce s).maxDegree_le_of_forall_degree_le G.maxDegree fun w =>
    (degree_induce_le w).trans (G.degree_le_maxDegree (w : V))

lemma card_induce_erase (v : V) :
    Fintype.card ({x | x ≠ v} : Set V) = Fintype.card V - 1 := by
  rw [Fintype.card_subtype]
  have hfilter :
      (univ.filter fun x : V => x ∈ ({x | x ≠ v} : Set V)) = univ.erase v := by
    ext x
    simp [mem_filter, mem_erase]
  rw [hfilter, card_erase_of_mem (mem_univ v), card_univ]

/-! ## Colouring extension across a deleted vertex -/

/-- Neighbours of `v` use at most `degree v ≤ Δ` colours in `Fin (Δ+1)`. -/
lemma colorable_extend_deleted {v : V}
    (h : (G.induce {x | x ≠ v}).Colorable (G.maxDegree + 1)) :
    G.Colorable (G.maxDegree + 1) := by
  obtain ⟨c⟩ := h
  let used : Finset (Fin (G.maxDegree + 1)) :=
    (G.neighborFinset v).attach.image fun ⟨w, hw⟩ =>
      c ⟨w, (G.ne_of_adj ((mem_neighborFinset G v w).mp hw)).symm⟩
  have hused : used.card ≤ G.degree v := by
    have hle : used.card ≤ (G.neighborFinset v).attach.card := card_image_le
    have hdeg : (G.neighborFinset v).attach.card = G.degree v := by
      rw [card_attach, degree]
    exact hle.trans hdeg.le
  have hex : ∃ col : Fin (G.maxDegree + 1), col ∉ used := by
    have hlt : used.card < Fintype.card (Fin (G.maxDegree + 1)) := by
      rw [Fintype.card_fin]
      have := G.degree_le_maxDegree v
      omega
    by_contra hnone
    push_neg at hnone
    have : used = univ := eq_univ_iff_forall.mpr hnone
    rw [this, card_univ] at hlt
    exact (lt_irrefl _ hlt)
  obtain ⟨col, hcol⟩ := hex
  let color : V → Fin (G.maxDegree + 1) := fun x =>
    if hx : x = v then col else c ⟨x, hx⟩
  refine ⟨Coloring.mk color ?_⟩
  intro x y hxy
  dsimp [color]
  split_ifs with hx hy hy
  · exact (G.ne_of_adj hxy (hx.trans hy.symm)).elim
  · intro hceq
    apply hcol
    have hadj : G.Adj v y := by rwa [hx] at hxy
    rw [hceq]
    exact mem_image.mpr
      ⟨⟨y, (mem_neighborFinset G v y).mpr hadj⟩, mem_attach _ _, rfl⟩
  · intro hceq
    apply hcol
    have hadj : G.Adj v x := by
      rw [hy] at hxy
      exact hxy.symm
    rw [← hceq]
    exact mem_image.mpr
      ⟨⟨x, (mem_neighborFinset G v x).mpr hadj⟩, mem_attach _ _, rfl⟩
  · exact c.valid hxy

end LevelA

/-! ## Level B: namesake greedy bound -/

lemma greedy_colorable_of_card_le :
    ∀ (k : ℕ) (V : Type*) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      Fintype.card V ≤ k → G.Colorable (G.maxDegree + 1) := by
  intro k
  induction k with
  | zero =>
    intro V _ _ G _ hle
    have h0 : Fintype.card V = 0 := Nat.eq_zero_of_le_zero hle
    haveI : IsEmpty V := Fintype.card_eq_zero_iff.mp h0
    exact colorable_of_isEmpty _ _
  | succ k ih =>
    intro V _ _ G _ hle
    by_cases hV : Nonempty V
    · obtain ⟨v⟩ := hV
      let s : Set V := {x | x ≠ v}
      let G' : SimpleGraph s := G.induce s
      have hle' : Fintype.card s ≤ k := by
        rw [card_induce_erase v]
        omega
      have ih' : G'.Colorable (G'.maxDegree + 1) := ih s G' hle'
      have hmono : G'.Colorable (G.maxDegree + 1) :=
        Colorable.mono (Nat.succ_le_succ (maxDegree_induce_le s)) ih'
      exact colorable_extend_deleted hmono
    · haveI : IsEmpty V := not_nonempty_iff.mp hV
      exact colorable_of_isEmpty _ _

section Namesake

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Every finite simple graph is `(Δ+1)`-colourable. Folklore / Diestel;
not Brooks. -/
theorem greedy_colorable : G.Colorable (G.maxDegree + 1) :=
  greedy_colorable_of_card_le (Fintype.card V) V G le_rfl

/-- Same bound on the `ℕ∞` chromatic number (not a second namesake theorem). -/
lemma chromaticNumber_le_maxDegree_add_one :
    G.chromaticNumber ≤ G.maxDegree + 1 :=
  greedy_colorable.chromaticNumber_le

end Namesake

end ProofLab.GreedyChromatic
