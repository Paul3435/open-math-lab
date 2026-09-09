/-
Petersen 1-factor — Level A only (empty Fin 0 / K₄ / K_{3,3}).
**Not labelled Petersen / Tutte.**

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 pin `a719ba5c3115` has `Subgraph.IsMatching` /
`IsPerfectMatching` / `IsRegularOfDegree` / `IsBridge` /
`completeGraph` / `completeBipartiteGraph` as **infra**. ZERO named
Petersen 1-factor / `petersen_one_factor` / `IsBridgeless` /
`cubic_bridgeless` under `Mathlib/` or `Archive/` or `ProofLab/`
except Moore-bound *comments* naming the Petersen graph
(`ProofLab/MooreDegreeGirth.lean` — consumed `moore`, different
object). Completing the Level A empty / K₄ / K_{3,3} glue is the
gap this ticket lands. The Level B namesake `petersen_one_factor`
(every finite cubic bridgeless graph has a perfect matching) is
**out of this ticket** and is **not** sorry-ed. Tutte / Tait /
snarks / Petersen-graph uniqueness extras are residual of this id.

Pin: `catalog/problems/petersen-1-factor/STATEMENT.md`
(OPE-1223; Scout OPE-1216 prime; Director OPE-1222). Encoding:
Mathlib `IsMatching` / `IsPerfectMatching` / `IsRegularOfDegree` /
`IsBridge` on `Fin n` / `Fin 3 ⊕ Fin 3`. Zero `sorry`. Do not
import `Archive.*`.

This is **not** Tutte (Matching.lean TODO) — a different not-one-wave
theorem; residual of this id; do **not** sorry Tutte; do **not**
take Tutte as namesake.
This is **not** Hall SDR
(`all_card_le_biUnion_card_iff_exists_injective`, Hall/Basic.lean
L116) — already Mathlib; do **not** re-prove; do **not** cite as
Petersen.
This is **not** König matching `ν=τ` (`ProofLab/Konig.lean`).
This is **not** Gale–Shapley (`ProofLab/GaleShapley.lean`, PR #126).
This is **not** the Petersen graph / Moore cage / Hoffman–Singleton
(`ProofLab/MooreDegreeGirth.lean`).
This is **not** circulant-det (`ProofLab/CirculantDet.lean`, PR #132).
This is **not** Wantzel / `IsConstructible`
(`ProofLab/WantzelConstructible.lean`, PR #133).
Do not re-prime the consumed mill. Leave OPE-403 alone.
Leave OPE-1195 alone.

v1 is cubic + bridgeless + perfect matching on named graphs:
empty `Fin 0` (vacuous), `K₄ = completeGraph (Fin 4)`, and
`K_{3,3} = completeBipartiteGraph (Fin 3) (Fin 3)`, **not**
labelled Petersen. Finite `Fin n` / `Fin 3 ⊕ Fin 3` is
load-bearing. Cubic `IsRegularOfDegree 3` is load-bearing.
Bridgeless (`¬ IsBridge`) is load-bearing. `IsPerfectMatching`
is load-bearing.

Level A: empty `Fin 0` is vacuously 3-regular and bridgeless;
the empty matching is perfect on an empty vertex set. `K₄` is
3-regular, has no bridges, and has a 1-factor (two disjoint
edges). `K_{3,3}` is 3-regular bridgeless with a 1-factor (the
matching `inl i — inr i`). **Not** labelled Petersen.

Transcribed classical argument (Petersen 1891). Compact form:
Wikipedia *Petersen's theorem* (graph theory). Type pin:
`IsRegularOfDegree 3` / `IsBridge` / `IsPerfectMatching`. Tutte
is a different not-one-wave theorem. The Petersen graph is a
different object. No novelty claim. Default no claim.
-/
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Tactic

set_option linter.unusedVariables false

open SimpleGraph

noncomputable section
open Classical

namespace ProofLab.PetersenOneFactor

/-! ## Level A: empty Fin 0 / K₄ / K_{3,3}
(not labelled Petersen / Tutte) -/

/-- No edge of `G` is a bridge. ProofLab encoding; Mathlib v4.10.0
has `IsBridge` but no `IsBridgeless`. Glue; **not** labelled
Petersen. -/
def IsBridgeless {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ e, e ∈ G.edgeSet → ¬ G.IsBridge e

/-- Empty `Fin 0` is vacuously 3-regular (no vertices).
Uses `IsRegularOfDegree`; does **not** re-prove it. Glue; **not**
labelled Petersen. -/
theorem isRegularOfDegree_bot_fin_zero :
    (⊥ : SimpleGraph (Fin 0)).IsRegularOfDegree 3 :=
  fun v => v.elim0

/-- Empty `Fin 0` is vacuously bridgeless (no edges).
Uses `edgeSet_bot` / `IsBridge`; does **not** re-prove them.
Glue; **not** labelled Petersen. -/
theorem isBridgeless_bot_fin_zero :
    IsBridgeless (⊥ : SimpleGraph (Fin 0)) := by
  intro e he
  rw [SimpleGraph.edgeSet_bot] at he
  exact he.elim

/-- Empty matching on empty `Fin 0` is perfect.
Uses `isPerfectMatching_iff`; does **not** re-prove matching.
Glue; **not** labelled Petersen. -/
theorem exists_perfectMatching_bot_fin_zero :
    ∃ M : (⊥ : SimpleGraph (Fin 0)).Subgraph, M.IsPerfectMatching :=
  ⟨⊥, (Subgraph.isPerfectMatching_iff (M := (⊥ : (⊥ : SimpleGraph (Fin 0)).Subgraph))).2
    fun v => v.elim0⟩

/-- `K₄ = completeGraph (Fin 4)` is 3-regular.
Uses `IsRegularOfDegree.top` / `complete_graph_degree`; does
**not** re-prove them. Glue; **not** labelled Petersen. -/
theorem completeGraph_fin_four_regular_three :
    (completeGraph (Fin 4)).IsRegularOfDegree 3 := by
  rw [completeGraph_eq_top]
  convert (IsRegularOfDegree.top : (⊤ : SimpleGraph (Fin 4)).IsRegularOfDegree _)

/-- A third vertex on `Fin 4`, given two distinct endpoints.
Glue for the K₄ detour; **not** labelled Petersen. -/
lemma exists_third_vertex_fin_four {v w : Fin 4} (hne : v ≠ w) :
    ∃ u : Fin 4, u ≠ v ∧ u ≠ w := by
  have hcard : ({v, w} : Finset (Fin 4)).card = 2 := by
    rw [Finset.card_insert_of_not_mem (Finset.not_mem_singleton.mpr hne),
      Finset.card_singleton]
  have : ∃ u, u ∉ ({v, w} : Finset (Fin 4)) := by
    by_contra! h
    have heq : ({v, w} : Finset (Fin 4)) = Finset.univ :=
      Finset.eq_univ_iff_forall.mpr h
    have h24 : (2 : ℕ) = 4 := by
      rw [← hcard, heq, Finset.card_univ, Fintype.card_fin]
    exact (by decide : (2 : ℕ) ≠ 4) h24
  obtain ⟨u, hu⟩ := this
  refine ⟨u, ?_⟩
  simpa [Finset.mem_insert, Finset.mem_singleton, not_or] using hu

/-- `K₄` has no bridges: any edge has a length-2 detour through a
third vertex. Uses `IsBridge` / `isBridge_iff_adj_and_forall_walk_mem_edges`;
does **not** re-prove them. Glue; **not** labelled Petersen. -/
theorem completeGraph_fin_four_bridgeless :
    IsBridgeless (completeGraph (Fin 4)) := by
  intro e he hb
  revert hb
  refine Sym2.inductionOn e fun v w => ?_
  intro hb
  rw [isBridge_iff_adj_and_forall_walk_mem_edges] at hb
  obtain ⟨hadj, hwalk⟩ := hb
  have hne : v ≠ w := hadj.ne
  obtain ⟨u, huv, huw⟩ := exists_third_vertex_fin_four hne
  have hvu : (completeGraph (Fin 4)).Adj v u := by
    rw [completeGraph_eq_top, SimpleGraph.top_adj]; exact Ne.symm huv
  have huw' : (completeGraph (Fin 4)).Adj u w := by
    rw [completeGraph_eq_top, SimpleGraph.top_adj]; exact huw
  have hmem := hwalk (Walk.cons hvu (Walk.cons huw' Walk.nil))
  simp only [Walk.edges_cons, Walk.edges_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hmem
  rcases hmem with h | h
  · rcases (Sym2.eq_iff).mp h with ⟨_, rfl⟩ | ⟨rfl, rfl⟩
    · exact huw rfl
    · exact hne rfl
  · rcases (Sym2.eq_iff).mp h with ⟨rfl, _⟩ | ⟨rfl, rfl⟩
    · exact huv rfl
    · exact hne rfl

/-- Adjacency `0—1` in `K₄`. Glue; **not** labelled Petersen. -/
lemma completeGraph_fin_four_adj_zero_one :
    (completeGraph (Fin 4)).Adj 0 1 := by
  rw [completeGraph_eq_top, SimpleGraph.top_adj]; decide

/-- Adjacency `2—3` in `K₄`. Glue; **not** labelled Petersen. -/
lemma completeGraph_fin_four_adj_two_three :
    (completeGraph (Fin 4)).Adj 2 3 := by
  rw [completeGraph_eq_top, SimpleGraph.top_adj]; decide

/-- `K₄` has a 1-factor `{0—1, 2—3}`. Uses `IsMatching.subgraphOfAdj` /
`IsMatching.sup` / `IsPerfectMatching`; does **not** re-prove
matching. Glue; **not** labelled Petersen. -/
theorem completeGraph_fin_four_exists_perfectMatching :
    ∃ M : (completeGraph (Fin 4)).Subgraph, M.IsPerfectMatching := by
  let G := completeGraph (Fin 4)
  let M1 := G.subgraphOfAdj completeGraph_fin_four_adj_zero_one
  let M2 := G.subgraphOfAdj completeGraph_fin_four_adj_two_three
  refine ⟨M1 ⊔ M2, ?_⟩
  constructor
  · refine Subgraph.IsMatching.sup (Subgraph.IsMatching.subgraphOfAdj _)
      (Subgraph.IsMatching.subgraphOfAdj _) ?_
    rw [(Subgraph.IsMatching.subgraphOfAdj
          completeGraph_fin_four_adj_zero_one).support_eq_verts,
      (Subgraph.IsMatching.subgraphOfAdj
          completeGraph_fin_four_adj_two_three).support_eq_verts,
      subgraphOfAdj_verts, subgraphOfAdj_verts]
    rw [Set.disjoint_iff]
    intro x
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_empty_iff_false, and_imp]
    rintro (rfl | rfl) h
    · rcases h with h | h <;> cases h
    · rcases h with h | h <;> cases h
  · intro v
    change v ∈ (M1 ⊔ M2).verts
    simp only [M1, M2, Subgraph.verts_sup, subgraphOfAdj_verts, Set.mem_union,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    fin_cases v <;> simp

/-- Left vertex of `K_{3,3}` has degree 3. Uses `IsRegularOfDegree` /
`neighborFinset`; does **not** re-prove them. Glue; **not** labelled
Petersen. -/
lemma completeBipartite_fin_three_degree_inl (i : Fin 3) :
    (completeBipartiteGraph (Fin 3) (Fin 3)).degree (Sum.inl i) = 3 := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
  have h :
      (Finset.univ.filter fun w : Fin 3 ⊕ Fin 3 =>
          (completeBipartiteGraph (Fin 3) (Fin 3)).Adj (Sum.inl i) w) =
        (Finset.univ : Finset (Fin 3)).map ⟨Sum.inr, Sum.inr_injective⟩ := by
    ext w
    constructor
    · intro hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      cases w with
      | inl _ =>
        simp [completeBipartiteGraph] at hw
      | inr j =>
        exact Finset.mem_map.2 ⟨j, Finset.mem_univ _, rfl⟩
    · intro hw
      obtain ⟨j, _, rfl⟩ := Finset.mem_map.1 hw
      simp [completeBipartiteGraph]
  rw [h, Finset.card_map, Finset.card_univ, Fintype.card_fin]

/-- Right vertex of `K_{3,3}` has degree 3. Glue; **not** labelled
Petersen. -/
lemma completeBipartite_fin_three_degree_inr (j : Fin 3) :
    (completeBipartiteGraph (Fin 3) (Fin 3)).degree (Sum.inr j) = 3 := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
  have h :
      (Finset.univ.filter fun w : Fin 3 ⊕ Fin 3 =>
          (completeBipartiteGraph (Fin 3) (Fin 3)).Adj (Sum.inr j) w) =
        (Finset.univ : Finset (Fin 3)).map ⟨Sum.inl, Sum.inl_injective⟩ := by
    ext w
    constructor
    · intro hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      cases w with
      | inl i =>
        exact Finset.mem_map.2 ⟨i, Finset.mem_univ _, rfl⟩
      | inr _ =>
        simp [completeBipartiteGraph] at hw
    · intro hw
      obtain ⟨i, _, rfl⟩ := Finset.mem_map.1 hw
      simp [completeBipartiteGraph]
  rw [h, Finset.card_map, Finset.card_univ, Fintype.card_fin]

/-- `K_{3,3}` is 3-regular. Glue; **not** labelled Petersen. -/
theorem completeBipartite_fin_three_regular_three :
    (completeBipartiteGraph (Fin 3) (Fin 3)).IsRegularOfDegree 3 := by
  intro v
  cases v with
  | inl i => exact completeBipartite_fin_three_degree_inl i
  | inr j => exact completeBipartite_fin_three_degree_inr j

/-- Some other index in `Fin 3`. Glue; **not** labelled Petersen. -/
lemma exists_ne_fin_three (i : Fin 3) : ∃ j : Fin 3, j ≠ i := by
  refine ⟨i + 1, ?_⟩
  intro h
  have : (1 : Fin 3) = 0 := by
    simpa using congrArg (fun x : Fin 3 => x - i) h
  exact zero_ne_one this.symm

/-- Length-3 detour in `K_{3,3}` around a left–right edge.
Glue; **not** labelled Petersen. -/
lemma completeBipartite_fin_three_detour_inl_inr (a b : Fin 3) :
    ∃ p : (completeBipartiteGraph (Fin 3) (Fin 3)).Walk
      (Sum.inl a) (Sum.inr b),
      s(Sum.inl a, Sum.inr b) ∉ p.edges := by
  obtain ⟨a', ha'⟩ := exists_ne_fin_three a
  obtain ⟨b', hb'⟩ := exists_ne_fin_three b
  have h1 : (completeBipartiteGraph (Fin 3) (Fin 3)).Adj
      (Sum.inl a) (Sum.inr b') := by simp [completeBipartiteGraph]
  have h2 : (completeBipartiteGraph (Fin 3) (Fin 3)).Adj
      (Sum.inr b') (Sum.inl a') := by simp [completeBipartiteGraph]
  have h3 : (completeBipartiteGraph (Fin 3) (Fin 3)).Adj
      (Sum.inl a') (Sum.inr b) := by simp [completeBipartiteGraph]
  refine ⟨Walk.cons h1 (Walk.cons h2 (Walk.cons h3 Walk.nil)), ?_⟩
  simp only [Walk.edges_cons, Walk.edges_nil, List.mem_cons, List.not_mem_nil,
    or_false]
  intro h
  rcases h with h | h | h
  · rcases (Sym2.eq_iff).mp h with ⟨hL, hR⟩ | ⟨hL, _⟩
    · exact hb' (Sum.inr.inj hR).symm
    · cases hL
  · rcases (Sym2.eq_iff).mp h with ⟨hL, _⟩ | ⟨hL, _⟩
    · cases hL
    · exact ha' (Sum.inl.inj hL).symm
  · rcases (Sym2.eq_iff).mp h with ⟨hL, _⟩ | ⟨hL, _⟩
    · exact ha' (Sum.inl.inj hL).symm
    · cases hL

/-- Length-3 detour in `K_{3,3}` around a right–left edge.
Glue; **not** labelled Petersen. -/
lemma completeBipartite_fin_three_detour_inr_inl (a b : Fin 3) :
    ∃ p : (completeBipartiteGraph (Fin 3) (Fin 3)).Walk
      (Sum.inr a) (Sum.inl b),
      s(Sum.inr a, Sum.inl b) ∉ p.edges := by
  obtain ⟨a', ha'⟩ := exists_ne_fin_three a
  obtain ⟨b', hb'⟩ := exists_ne_fin_three b
  have h1 : (completeBipartiteGraph (Fin 3) (Fin 3)).Adj
      (Sum.inr a) (Sum.inl b') := by simp [completeBipartiteGraph]
  have h2 : (completeBipartiteGraph (Fin 3) (Fin 3)).Adj
      (Sum.inl b') (Sum.inr a') := by simp [completeBipartiteGraph]
  have h3 : (completeBipartiteGraph (Fin 3) (Fin 3)).Adj
      (Sum.inr a') (Sum.inl b) := by simp [completeBipartiteGraph]
  refine ⟨Walk.cons h1 (Walk.cons h2 (Walk.cons h3 Walk.nil)), ?_⟩
  simp only [Walk.edges_cons, Walk.edges_nil, List.mem_cons, List.not_mem_nil,
    or_false]
  intro h
  rcases h with h | h | h
  · rcases (Sym2.eq_iff).mp h with ⟨hL, hR⟩ | ⟨hL, _⟩
    · exact hb' (Sum.inl.inj hR).symm
    · cases hL
  · rcases (Sym2.eq_iff).mp h with ⟨hL, _⟩ | ⟨hL, _⟩
    · cases hL
    · exact ha' (Sum.inr.inj hL).symm
  · rcases (Sym2.eq_iff).mp h with ⟨hL, _⟩ | ⟨hL, _⟩
    · exact ha' (Sum.inr.inj hL).symm
    · cases hL

/-- `K_{3,3}` has no bridges. Uses `IsBridge`; does **not** re-prove
it. Glue; **not** labelled Petersen. -/
theorem completeBipartite_fin_three_bridgeless :
    IsBridgeless (completeBipartiteGraph (Fin 3) (Fin 3)) := by
  intro e he hb
  revert hb
  refine Sym2.inductionOn e fun v w => ?_
  intro hb
  rw [isBridge_iff_adj_and_forall_walk_mem_edges] at hb
  obtain ⟨hadj, hwalk⟩ := hb
  cases v with
  | inl a =>
    cases w with
    | inl _ =>
      simp [completeBipartiteGraph] at hadj
    | inr b =>
      obtain ⟨p, hp⟩ := completeBipartite_fin_three_detour_inl_inr a b
      exact hp (hwalk p)
  | inr a =>
    cases w with
    | inl b =>
      obtain ⟨p, hp⟩ := completeBipartite_fin_three_detour_inr_inl a b
      exact hp (hwalk p)
    | inr _ =>
      simp [completeBipartiteGraph] at hadj

/-- Matching edge `inl i — inr i` in `K_{3,3}`. Glue; **not**
labelled Petersen. -/
lemma completeBipartite_fin_three_adj_diag (i : Fin 3) :
    (completeBipartiteGraph (Fin 3) (Fin 3)).Adj (Sum.inl i) (Sum.inr i) := by
  simp [completeBipartiteGraph]

/-- `K_{3,3}` has a 1-factor `{inl i — inr i | i : Fin 3}`.
Uses `IsMatching.iSup` / `IsMatching.subgraphOfAdj`; does **not**
re-prove matching. Glue; **not** labelled Petersen. -/
theorem completeBipartite_fin_three_exists_perfectMatching :
    ∃ M : (completeBipartiteGraph (Fin 3) (Fin 3)).Subgraph,
      M.IsPerfectMatching := by
  let G := completeBipartiteGraph (Fin 3) (Fin 3)
  let f : Fin 3 → G.Subgraph :=
    fun i => G.subgraphOfAdj (completeBipartite_fin_three_adj_diag i)
  refine ⟨⨆ i, f i, ?_⟩
  constructor
  · refine Subgraph.IsMatching.iSup (fun i => Subgraph.IsMatching.subgraphOfAdj _) ?_
    intro i j hij
    rw [(Subgraph.IsMatching.subgraphOfAdj
          (completeBipartite_fin_three_adj_diag i)).support_eq_verts,
      (Subgraph.IsMatching.subgraphOfAdj
          (completeBipartite_fin_three_adj_diag j)).support_eq_verts,
      subgraphOfAdj_verts, subgraphOfAdj_verts]
    rw [Set.disjoint_left]
    intro x hx1 hx2
    have hx1' : x = Sum.inl i ∨ x = Sum.inr i := by
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hx1
    have hx2' : x = Sum.inl j ∨ x = Sum.inr j := by
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hx2
    rcases hx1' with h1 | h1 <;> rcases hx2' with h2 | h2
    · exact hij (Sum.inl.inj (h1.symm.trans h2))
    · cases h1.symm.trans h2
    · cases h1.symm.trans h2
    · exact hij (Sum.inr.inj (h1.symm.trans h2))
  · intro v
    simp only [f, Subgraph.verts_iSup, Set.mem_iUnion, subgraphOfAdj_verts,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    cases v with
    | inl i => exact ⟨i, Or.inl rfl⟩
    | inr i => exact ⟨i, Or.inr rfl⟩

/- Residual of this id (comment, **not** `sorry`):
Level B namesake `petersen_one_factor` — every finite cubic
bridgeless simple graph has a perfect matching. Tutte 1-factor
criterion / Tait colouring / snarks / 4-colour / Petersen-graph
uniqueness / Moore cages / Vizing / 1-factorization of `K_{2n}`
are residual, not extra namesakes. Out of this ticket. Do **not**
prove Hall SDR / König matching / gale_shapley / Wantzel /
circulant-det. -/

end ProofLab.PetersenOneFactor
