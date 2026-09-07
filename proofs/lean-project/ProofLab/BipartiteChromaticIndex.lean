/-
König 1916 line-colouring — Level A only (EdgeColorable encoding;
matching-is-1 / star-is-Δ / trivial Δ ≤ χ' glue). **Not labelled König.**

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 has `Colorable` / `maxDegree` / `Subgraph.IsMatching`
and ZERO `EdgeColorable` / `chromaticIndex` / Vizing. Completing the
Level A encoding + matching/star/Δ≤χ' glue is the gap this ticket lands.
The Level B namesake `konig_edge_chromatic`
(`Colorable 2 → EdgeColorable maxDegree`, missing-colour alternating
path) is **out of this ticket** and is **not** sorry-ed. Vizing /
list-edge-colouring / class 2 graphs are residual.

Pin: `catalog/problems/bipartite-chromatic-index/STATEMENT.md`
(OPE-1105; Scout OPE-1095 leftover; Director OPE-1104). Encoding:
ProofLab `EdgeColorable` on `G.edgeSet`. Zero `sorry`. Do not import
`Archive.*`.

This is **not** König matching `ν = τ` (`ProofLab/Konig.lean`
`konig_bipartite`, PRs #48+#50) — min-max ≠ chromatic index; **USE
matching infra**, **do not re-prove `konig_bipartite`**, do not revive
König matching. This is **not** Vizing (`χ' ∈ {Δ, Δ+1}`). This is
**not** Hall / Tutte / greedy / Brooks / ore-hamiltonian Level B /
AES Level B / ostrowski-q Level B / frobenius-real-division Level B /
noether-normalization Level B / krenn-gu / hou-zeng-pfc / sun-135.
Do not re-prime the consumed mill. Leave OPE-403 alone.

v1 is the bipartite `χ' = Δ` theorem only. **Do not label any theorem
König.** `Colorable 2` is **not** required on the Level A encoding
(matching/star/Δ≤χ' glue is graph-general); it **is** load-bearing
for the Level B namesake (`C₅` landmine: odd cycles have `χ' = Δ+1`).
`Fintype V` and `DecidableRel G.Adj` are load-bearing (`maxDegree` /
`edgeSet`).

Level A: encode a proper edge-colouring as a map on `edgeSet` that
separates edges sharing a vertex. A matching uses 1 colour. A star
uses Δ colours. Any proper colouring needs ≥ Δ colours. **Not**
labelled König.

Transcribed classical argument (D. König, Math. Ann. 77 (1916)
453–465; Diestel bipartite edge-colouring). Compact form: Wikipedia
*König's theorem (graph theory)* — the **line-colouring** form, **not**
the matching min-max. König matching is a different consumed theorem,
not this claim.
-/
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

open Finset Function SimpleGraph

noncomputable section
open Classical

namespace ProofLab.BipartiteChromaticIndex

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## Level A encoding (not labelled König) -/

/-- A proper edge-colouring with `n` colours: incident edges get
distinct colours. One new encoding; Mathlib v4.10.0 has no
`EdgeColorable` / chromatic index. Not labelled König. -/
def EdgeColorable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ) : Prop :=
  ∃ f : G.edgeSet → Fin n,
    ∀ ⦃e₁ e₂ : G.edgeSet⦄, e₁ ≠ e₂ →
      (∃ v, v ∈ (e₁ : Sym2 V) ∧ v ∈ (e₂ : Sym2 V)) →
        f e₁ ≠ f e₂

/-- All edges are incident to `c` (a star centred at `c`, possibly with
isolated vertices). Not labelled König. -/
def IsStarAt (G : SimpleGraph V) (c : V) : Prop :=
  ∀ ⦃u v : V⦄, G.Adj u v → u = c ∨ v = c

/-! ## Incidence glue -/

lemma mem_incidenceSet_of_isStarAt {c : V} (hstar : IsStarAt G c) {e : Sym2 V}
    (he : e ∈ G.edgeSet) : c ∈ e := by
  refine Sym2.ind (fun u v h => ?_) e he
  have hadj : G.Adj u v := h
  rcases hstar hadj with rfl | rfl
  · exact Sym2.mem_mk_left _ _
  · exact Sym2.mem_mk_right _ _

lemma edgeSet_eq_incidenceSet_of_isStarAt {c : V} (hstar : IsStarAt G c) :
    G.edgeSet = G.incidenceSet c := by
  ext e
  constructor
  · intro he
    exact ⟨he, mem_incidenceSet_of_isStarAt hstar he⟩
  · intro h
    exact h.1

lemma card_edgeSet_eq_degree_of_isStarAt {c : V} (hstar : IsStarAt G c) :
    Fintype.card G.edgeSet = G.degree c := by
  have heq : G.edgeSet = G.incidenceSet c :=
    edgeSet_eq_incidenceSet_of_isStarAt hstar
  have hcard := Fintype.card_congr (Equiv.setCongr heq)
  rwa [G.card_incidenceSet_eq_degree] at hcard

lemma two_le_degree_of_distinct_incident {e₁ e₂ : G.edgeSet} {v : V}
    (hne : e₁ ≠ e₂) (h1 : v ∈ (e₁ : Sym2 V)) (h2 : v ∈ (e₂ : Sym2 V)) :
    2 ≤ G.degree v := by
  have hne' : (e₁ : Sym2 V) ≠ (e₂ : Sym2 V) :=
    Subtype.coe_injective.ne hne
  have hsub : ({(e₁ : Sym2 V), (e₂ : Sym2 V)} : Finset (Sym2 V)) ⊆
      G.incidenceFinset v := by
    intro e he
    simp only [mem_insert, mem_singleton] at he
    rw [mem_incidenceFinset]
    rcases he with rfl | rfl
    · exact ⟨e₁.property, h1⟩
    · exact ⟨e₂.property, h2⟩
  have hcard : ({(e₁ : Sym2 V), (e₂ : Sym2 V)} : Finset (Sym2 V)).card = 2 :=
    card_pair hne'
  have : 2 ≤ (G.incidenceFinset v).card := hcard ▸ card_le_card hsub
  rwa [card_incidenceFinset_eq_degree] at this

/-! ## Level A: a matching is `EdgeColorable 1` -/

/-- Distinct edges in a degree-at-most-one graph cannot share a vertex. -/
lemma not_adjacent_edges_of_degree_le_one (hΔ : ∀ x, G.degree x ≤ 1)
    {e₁ e₂ : G.edgeSet} (hne : e₁ ≠ e₂) (v : V)
    (h1 : v ∈ (e₁ : Sym2 V)) (h2 : v ∈ (e₂ : Sym2 V)) : False := by
  have := two_le_degree_of_distinct_incident (G := G) hne h1 h2
  have := hΔ v
  omega

/-- Degree-at-most-one graphs are 1-edge-colourable (constant colour).
Graph-general matching glue. Not labelled König. -/
theorem edgeColorable_one_of_degree_le_one (hΔ : ∀ v, G.degree v ≤ 1) :
    EdgeColorable G 1 := by
  refine ⟨fun _ => 0, ?_⟩
  intro e₁ e₂ hne ⟨v, h1, h2⟩
  exact (not_adjacent_edges_of_degree_le_one hΔ hne v h1 h2).elim

lemma spanningCoe_degree_eq_zero_of_not_mem_verts {M : Subgraph G}
    [DecidableRel M.Adj] {v : V} (hv : v ∉ M.verts) :
    M.spanningCoe.degree v = 0 := by
  rw [← card_neighborFinset_eq_degree]
  have hempty : M.spanningCoe.neighborFinset v = ∅ := by
    ext w
    simp only [mem_neighborFinset, not_mem_empty, iff_false]
    intro hadj
    exact hv (M.edge_vert hadj)
  simp [hempty]

/-- Matching infra (Mathlib `IsMatching`): every vertex of the spanning
coe has degree ≤ 1. Not a re-proof of `konig_bipartite`. -/
theorem spanningCoe_degree_le_one_of_isMatching {M : Subgraph G}
    [DecidableRel M.Adj] (hM : M.IsMatching) (v : V) :
    M.spanningCoe.degree v ≤ 1 := by
  by_cases hv : v ∈ M.verts
  · have hdeg : M.degree v = 1 :=
     (Subgraph.isMatching_iff_forall_degree.mp hM) v hv
    have hcoe : M.spanningCoe.degree v = M.degree v :=
      Subgraph.degree_spanningCoe v
    omega
  · have := spanningCoe_degree_eq_zero_of_not_mem_verts (M := M) hv
    omega

/-- A matching, as a spanning subgraph (isolates allowed), is
1-edge-colourable. Uses Mathlib `IsMatching`; does **not** re-prove
`konig_bipartite`. Not labelled König. -/
theorem matching_spanningCoe_edgeColorable_one {M : Subgraph G}
    [DecidableRel M.Adj] (hM : M.IsMatching) :
    EdgeColorable M.spanningCoe 1 :=
  edgeColorable_one_of_degree_le_one
    (spanningCoe_degree_le_one_of_isMatching hM)

/-! ## Level A: a star is `EdgeColorable Δ` -/

lemma card_edgeSet_le_maxDegree_of_isStarAt {c : V} (hstar : IsStarAt G c) :
    Fintype.card G.edgeSet ≤ G.maxDegree := by
  rw [card_edgeSet_eq_degree_of_isStarAt hstar]
  exact G.degree_le_maxDegree c

/-- A star centred at `c` is `maxDegree`-edge-colourable: all edges
touch `c`, there are `deg c ≤ Δ` of them, and they inject into
`Fin Δ`. Not labelled König. -/
theorem star_edgeColorable_maxDegree {c : V} (hstar : IsStarAt G c) :
    EdgeColorable G G.maxDegree := by
  have hle : Fintype.card G.edgeSet ≤ G.maxDegree :=
    card_edgeSet_le_maxDegree_of_isStarAt hstar
  let f : G.edgeSet → Fin G.maxDegree :=
    Fin.castLE hle ∘ Fintype.equivFin G.edgeSet
  refine ⟨f, ?_⟩
  intro e₁ e₂ hne _hinc
  have hinj : Injective f :=
    (Fin.castLE_injective hle).comp (Fintype.equivFin G.edgeSet).injective
  exact hinj.ne hne

/-! ## Level A: trivial `Δ ≤ χ'` -/

lemma coloring_inj_on_incidence {n : ℕ} {f : G.edgeSet → Fin n}
    (hf : ∀ ⦃e₁ e₂ : G.edgeSet⦄, e₁ ≠ e₂ →
      (∃ v, v ∈ (e₁ : Sym2 V) ∧ v ∈ (e₂ : Sym2 V)) → f e₁ ≠ f e₂)
    (v : V) :
    Injective (fun e : G.incidenceSet v => f ⟨e.1, e.2.1⟩) := by
  intro e₁ e₂ hfeq
  apply Subtype.ext
  by_contra hne_val
  let ε₁ : G.edgeSet := ⟨e₁.val, e₁.property.1⟩
  let ε₂ : G.edgeSet := ⟨e₂.val, e₂.property.1⟩
  have hne : ε₁ ≠ ε₂ := by
    intro h
    exact hne_val (congrArg (fun e : G.edgeSet => e.val) h)
  have : f ε₁ ≠ f ε₂ := hf hne ⟨v, e₁.property.2, e₂.property.2⟩
  exact this hfeq

/-- Any proper edge-colouring uses at least `maxDegree` colours
(incident edges at a Δ-vertex are pairwise adjacent). Graph-general.
Not labelled König. -/
theorem maxDegree_le_of_edgeColorable {n : ℕ} (hc : EdgeColorable G n) :
    G.maxDegree ≤ n := by
  obtain ⟨f, hf⟩ := hc
  by_cases hV : Nonempty V
  · haveI := hV
    obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
    have hinj := coloring_inj_on_incidence (G := G) hf v
    have hcard :
        Fintype.card (G.incidenceSet v) ≤ Fintype.card (Fin n) :=
      Fintype.card_le_of_injective _ hinj
    have : G.degree v ≤ n := by
      simpa [G.card_incidenceSet_eq_degree, Fintype.card_fin] using hcard
    rw [hv]
    exact this
  · exact G.maxDegree_le_of_forall_degree_le n fun v => (hV ⟨v⟩).elim

/-
Residual / out of this ticket (comment, **not** `sorry`):

Level B namesake `konig_edge_chromatic`: under `G.Colorable 2`,
`EdgeColorable G G.maxDegree` via a missing-colour alternating path
(or a matching of unsaturated edges at a Δ-vertex). Not landed. Not
labelled König in this file. `Colorable 2` is load-bearing (`C₅` is
class 2). Vizing (`χ' ≤ Δ+1` for general simple graphs) and
list-edge-colouring are leftover-risk of this id — do not expand.
Do not re-prove `konig_bipartite` / Hall / Tutte / greedy / Brooks.
-/

end ProofLab.BipartiteChromaticIndex
