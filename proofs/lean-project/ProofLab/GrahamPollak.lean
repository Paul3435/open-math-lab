/-
Graham–Pollak biclique decomposition of K_n — Level A only (K₁ empty /
K₂ one K_{1,1} / K₃ star-plus-edge). **Not labelled Graham–Pollak /
Nash–Williams / KST.**

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 pin `a719ba5c3115` has `completeGraph` /
`completeGraph_eq_top` / `completeBipartiteGraph` / `edgeFinset` /
`edgeFinset_bot` / `card_edgeFinset_top_eq_card_choose_two` /
`Disjoint` as **infra**. ZERO named Graham–Pollak / `grahamPollak` /
`graham_pollak` / `biclique` / `Biclique` / `bicliquePartition` /
`Pollak` / `pollak` under `Mathlib/` or `Archive/` or `ProofLab/`.
Completing the Level A K₁ empty / K₂ one edge / K₃ star-plus-edge
glue is the gap this ticket lands. The Level B namesake
`graham_pollak` (every biclique partition of `K_n`, `n ≥ 1`, has
size `≥ n-1`, and size `n-1` is achieved) is **out of this ticket**
and is **not** sorry-ed. Biclique *cover* (overlapping allowed) /
Zarankiewicz extras are residual of this id.

Pin: `catalog/problems/graham-pollak/STATEMENT.md`
(OPE-1258; Scout OPE-1248 leftover; Director OPE-1257). Encoding:
Mathlib `completeGraph` / `edgeFinset` / `Disjoint` on `Fin 1` /
`Fin 2` / `Fin 3`. Zero `sorry`. Do not import `Archive.*`.

This is **not** `completeGraph` (`Basic.lean` L144) /
`completeGraph_eq_top` L339 — already Mathlib. **USE, do not
re-prove; do not cite as Graham–Pollak.**
This is **not** `completeBipartiteGraph` (`Basic.lean` L153) —
DIFFERENT `K_{a,b}` glue; a biclique *in* `K_n` is a Finset-pair
encoding, not a re-proof of `K_{a,b}`. **USE as glue if needed; do
not re-prove; do not cite as Graham–Pollak.**
This is **not** `edgeFinset` (`Finite.lean` L53) / `edgeFinset_bot`
L81 / `card_edgeFinset_top_eq_card_choose_two` L110 — already
Mathlib. **USE, do not re-prove.**
This is **not** Nash–Williams arboricity
(`ProofLab/NashWilliamsArboricity.lean`, PR #124). Forests ≠
bicliques. Do **not** revive `nash_williams` / matroid-union.
This is **not** Kővári–Sós–Turán (`ProofLab/KovariSosTuran.lean`).
Forbidding a biclique is the opposite theorem.
This is **not** Cayley / Kirchhoff (`ProofLab/CayleyTrees.lean`).
Do not count spanning trees.
This is **not** Sherman–Morrison (`ProofLab/ShermanMorrison.lean`,
PR #141) / Woodbury / SVD.
This is **not** Kraft (`ProofLab/KraftInequality.lean`, PR #138) /
McMillan / Huffman.
This is **not** Sabidussi (`ProofLab/SabidussiBoxProd.lean`, PR
#139) / Hedetniemi.
This is **not** Brooks / greedy / König χ'
(`ProofLab/Brooks.lean` / `ProofLab/GreedyChromatic.lean` /
`ProofLab/BipartiteChromaticIndex.lean`).
Do not re-prime the consumed mill. Leave OPE-403 alone.
Leave OPE-1195 alone.

v1 is an explicit biclique-edge partition of
`completeGraph (Fin n)` of size `n-1` for `n = 1, 2, 3`, **not
labelled Graham–Pollak**. Bipartition `Disjoint X Y` is
load-bearing. Partition of `edgeFinset` is load-bearing.
`n ≥ 1` is load-bearing (`n-1` for `n = 0` is not a Nat). Finite
`Fin 1` / `Fin 2` / `Fin 3` are load-bearing.

Level A: `K_1` has no edges, empty partition of size `0 = 1-1`.
`K_2` is one edge, one `K_{1,1}` on `{0}` vs `{1}`. `K_3` is the
star at 0 covering `{0-1, 0-2}` plus leftover `{1}–{2}`. **Not**
labelled Graham–Pollak.

Transcribed classical argument (R. L. Graham, H. O. Pollak,
*On the addressing problem for loop switching*, Bell System
Tech. J. 50 (1971) 2495–2519). Compact form: Wikipedia
*Graham–Pollak theorem*. Type pin: `completeGraph` / `edgeFinset`
/ Finset-pair `bicliqueEdges`. Nash–Williams is a different
consumed forest-partition theorem. KST is a different consumed
forbidden-biclique theorem. No novelty claim. Default no claim.
-/
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sym
import Mathlib.Tactic

set_option linter.unusedVariables false

open SimpleGraph Finset

noncomputable section
open Classical

namespace ProofLab.GrahamPollak

/-- `completeGraph` is `⊤`; Mathlib already has `fintypeEdgeSet` for
graphs with decidable adjacency. Glue instance; **not** labelled
Graham–Pollak. -/
instance instFintypeCompleteGraphEdgeSet (V : Type*) [Fintype V] [DecidableEq V] :
    Fintype (completeGraph V).edgeSet :=
  inferInstanceAs (Fintype (⊤ : SimpleGraph V).edgeSet)

/-! ## Level A: K₁ empty / K₂ one edge / K₃ star-plus-edge
(not labelled Graham–Pollak / Nash–Williams / KST) -/

/-- Edges of the biclique with parts `X`, `Y` (loops dropped).
Encoding; **not** labelled Graham–Pollak. -/
def bicliqueEdges {V : Type*} [DecidableEq V] (X Y : Finset V) :
    Finset (Sym2 V) :=
  ((X ×ˢ Y).filter fun p => p.1 ≠ p.2).image fun p => s(p.1, p.2)

/-- Membership: an undirected edge is in `bicliqueEdges X Y` iff it
joins a vertex of `X` to a distinct vertex of `Y`. Glue; **not**
labelled Graham–Pollak. -/
lemma mem_bicliqueEdges {V : Type*} [DecidableEq V] {X Y : Finset V}
    {e : Sym2 V} :
    e ∈ bicliqueEdges X Y ↔ ∃ x ∈ X, ∃ y ∈ Y, x ≠ y ∧ e = s(x, y) := by
  constructor
  · intro h
    obtain ⟨p, hp, rfl⟩ := mem_image.mp h
    obtain ⟨hpXY, hne⟩ := mem_filter.mp hp
    obtain ⟨hx, hy⟩ := mem_product.mp hpXY
    exact ⟨p.1, hx, p.2, hy, hne, rfl⟩
  · rintro ⟨x, hx, y, hy, hne, rfl⟩
    refine mem_image.mpr ⟨(x, y), ?_, rfl⟩
    exact mem_filter.mpr ⟨mem_product.mpr ⟨hx, hy⟩, hne⟩

/-- A pair of Finsets is a biclique partition of `completeGraph V`
when parts are disjoint, their biclique edge-sets are pairwise
disjoint, and they union to `edgeFinset`. Encoding; **not** labelled
Graham–Pollak. -/
def IsBicliquePartition {V : Type*} [Fintype V] [DecidableEq V]
    (parts : Finset (Finset V × Finset V)) : Prop :=
  (∀ p ∈ parts, Disjoint p.1 p.2) ∧
  (parts.toSet.Pairwise fun p q =>
      Disjoint (bicliqueEdges p.1 p.2) (bicliqueEdges q.1 q.2)) ∧
  (parts.biUnion (fun p => bicliqueEdges p.1 p.2)
      = (completeGraph V).edgeFinset)

/-- Non-loop edges of `K_V`. Uses `completeGraph_eq_top` /
`edgeFinset_top`; does **not** re-prove them. Glue; **not** labelled
Graham–Pollak. -/
lemma mem_completeGraph_edgeFinset {V : Type*} [Fintype V] [DecidableEq V]
    {e : Sym2 V} :
    e ∈ (completeGraph V).edgeFinset ↔ ¬e.IsDiag := by
  rw [mem_edgeFinset]
  refine Sym2.inductionOn e fun x y => ?_
  rw [mem_edgeSet, completeGraph_eq_top, top_adj, Sym2.mk_isDiag_iff]

/-- `s(x,y)` is an edge of `K_V` iff `x ≠ y`. Uses `mem_edgeSet` /
`top_adj` via `completeGraph_eq_top`; does **not** re-prove complete
graphs. Glue; **not** labelled Graham–Pollak. -/
lemma mk_mem_completeGraph_edgeFinset {V : Type*} [Fintype V]
    [DecidableEq V] {x y : V} :
    s(x, y) ∈ (completeGraph V).edgeFinset ↔ x ≠ y := by
  rw [mem_completeGraph_edgeFinset, Sym2.mk_isDiag_iff]

/-- Empty partition of `K_1`: no edges, size `0 = 1-1`. Glue; **not**
labelled Graham–Pollak. -/
theorem bicliquePartition_complete_fin_one :
    IsBicliquePartition
      (∅ : Finset (Finset (Fin 1) × Finset (Fin 1)))
    ∧ (∅ : Finset (Finset (Fin 1) × Finset (Fin 1))).card
        = 1 - 1 := by
  refine ⟨⟨?disj, ⟨?pair, ?cover⟩⟩, ?card⟩
  · intro p hp
    exact (not_mem_empty p hp).elim
  · intro a ha
    exact (not_mem_empty a (mem_coe.mp ha)).elim
  · rw [biUnion_empty]
    ext e
    refine Sym2.inductionOn e fun x y => ?_
    simp [mk_mem_completeGraph_edgeFinset, Subsingleton.elim x y]
  · simp

/-- `K_2` is the single edge `0—1`. Uses `edgeFinset_top`; does
**not** re-prove complete graphs. Glue; **not** labelled
Graham–Pollak. -/
lemma completeGraph_fin_two_edgeFinset :
    (completeGraph (Fin 2)).edgeFinset = {s((0 : Fin 2), 1)} := by
  ext e
  refine Sym2.inductionOn e fun x y => ?_
  rw [mk_mem_completeGraph_edgeFinset, mem_singleton, Sym2.eq_iff]
  fin_cases x <;> fin_cases y <;> decide

/-- Singleton biclique `{x}` vs `{y}` is the one edge `x—y` when
`x ≠ y`. Glue; **not** labelled Graham–Pollak. -/
lemma bicliqueEdges_singletons {V : Type*} [DecidableEq V] {x y : V}
    (h : x ≠ y) :
    bicliqueEdges ({x} : Finset V) {y} = {s(x, y)} := by
  ext e
  rw [mem_bicliqueEdges, mem_singleton]
  constructor
  · rintro ⟨a, ha, b, hb, _, rfl⟩
    simp only [mem_singleton] at ha hb
    subst ha; subst hb
    rfl
  · rintro rfl
    exact ⟨x, mem_singleton.2 rfl, y, mem_singleton.2 rfl, h, rfl⟩

/-- One `K_{1,1}` partitions `K_2`, size `1 = 2-1`. Glue; **not**
labelled Graham–Pollak. -/
theorem bicliquePartition_complete_fin_two :
    IsBicliquePartition
      ({({0}, {1})} : Finset (Finset (Fin 2) × Finset (Fin 2)))
    ∧ ({({0}, {1})} : Finset (Finset (Fin 2) × Finset (Fin 2))).card
        = 2 - 1 := by
  refine ⟨⟨?disj, ⟨?pair, ?cover⟩⟩, ?card⟩
  · intro p hp
    simp only [mem_singleton] at hp
    subst hp
    exact disjoint_singleton.2 (by decide : (0 : Fin 2) ≠ 1)
  · intro a ha b hb hne
    simp only [mem_coe, mem_singleton] at ha hb
    exact (hne (ha.trans hb.symm)).elim
  · change bicliqueEdges {0} {1} = (completeGraph (Fin 2)).edgeFinset
    rw [bicliqueEdges_singletons (by decide : (0 : Fin 2) ≠ 1),
      completeGraph_fin_two_edgeFinset]
  · decide

/-- `K_3` has edges `0—1`, `0—2`, `1—2`. Uses `edgeFinset_top`; does
**not** re-prove complete graphs. Glue; **not** labelled
Graham–Pollak. -/
lemma completeGraph_fin_three_edgeFinset :
    (completeGraph (Fin 3)).edgeFinset =
      {s((0 : Fin 3), 1), s(0, 2), s(1, 2)} := by
  ext e
  refine Sym2.inductionOn e fun x y => ?_
  rw [mk_mem_completeGraph_edgeFinset]
  fin_cases x <;> fin_cases y <;> decide

/-- Star at `0` on `K_3` covers `{0—1, 0—2}`. Glue; **not** labelled
Graham–Pollak. -/
lemma bicliqueEdges_fin_three_star :
    bicliqueEdges ({0} : Finset (Fin 3)) {1, 2} =
      {s((0 : Fin 3), 1), s(0, 2)} := by
  ext e
  refine Sym2.inductionOn e fun x y => ?_
  rw [mem_bicliqueEdges]
  fin_cases x <;> fin_cases y <;> simp [Sym2.eq_iff]

/-- Leftover edge `{1}–{2}` on `K_3`. Glue; **not** labelled
Graham–Pollak. -/
lemma bicliqueEdges_fin_three_edge :
    bicliqueEdges ({1} : Finset (Fin 3)) {2} = {s((1 : Fin 3), 2)} :=
  bicliqueEdges_singletons (by decide : (1 : Fin 3) ≠ 2)

/-- Star at 0 plus leftover edge partitions `K_3`, size `2 = 3-1`.
Glue; **not** labelled Graham–Pollak. -/
theorem bicliquePartition_complete_fin_three :
    IsBicliquePartition
      ({({0}, {1, 2}), ({1}, {2})} :
        Finset (Finset (Fin 3) × Finset (Fin 3)))
    ∧ ({({0}, {1, 2}), ({1}, {2})} :
        Finset (Finset (Fin 3) × Finset (Fin 3))).card
        = 3 - 1 := by
  set parts :
      Finset (Finset (Fin 3) × Finset (Fin 3)) :=
    {({0}, {1, 2}), ({1}, {2})}
  have hmem {p : Finset (Fin 3) × Finset (Fin 3)} :
      p ∈ parts ↔ p = ({0}, {1, 2}) ∨ p = ({1}, {2}) := by
    simp [parts, mem_insert, mem_singleton]
  refine ⟨⟨?disj, ⟨?pair, ?cover⟩⟩, ?card⟩
  · intro p hp
    rcases (hmem.mp hp) with rfl | rfl
    · exact disjoint_singleton_left.2 (by decide)
    · exact disjoint_singleton.2 (by decide : (1 : Fin 3) ≠ 2)
  · intro a ha b hb hab
    have ha' := hmem.mp (mem_coe.mp ha)
    have hb' := hmem.mp (mem_coe.mp hb)
    rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
    · exact (hab rfl).elim
    · rw [bicliqueEdges_fin_three_star, bicliqueEdges_fin_three_edge]
      decide
    · rw [bicliqueEdges_fin_three_star, bicliqueEdges_fin_three_edge]
      decide
    · exact (hab rfl).elim
  · ext e
    refine Sym2.inductionOn e fun x y => ?_
    simp [parts, mem_biUnion, mem_insert, mem_singleton,
      bicliqueEdges_fin_three_star, bicliqueEdges_fin_three_edge,
      mk_mem_completeGraph_edgeFinset]
    fin_cases x <;> fin_cases y <;> decide
  · decide

/-
Level B namesake OUT of this ticket (do not sorry):

theorem graham_pollak {n : ℕ} (hn : 0 < n) :
    IsLeast {k | ∃ parts : Finset (Finset (Fin n) × Finset (Fin n)),
      IsBicliquePartition parts ∧ parts.card = k} (n - 1)

Residual of this id (comment only, not sorry): biclique *cover*
(overlapping allowed) / Zarankiewicz / linear-algebra rank proof of
the `n-1` lower bound. Do not expand this ticket.
-/

end ProofLab.GrahamPollak
