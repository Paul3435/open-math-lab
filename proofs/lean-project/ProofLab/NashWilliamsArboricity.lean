/-
Forest packing — Level A only (empty / ⊥ is 0-forest; a tree is
1-forest and e = n-1; a path is a tree; a star is a tree; K₂ is a
tree; a cycle needs 2 forests). **Not labelled Nash-Williams /
arboricity.**

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 has `IsAcyclic` / `IsTree` / `isAcyclic_bot` /
`IsTree.card_edgeFinset` / `induce` / `edgeFinset` / `completeGraph` /
`pathGraph` and ZERO named Nash-Williams / `nashWilliams` /
`arboricity` / `IsForest` (beyond the `IsAcyclic` module-doc synonym).
Completing the Level A empty / tree / path / star / K₂ / cycle
2-forest glue is the gap this ticket lands. The Level B namesake
`nash_williams` (packing ↔ subgraph bound) is **out of this ticket**
and is **not** sorry-ed. Matroid union / directed branching extras
are residual of this id.

Pin: `catalog/problems/nash-williams-arboricity/STATEMENT.md`
(OPE-1167; Scout OPE-1157 leftover; Director OPE-1166). Encoding:
Mathlib `SimpleGraph` + `IsAcyclic` + edge partition. Zero `sorry`.
Do not import `Archive.*`.

This is **not** `IsAcyclic` / `IsTree`
(`Combinatorics/SimpleGraph/Acyclic.lean` L50 / L54) — already
Mathlib; that is the forest predicate. **USE as glue; do not
re-prove; do not cite as Nash-Williams.** This is **not** `induce` /
`edgeFinset` / `completeGraph` / `pathGraph` (already-in infra).
This is **not** Cayley labelled-tree count (`ProofLab/CayleyTrees.lean`,
#64 informal leftover Prüfer) — different consumed count; do **not**
revive Prüfer. This is **not** Kirchhoff matrix-tree (Cayley leftover
AND Cauchy–Binet leftover). This is **not** Turán / Mantel / KST /
Moore. This is **not** König edge-colouring (#112) / Vizing / Brooks.
Colouring ≠ forest packing. This is **not** matroid union / Edmonds /
directed branching (residual of this id). This is **not**
birkhoff-von-neumann (#123) / Hall / Gale–Ryser. This is **not**
Singleton (#120) / hook-length (#121). Do not re-prime the consumed
mill. Leave OPE-403 alone.

v1 is the undirected finite packing form only. Finite `V` is
load-bearing. Edge *partition* (not cover) is load-bearing. `1 ≤ k`
is load-bearing for the Level B `ℕ` subtraction, not this ticket.
The packing ↔ subgraph-bound identity is the Level B engine, not
this ticket.

Level A: `⊥` is acyclic (`isAcyclic_bot`) and a 0-forest. A tree has
`e = n-1` (`IsTree.card_edgeFinset`) and is already one forest.
`pathGraph (n+1)` is a tree. A star `K_{1,n}` is a tree. `K₂`
(`completeGraph` on 2 vertices) is a tree. A cycle has `e = n` and
`ceil(n/(n-1)) = 2`; deleting one edge leaves a path (1-forest) plus
a leftover edge (1-forest). **Not** labelled Nash-Williams.

Transcribed classical argument (C. St. J. A. Nash-Williams,
*Decomposition of finite graphs into forests*, J. London Math. Soc.
39 (1964) 12). Textbook: Diestel, *Graph Theory*, §2.4 / arboricity.
Compact form: Wikipedia *Nash-Williams theorem* (arboricity). Type
pin: Mathlib `IsAcyclic` / `induce` / `edgeFinset` / `completeGraph` /
`pathGraph`. `IsTree` is a different already-in predicate, used as
glue. Cayley is a different consumed count. No novelty claim.
Default no claim.
-/
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Tactic

set_option linter.unusedVariables false

open Finset Function SimpleGraph

noncomputable section

namespace ProofLab.NashWilliamsArboricity

instance {n : ℕ} : DecidableRel (pathGraph n).Adj :=
  fun i j => decidable_of_iff _ pathGraph_adj.symm

/-! ## Encoding: forest partition (not labelled Nash-Williams) -/

/-- An edge-partition of `G` into `k` acyclic spanning subgraphs
(forests). Partition of *edges* is load-bearing (a cover by
overlapping forests is a different, weaker statement).
**Not** labelled Nash-Williams / arboricity. Reuses Mathlib
`IsAcyclic`; does **not** re-prove acyclicity / Cayley / Turán. -/
def IsForestPartition {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ F : Fin k → SimpleGraph V,
    (∀ i, F i ≤ G ∧ (F i).IsAcyclic) ∧
    (∀ e ∈ G.edgeSet, ∃! i, e ∈ (F i).edgeSet)

/-! ## Glue: small-card / few-edge acyclicity (not a namesake) -/

/-- A cycle needs three distinct vertices, so every graph on at most
two vertices is acyclic. Glue; **not** labelled Nash-Williams. -/
lemma isAcyclic_of_card_le_two {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hV : Fintype.card V ≤ 2) : G.IsAcyclic := by
  intro v p hp
  have hlen : 3 ≤ p.length := hp.three_le_length
  have hnodup : p.support.tail.Nodup := hp.support_nodup
  have hlen' : p.support.tail.length = p.length := by
    simp [Walk.length_support]
  have : p.support.tail.length ≤ Fintype.card V :=
    List.Nodup.length_le_card hnodup
  omega

/-- A cycle is a trail of length ≥ 3, hence uses ≥ 3 distinct edges.
Glue; **not** labelled Nash-Williams. -/
lemma isAcyclic_of_edgeFinset_card_le_two {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.edgeFinset.card ≤ 2) : G.IsAcyclic := by
  intro v p hp
  have hlen : 3 ≤ p.length := hp.three_le_length
  have hnodup : p.edges.Nodup := hp.edges_nodup
  have hcard : p.edges.toFinset.card = p.edges.length :=
    List.toFinset_card_of_nodup hnodup
  have hlenE : p.edges.length = p.length := p.length_edges
  have hsub : p.edges.toFinset ⊆ G.edgeFinset := by
    intro e he
    exact mem_edgeFinset.mpr (p.edges_subset_edgeSet (List.mem_toFinset.mp he))
  have : p.edges.toFinset.card ≤ G.edgeFinset.card := card_le_card hsub
  omega

/-! ## Level A: empty / `⊥` is a 0-forest -/

/-- The empty graph is a 0-forest: no edges to partition, and `Fin 0`
supplies no parts. Uses `isAcyclic_bot`. **Not** labelled
Nash-Williams. -/
theorem isForestPartition_bot_zero {V : Type*} [DecidableEq V] :
    IsForestPartition (⊥ : SimpleGraph V) 0 := by
  refine ⟨Fin.elim0, fun i => i.elim0, ?_⟩
  intro e he
  simp [edgeSet_bot] at he

/-- Glue: Mathlib `isAcyclic_bot`. **Not** labelled Nash-Williams. -/
theorem bot_isAcyclic {V : Type*} : IsAcyclic (⊥ : SimpleGraph V) :=
  isAcyclic_bot

/-! ## Level A: a tree is a 1-forest and `e = n-1` -/

/-- A tree is already one forest: put every edge in the unique part.
**Not** labelled Nash-Williams. -/
theorem isForestPartition_of_isTree {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} (hG : G.IsTree) : IsForestPartition G 1 := by
  refine ⟨fun _ => G, fun _ => ⟨le_rfl, hG.IsAcyclic⟩, ?_⟩
  intro e he
  refine ⟨0, he, ?_⟩
  intro i _
  exact Subsingleton.elim i 0

/-- Glue: Mathlib `IsTree.card_edgeFinset`. A tree on `n` vertices has
`n-1` edges. **Not** labelled Nash-Williams. **Not** Cayley. -/
theorem tree_card_edgeFinset {V : Type*} [Fintype V] {G : SimpleGraph V}
    [Fintype G.edgeSet] (hG : G.IsTree) :
    G.edgeFinset.card + 1 = Fintype.card V :=
  hG.card_edgeFinset

/-! ## Walk glue: getVert vs support, injectivity on a cycle -/

lemma getVert_eq_getElem {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) {i : ℕ} (hi : i < p.support.length) :
    p.getVert i = p.support[i] := by
  induction p generalizing i with
  | nil =>
    have : i = 0 := by
      have : i < 1 := by simpa [Walk.support_nil] using hi
      exact Nat.lt_one_iff.mp this
    subst this
    simp
  | cons h q ih =>
    cases i with
    | zero => simp
    | succ i =>
      have : i < q.support.length := by
        simpa [Walk.support_cons] using hi
      simpa [Walk.getVert, Walk.support_cons] using ih this

lemma support_tail_getElem {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) {k : ℕ} (hk : k + 1 < p.support.length) :
    p.support[k + 1] = p.support.tail[k]'(by
      cases p with
      | nil => simp [Walk.support_nil] at hk
      | cons h q =>
        simpa [Walk.support_cons] using hk) := by
  cases p with
  | nil =>
    simp [Walk.support_nil] at hk
  | cons h q =>
    simp [Walk.support_cons]

lemma list_getElem_eq_of_idx {α : Type*} (l : List α) {i j : ℕ} (h : i = j)
    {hi : i < l.length} {hj : j < l.length} : l[i] = l[j] := by
  subst h
  rfl

lemma cycle_getVert_ne_of_lt {V : Type*} {G : SimpleGraph V} {v : V}
    {p : G.Walk v v} (hp : p.IsCycle) {i j : ℕ}
    (hi : i < p.length) (hj : j < p.length) (hlt : i < j) :
    p.getVert i ≠ p.getVert j := by
  intro heq
  have hlenS : p.support.length = p.length + 1 := p.length_support
  have hiS : i < p.support.length := by omega
  have hjS : j < p.support.length := by omega
  have hnodup : p.support.tail.Nodup := hp.support_nodup
  have hjpos : 0 < j := Nat.zero_lt_of_lt hlt
  have hjt : j - 1 < p.support.tail.length := by simp [Walk.length_support]; omega
  have htailj : p.support.tail[j - 1] = p.getVert j := by
    have hsucc : j - 1 + 1 = j := Nat.sub_add_cancel hjpos
    have hst := support_tail_getElem p (k := j - 1) (by omega)
    refine hst.symm.trans ?_
    have : p.support[j - 1 + 1] = p.support[j] :=
      list_getElem_eq_of_idx p.support hsucc
    exact this.trans (getVert_eq_getElem p hjS).symm
  by_cases hi0 : i = 0
  · subst hi0
    have hjv : p.getVert j = v := by
      simpa [Walk.getVert_zero p] using heq.symm
    have hltail : p.length - 1 < p.support.tail.length := by
      simp [Walk.length_support]; omega
    have htaill : p.support.tail[p.length - 1] = v := by
      have hsucc : p.length - 1 + 1 = p.length := by omega
      have hst := support_tail_getElem p (k := p.length - 1) (by omega)
      refine hst.symm.trans ?_
      have : p.support[p.length - 1 + 1] = p.support[p.length] :=
        list_getElem_eq_of_idx p.support hsucc
      exact this.trans
        ((getVert_eq_getElem p (by omega)).symm.trans p.getVert_length)
    have heq' : p.support.tail[j - 1] = p.support.tail[p.length - 1] := by
      rw [htailj, htaill, hjv]
    have : j - 1 = p.length - 1 := (List.Nodup.getElem_inj_iff hnodup).1 heq'
    omega
  · have hi_pos : 0 < i := Nat.pos_of_ne_zero hi0
    have hit : i - 1 < p.support.tail.length := by simp [Walk.length_support]; omega
    have htaili : p.support.tail[i - 1] = p.getVert i := by
      have hsucc : i - 1 + 1 = i := Nat.sub_add_cancel hi_pos
      have hst := support_tail_getElem p (k := i - 1) (by omega)
      refine hst.symm.trans ?_
      have : p.support[i - 1 + 1] = p.support[i] :=
        list_getElem_eq_of_idx p.support hsucc
      exact this.trans (getVert_eq_getElem p hiS).symm
    have heq' : p.support.tail[i - 1] = p.support.tail[j - 1] := by
      rw [htaili, htailj, heq]
    have : i - 1 = j - 1 := (List.Nodup.getElem_inj_iff hnodup).1 heq'
    omega

lemma cycle_getVert_ne {V : Type*} {G : SimpleGraph V} {v : V}
    {p : G.Walk v v} (hp : p.IsCycle) {i j : ℕ}
    (hi : i < p.length) (hj : j < p.length) (hij : i ≠ j) :
    p.getVert i ≠ p.getVert j := by
  rcases lt_trichotomy i j with hlt | heq | hgt
  · exact cycle_getVert_ne_of_lt hp hi hj hlt
  · exact (hij heq).elim
  · exact (cycle_getVert_ne_of_lt hp hj hi hgt).symm

lemma mem_support_rotate {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v : V}
    {p : G.Walk v v} (h : u ∈ p.support) (x : V) :
    x ∈ (p.rotate h).support ↔ x ∈ p.support := by
  have hspec := p.take_spec h
  constructor
  · intro hx
    rw [Walk.rotate, Walk.mem_support_append_iff] at hx
    rw [← hspec, Walk.mem_support_append_iff]
    exact Or.symm hx
  · intro hx
    rw [Walk.rotate, Walk.mem_support_append_iff]
    rw [← hspec, Walk.mem_support_append_iff] at hx
    exact Or.symm hx

lemma length_rotate {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v : V}
    (p : G.Walk v v) (h : u ∈ p.support) :
    (p.rotate h).length = p.length := by
  have hs := congrArg Walk.length (p.take_spec h)
  rw [Walk.length_append] at hs
  rw [Walk.rotate, Walk.length_append, add_comm, hs]

lemma adj_getVert_last {V : Type*} {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hlen : 1 ≤ p.length) :
    G.Adj (p.getVert (p.length - 1)) v := by
  have hi : p.length - 1 < p.length := Nat.sub_lt (lt_of_lt_of_le Nat.zero_lt_one hlen)
    Nat.zero_lt_one
  have hadj := p.adj_getVert_succ hi
  have : p.length - 1 + 1 = p.length := Nat.sub_add_cancel hlen
  simpa [this, Walk.getVert_length] using hadj

/-! ## Level A: a path is a tree -/

lemma pathGraph_isAcyclic (n : ℕ) : (pathGraph n).IsAcyclic := by
  intro v p hp
  by_cases hn : n ≤ 2
  · exact isAcyclic_of_card_le_two (pathGraph n)
      (by simp [Fintype.card_fin]; omega) p hp
  have hn3 : 3 ≤ n := by omega
  let s : Finset (Fin n) := p.support.toFinset
  have hs : s.Nonempty := ⟨v, List.mem_toFinset.mpr (Walk.start_mem_support p)⟩
  let vmin := s.min' hs
  have hvmin_mem : vmin ∈ p.support := List.mem_toFinset.mp (min'_mem _ hs)
  let q := p.rotate hvmin_mem
  have hq : q.IsCycle := hp.rotate hvmin_mem
  have hlen : 3 ≤ q.length := hq.three_le_length
  have hstart : q.getVert 0 = vmin := q.getVert_zero
  have hneV : q.getVert 1 ≠ q.getVert (q.length - 1) :=
    cycle_getVert_ne hq (by omega) (by omega) (by omega)
  have hadj1 : (pathGraph n).Adj vmin (q.getVert 1) := by
    simpa [hstart] using q.adj_getVert_succ (by omega : (0 : ℕ) < q.length)
  have hadj2 : (pathGraph n).Adj (q.getVert (q.length - 1)) vmin :=
    by simpa [hstart] using adj_getVert_last q (by omega)
  have hql : q.length = p.length := by
    simpa [q] using length_rotate p hvmin_mem
  have hmem1 : q.getVert 1 ∈ s := by
    have : q.getVert 1 ∈ q.support :=
      (Walk.mem_support_iff_exists_getVert).2 ⟨1, rfl, by omega⟩
    have : q.getVert 1 ∈ p.support := (mem_support_rotate hvmin_mem _).1 (by simpa [q] using this)
    exact List.mem_toFinset.mpr this
  have hmem2 : q.getVert (q.length - 1) ∈ s := by
    have : q.getVert (q.length - 1) ∈ q.support :=
      (Walk.mem_support_iff_exists_getVert).2 ⟨q.length - 1, rfl, by omega⟩
    have : q.getVert (q.length - 1) ∈ p.support :=
      (mem_support_rotate hvmin_mem _).1 (by simpa [q] using this)
    exact List.mem_toFinset.mpr this
  have _ := hql
  have hle1 : vmin.val ≤ (q.getVert 1).val :=
    Fin.val_le_of_le (min'_le _ _ hmem1)
  have hle2 : vmin.val ≤ (q.getVert (q.length - 1)).val :=
    Fin.val_le_of_le (min'_le _ _ hmem2)
  have hval1 : (q.getVert 1).val = vmin.val + 1 := by
    have := pathGraph_adj.mp hadj1
    rcases this with h | h
    · exact h.symm
    · omega
  have hval2 : (q.getVert (q.length - 1)).val = vmin.val + 1 := by
    have := pathGraph_adj.mp hadj2.symm
    rcases this with h | h
    · exact h.symm
    · omega
  exact hneV (Fin.ext (hval1.trans hval2.symm))

/-- `pathGraph (n+1)` is a tree. Glue: Mathlib `pathGraph_connected`.
**Not** labelled Nash-Williams. -/
theorem isTree_pathGraph (n : ℕ) : (pathGraph (n + 1)).IsTree where
  isConnected := pathGraph_connected n
  IsAcyclic := pathGraph_isAcyclic (n + 1)

theorem isForestPartition_pathGraph (n : ℕ) :
    IsForestPartition (pathGraph (n + 1)) 1 :=
  isForestPartition_of_isTree (isTree_pathGraph n)

theorem pathGraph_card_edgeFinset (n : ℕ) :
    (pathGraph (n + 1)).edgeFinset.card + 1 = n + 1 := by
  simpa [Fintype.card_fin] using (isTree_pathGraph n).card_edgeFinset

/-! ## Level A: `K₂` is a tree -/

lemma completeGraph_fin_two_eq_pathGraph :
    completeGraph (Fin 2) = pathGraph 2 := by
  rw [pathGraph_two_eq_top]
  ext u v
  simp [completeGraph, SimpleGraph.top_adj]

/-- `K₂` (`completeGraph` on two vertices) is a tree. **Not** labelled
Nash-Williams. -/
theorem isTree_completeGraph_fin_two : (completeGraph (Fin 2)).IsTree := by
  rw [completeGraph_fin_two_eq_pathGraph]
  exact isTree_pathGraph 1

theorem isForestPartition_completeGraph_fin_two :
    IsForestPartition (completeGraph (Fin 2)) 1 :=
  isForestPartition_of_isTree isTree_completeGraph_fin_two

/-! ## Level A: a star is a tree -/

/-- Star `K_{1,n}` as Mathlib `completeBipartiteGraph (Fin 1) (Fin n)`.
Glue; **not** labelled Nash-Williams. -/
abbrev starGraph (n : ℕ) : SimpleGraph (Fin 1 ⊕ Fin n) :=
  completeBipartiteGraph (Fin 1) (Fin n)

lemma starGraph_adj_inr {n : ℕ} (j : Fin n) :
    (starGraph n).Adj (Sum.inl 0) (Sum.inr j) := by
  simp [starGraph, completeBipartiteGraph]

lemma starGraph_preconnected (n : ℕ) : (starGraph n).Preconnected := by
  intro x y
  cases x with
  | inl a =>
    cases y with
    | inl b =>
      have : a = b := Subsingleton.elim a b
      subst this
      exact Reachable.refl _
    | inr j =>
      have : a = 0 := Subsingleton.elim a 0
      subst this
      exact (starGraph_adj_inr j).reachable
  | inr i =>
    cases y with
    | inl b =>
      have : b = 0 := Subsingleton.elim b 0
      subst this
      exact (starGraph_adj_inr i).symm.reachable
    | inr j =>
      exact ((starGraph_adj_inr i).symm.reachable).trans
        (starGraph_adj_inr j).reachable

lemma starGraph_connected (n : ℕ) : (starGraph n).Connected :=
  ⟨starGraph_preconnected n⟩

lemma starGraph_isAcyclic (n : ℕ) : (starGraph n).IsAcyclic := by
  intro v p hp
  have hlen : 3 ≤ p.length := hp.three_le_length
  have hex : ∃ j : Fin n, Sum.inr j ∈ p.support := by
    by_contra h
    push_neg at h
    have hleft : ∀ i : ℕ, i ≤ 2 → ∃ a : Fin 1, p.getVert i = Sum.inl a := by
      intro i hi
      have hmem : p.getVert i ∈ p.support :=
        (Walk.mem_support_iff_exists_getVert).2 ⟨i, rfl, by omega⟩
      cases hx : p.getVert i with
      | inl a => exact ⟨a, rfl⟩
      | inr j => exact (h j (by simpa [hx] using hmem)).elim
    obtain ⟨a, ha⟩ := hleft 0 (by omega)
    obtain ⟨b, hb⟩ := hleft 1 (by omega)
    obtain ⟨c, hc⟩ := hleft 2 (by omega)
    have hab : a = b := Subsingleton.elim a b
    have : p.getVert 0 = p.getVert 1 := by simp [ha, hb, hab]
    exact cycle_getVert_ne hp (by omega) (by omega) (by omega) this
  obtain ⟨j, hj⟩ := hex
  let q := p.rotate hj
  have hq : q.IsCycle := hp.rotate hj
  have hql : q.length = p.length := by
    simpa [q] using length_rotate p hj
  have hlenq : 3 ≤ q.length := hq.three_le_length
  have n1 : q.getVert 1 ≠ q.getVert (q.length - 1) :=
    cycle_getVert_ne hq (by omega) (by omega) (by omega)
  have a1 : (starGraph n).Adj (Sum.inr j) (q.getVert 1) := by
    simpa [q.getVert_zero] using q.adj_getVert_succ (by omega : (0 : ℕ) < q.length)
  have a2 : (starGraph n).Adj (Sum.inr j) (q.getVert (q.length - 1)) := by
    simpa [q.getVert_zero] using (adj_getVert_last q (by omega)).symm
  have only : ∀ w, (starGraph n).Adj (Sum.inr j) w → w = Sum.inl 0 := by
    intro w hw
    cases w with
    | inl a =>
      have : a = 0 := Subsingleton.elim a 0
      subst this
      rfl
    | inr k =>
      simp [starGraph, completeBipartiteGraph] at hw
  exact n1 ((only _ a1).trans (only _ a2).symm)

/-- A star `K_{1,n}` is a tree. **Not** labelled Nash-Williams. -/
theorem isTree_starGraph (n : ℕ) : (starGraph n).IsTree where
  isConnected := starGraph_connected n
  IsAcyclic := starGraph_isAcyclic n

theorem isForestPartition_starGraph (n : ℕ) :
    IsForestPartition (starGraph n) 1 :=
  isForestPartition_of_isTree (isTree_starGraph n)

/-! ## Level A: a cycle needs 2 forests -/

/-- Cycle graph on `Fin n`. Encoding glue for the 2-forest packing;
**not** Eulerian / Hierholzer; **not** labelled Nash-Williams.
Adjacency is by `ℕ`-value so we never need `OfNat (Fin n)`. -/
def cycleGraph (n : ℕ) : SimpleGraph (Fin n) where
  Adj i j :=
    i.val + 1 = j.val ∨ j.val + 1 = i.val ∨
      (2 ≤ n ∧ i.val + 1 = n ∧ j.val = 0) ∨
      (2 ≤ n ∧ j.val + 1 = n ∧ i.val = 0)
  symm := by
    intro i j h
    rcases h with h | h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl h))
  loopless := by
    intro i h
    rcases h with h | h | h | h
    · omega
    · omega
    · omega
    · omega

instance {n : ℕ} : DecidableRel (cycleGraph n).Adj :=
  fun i j => inferInstanceAs (Decidable
    (i.val + 1 = j.val ∨ j.val + 1 = i.val ∨
      (2 ≤ n ∧ i.val + 1 = n ∧ j.val = 0) ∨
      (2 ≤ n ∧ j.val + 1 = n ∧ i.val = 0)))

lemma cycleGraph_adj {n : ℕ} {i j : Fin n} :
    (cycleGraph n).Adj i j ↔
      i.val + 1 = j.val ∨ j.val + 1 = i.val ∨
        (2 ≤ n ∧ i.val + 1 = n ∧ j.val = 0) ∨
        (2 ≤ n ∧ j.val + 1 = n ∧ i.val = 0) :=
  Iff.rfl

def fin0 (n : ℕ) (hn : 1 ≤ n) : Fin n :=
  ⟨0, lt_of_lt_of_le Nat.zero_lt_one hn⟩

def finLast (n : ℕ) (hn : 1 ≤ n) : Fin n :=
  ⟨n - 1, Nat.sub_lt (lt_of_lt_of_le Nat.zero_lt_one hn) Nat.zero_lt_one⟩

lemma finLast_ne_fin0 {n : ℕ} (hn : 2 ≤ n) :
    finLast n (le_trans (by decide : 1 ≤ 2) hn) ≠
      fin0 n (le_trans (by decide : 1 ≤ 2) hn) := by
  intro h
  have : n - 1 = 0 := by
    simpa [finLast, fin0] using congrArg Fin.val h
  omega

lemma cycleGraph_adj_wrap {n : ℕ} (hn : 3 ≤ n) :
    (cycleGraph n).Adj (finLast n (by omega)) (fin0 n (by omega)) :=
  Or.inr (Or.inr (Or.inl ⟨le_trans (by decide : 2 ≤ 3) hn, Nat.sub_add_cancel (by omega), rfl⟩))

lemma pathGraph_not_adj_wrap {n : ℕ} (hn : 3 ≤ n) :
    ¬ (pathGraph n).Adj (finLast n (by omega)) (fin0 n (by omega)) := by
  intro h
  cases pathGraph_adj.mp h with
  | inl h =>
    simp [finLast, fin0] at h
    try omega
  | inr h =>
    simp [finLast, fin0] at h
    try omega

lemma pathGraph_le_cycleGraph {n : ℕ} (hn : 3 ≤ n) :
    pathGraph n ≤ cycleGraph n := by
  intro i j hij
  rw [pathGraph_adj] at hij
  rcases hij with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

lemma wrap_edge_le_cycleGraph {n : ℕ} (hn : 3 ≤ n) :
    SimpleGraph.edge (finLast n (by omega : 1 ≤ n)) (fin0 n (by omega : 1 ≤ n)) ≤
      cycleGraph n := by
  intro i j hij
  rw [edge_adj] at hij
  rcases hij with ⟨h, _hne⟩
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact cycleGraph_adj_wrap hn
  · exact (cycleGraph_adj_wrap hn).symm

lemma cycleGraph_eq_path_sup_wrap {n : ℕ} (hn : 3 ≤ n) :
    cycleGraph n =
      pathGraph n ⊔
        SimpleGraph.edge (finLast n (by omega : 1 ≤ n)) (fin0 n (by omega : 1 ≤ n)) := by
  ext i j
  simp only [sup_adj, cycleGraph_adj, pathGraph_adj, edge_adj]
  constructor
  · intro h
    rcases h with h | h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · refine Or.inr ⟨Or.inl ⟨?_, ?_⟩, ?_⟩
      · exact Fin.ext (show i.val = n - 1 by have := h.2.1; omega)
      · exact Fin.ext (show j.val = 0 from h.2.2)
      · intro hij
        have : i.val = j.val := congrArg Fin.val hij
        omega
    · refine Or.inr ⟨Or.inr ⟨?_, ?_⟩, ?_⟩
      · exact Fin.ext (show i.val = 0 from h.2.2)
      · exact Fin.ext (show j.val = n - 1 by have := h.2.1; omega)
      · intro hij
        have : i.val = j.val := congrArg Fin.val hij
        omega
  · intro h
    rcases h with h | h
    · rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rcases h with ⟨h, hne⟩
      rcases h with ⟨hi, hj⟩ | ⟨hi, hj⟩
      · subst hi
        subst hj
        exact Or.inr (Or.inr (Or.inl
          ⟨le_trans (by decide : 2 ≤ 3) hn, by simp [finLast]; omega, by simp [fin0]⟩))
      · subst hi
        subst hj
        exact Or.inr (Or.inr (Or.inr
          ⟨le_trans (by decide : 2 ≤ 3) hn, by simp [finLast]; omega, by simp [fin0]⟩))

lemma wrap_edge_isAcyclic {n : ℕ} (hn : 3 ≤ n) :
    (SimpleGraph.edge (finLast n (by omega : 1 ≤ n)) (fin0 n (by omega : 1 ≤ n))).IsAcyclic := by
  intro v p hp
  have hlen : 3 ≤ p.length := hp.three_le_length
  have hnodup : p.edges.Nodup := hp.edges_nodup
  have hlenE : p.edges.length = p.length := p.length_edges
  have hne := finLast_ne_fin0 (le_trans (by decide : 2 ≤ 3) hn)
  have hE :=
    edge_edgeSet_of_ne (s := finLast n (by omega : 1 ≤ n))
      (t := fin0 n (by omega : 1 ≤ n)) hne
  have hsub : p.edges.toFinset ⊆ {s(finLast n (by omega : 1 ≤ n), fin0 n (by omega : 1 ≤ n))} := by
    intro e he
    have : e ∈ (SimpleGraph.edge (finLast n (by omega : 1 ≤ n))
        (fin0 n (by omega : 1 ≤ n))).edgeSet :=
      p.edges_subset_edgeSet (List.mem_toFinset.mp he)
    simpa [hE] using this
  have hle : p.edges.toFinset.card ≤ 1 := by
    have := card_le_card hsub
    simpa using this
  have hcard : p.edges.toFinset.card = p.edges.length :=
    List.toFinset_card_of_nodup hnodup
  omega

/-- A cycle on `n ≥ 3` vertices has `n` edges: path (`n-1` edges) plus
the wrap edge. Glue: `IsTree.card_edgeFinset` on `pathGraph`. **Not**
labelled Nash-Williams. **Not** Cayley. -/
theorem cycleGraph_card_edgeFinset {n : ℕ} (hn : 3 ≤ n) :
    (cycleGraph n).edgeFinset.card = n := by
  have heq := cycleGraph_eq_path_sup_wrap hn
  have hnadj := pathGraph_not_adj_wrap hn
  have hne := finLast_ne_fin0 (le_trans (by decide : 2 ≤ 3) hn)
  have hpath : (pathGraph n).edgeFinset.card + 1 = n := by
    have h := pathGraph_card_edgeFinset (n - 1)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at h
    exact h
  have hsup :=
    card_edgeFinset_sup_edge (G := pathGraph n) (s := finLast n (by omega : 1 ≤ n))
      (t := fin0 n (by omega : 1 ≤ n)) hnadj hne
  have : (cycleGraph n).edgeFinset.card =
      (pathGraph n ⊔ SimpleGraph.edge (finLast n (by omega : 1 ≤ n))
        (fin0 n (by omega : 1 ≤ n))).edgeFinset.card := by
    simp [heq]
  omega

/-- Integer form of `⌈n/(n-1)⌉ = 2`: a cycle has `n` edges, which is
strictly more than `n-1` and at most `2(n-1)`. **Not** labelled
Nash-Williams. -/
theorem cycle_ceil_two {n : ℕ} (hn : 3 ≤ n) :
    (cycleGraph n).edgeFinset.card = n ∧
      n ≤ 2 * (n - 1) ∧ n - 1 < n := by
  refine ⟨cycleGraph_card_edgeFinset hn, ?_, ?_⟩
  · omega
  · omega

/-- Deleting one edge of a cycle leaves a path plus a leftover edge —
a 2-forest partition. **Not** labelled Nash-Williams. -/
theorem isForestPartition_cycleGraph_two {n : ℕ} (hn : 3 ≤ n) :
    IsForestPartition (cycleGraph n) 2 := by
  let w := finLast n (by omega : 1 ≤ n)
  let z := fin0 n (by omega : 1 ≤ n)
  let F : Fin 2 → SimpleGraph (Fin n) := fun i =>
    if i.1 = 0 then pathGraph n else SimpleGraph.edge w z
  refine ⟨F, ?_, ?_⟩
  · intro i
    by_cases hi : i.1 = 0
    · simp [F, hi]
      exact ⟨pathGraph_le_cycleGraph hn, pathGraph_isAcyclic n⟩
    · simp [F, hi]
      exact ⟨wrap_edge_le_cycleGraph hn, wrap_edge_isAcyclic hn⟩
  · intro e he
    have hG := cycleGraph_eq_path_sup_wrap hn
    have hmem : e ∈ (pathGraph n ⊔ SimpleGraph.edge w z).edgeSet := by
      simpa [hG] using he
    rw [edgeSet_sup] at hmem
    rcases hmem with hp | hw
    · refine ⟨⟨0, by decide⟩, ?_, ?_⟩
      · simp [F, hp]
      · intro j hj
        fin_cases j
        · rfl
        · simp [F] at hj
          have hne := finLast_ne_fin0 (le_trans (by decide : 2 ≤ 3) hn)
          have : e = s(w, z) := by
            simpa [edge_edgeSet_of_ne hne] using hj
          subst this
          exact (pathGraph_not_adj_wrap hn (by simpa [mem_edgeSet] using hp)).elim
    · refine ⟨⟨1, by decide⟩, ?_, ?_⟩
      · simp [F]
        exact hw
      · intro j hj
        fin_cases j
        · simp [F] at hj
          have hne := finLast_ne_fin0 (le_trans (by decide : 2 ≤ 3) hn)
          have : e = s(w, z) := by
            simpa [edge_edgeSet_of_ne hne] using hw
          subst this
          exact (pathGraph_not_adj_wrap hn (by simpa [mem_edgeSet] using hj)).elim
        · rfl

/-
Residual (Level B, **out of this ticket**, not sorry-ed):
  theorem nash_williams {V : Type*} [Fintype V] [DecidableEq V]
      [DecidableRel (· : SimpleGraph V).Adj]
      (G : SimpleGraph V) {k : ℕ} (hk : 1 ≤ k) :
      IsForestPartition G k ↔
        ∀ s : Set V, 2 ≤ Fintype.card s →
          (G.induce s).edgeFinset.card ≤ k * (Fintype.card s - 1)
Necessity: a forest on `s` has < |s| edges. Sufficiency is the
Nash-Williams packing (induct / greedy spanning-forest extraction).
Do not sorry the namesake. Matroid union / directed branching remain
residual of this id. Do not re-prove IsAcyclic / Cayley / Prüfer /
Kirchhoff / Turán / König edge-colouring / Vizing / Brooks /
birkhoff_von_neumann / Hall / Gale–Ryser / singleton_bound /
hook_length.
-/

end ProofLab.NashWilliamsArboricity
