/-
Moore degree–girth bound (Hoffman–Singleton 1960 counting; Biggs / Diestel BFS).

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 has `egirth` / `girth` / `minDegree` / `degree` / `dist` /
`edist` / `Walk.IsCycle` / `neighborFinset` and ZERO Moore-bound / cage /
degree–girth ident (Archive `moore` hits only algebraic-topology
`MooreComplex`). Completing the namesake is the gap.

Pin: `catalog/problems/moore-degree-girth/STATEMENT.md` (OPE-759; Scout
OPE-754 prime; Director OPE-758). Encoding: Mathlib `SimpleGraph` +
`minDegree` + `egirth`. Zero `sorry`. Do not import `Archive.*`.

This is **not** Turán (`SimpleGraph/Turan.lean` already upstream; OPE-25
negative control — never cite Turán as this gap). Moore is degree–girth
counting, not `K_{r+1}`-free max-edges.
This is **not** Mantel.
This is **not** the cage problem (exact `n(k,g)` is open for most
parameters; out of v1). Formalizing the classical lower bound is not a
novelty claim and not a near-miss at cages.
This is **not** Hoffman–Singleton classification (cycles, Petersen, HS,
maybe 57-regular). The 57-regular existence question is **open**. Out of v1.
This is **not** Friendship / windmill (`ProofLab/Friendship.lean`, PR #40).
This is **not** Mycielski (`ProofLab/Mycielski.lean`, PR #65). `C5` may be
reused as a tightness *comment* for `k = 2, t = 2` (`n ≥ 5`), **not**
labelled Moore.
This is **not** Kővári–Sós–Turán (consumed PR #73).
This is **not** the degree–diameter *upper* bound `n ≤ 1 + Δ Σ (Δ−1)^i`
(dual counting; out of v1 this id).
Even girth `g = 2t` is out of v1. Do not invent moore-C / even-girth /
cages as a leftover.
This is **not** stirling-second-kind (OPE-754 leftover slot #2, unassigned).

`2 ≤ k` is load-bearing so `k - 1` is a predecessor in `ℕ`.
`1 ≤ t` is load-bearing so the sum is the interesting geometric sum
(`t = 0` is vacuous `n ≥ 1`). v1 is **odd girth only**.

Level A: `t = 1` (girth ≥ 3) gives `n ≥ 1 + k`, the star bound
`card V ≥ 1 + minDegree` (glue, **not** labelled Moore). `k = 2, t = 2`
gives `n ≥ 5`; `C5` saturates (comment, not labelled Moore). `k = 3, t = 2`
gives `n ≥ 10` (Petersen tightness is a **comment**, not a uniqueness
theorem). Empty / edgeless landmines: `minDegree = 0` is excluded by
`2 ≤ k`. Zero sorry.
Level B: namesake `moore_bound_odd_girth` by BFS non-collision inside
radius `t`.

Equality cases (cycles `C_{2t+1}`, Petersen, Hoffman–Singleton) are
**comments, not theorems**.
-/
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Tactic

set_option maxHeartbeats 400000

open Finset SimpleGraph

noncomputable section
open Classical

namespace ProofLab.MooreDegreeGirth

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## Degree / emptiness dictionary -/

lemma minDegree_eq_zero_of_isEmpty [IsEmpty V] : G.minDegree = 0 := by
  simp [minDegree]

lemma nonempty_of_two_le_minDegree {k : ℕ} (hk : 2 ≤ k) (hδ : k ≤ G.minDegree) :
    Nonempty V := by
  by_contra hne
  haveI : IsEmpty V := not_nonempty_iff.mp hne
  have := minDegree_eq_zero_of_isEmpty G
  omega

lemma card_ge_one_add_degree (u : V) : 1 + G.degree u ≤ Fintype.card V := by
  have := G.degree_lt_card_verts u
  omega

/-! ## Level A: star bound (glue, **not** labelled Moore)

`t = 1` unfolding is `n ≥ 1 + k`. Simple graphs already satisfy
`3 ≤ egirth` (`three_le_egirth`), so the girth pin is free here.
Empty / edgeless graphs have `minDegree = 0` and are excluded by `2 ≤ k`. -/

/-- Star bound: `card V ≥ 1 + minDegree` under `2 ≤ k ≤ minDegree`.
Glue, **not** labelled Moore. -/
theorem star_bound {k : ℕ} (hk : 2 ≤ k) (hδ : k ≤ G.minDegree) :
    1 + k ≤ Fintype.card V := by
  haveI := nonempty_of_two_le_minDegree G hk hδ
  obtain ⟨u⟩ := ‹Nonempty V›
  have hdeg : k ≤ G.degree u := le_trans hδ (G.minDegree_le_degree u)
  have := card_ge_one_add_degree G u
  omega

/-- Level A specialisation `t = 1`: `2 * 1 + 1 = 3 ≤ egirth` is automatic
for simple graphs. Glue, **not** labelled Moore. -/
theorem moore_bound_odd_girth_t_one {k : ℕ} (hk : 2 ≤ k)
    (hδ : k ≤ G.minDegree) (_hg : 2 * 1 + 1 ≤ G.egirth) :
    1 + k * ∑ i ∈ range 1, (k - 1) ^ i ≤ Fintype.card V := by
  have := star_bound G hk hδ
  simpa [Finset.sum_range_one] using this

/-! ## Spheres (BFS layers via `edist`, not junk-`0` `dist`) -/

/-- Vertices at extended distance `i` from `u`. Engine, not a second id. -/
def sphere (u : V) (i : ℕ) : Finset V :=
  univ.filter (fun v => G.edist u v = i)

lemma mem_sphere {u v : V} {i : ℕ} :
    v ∈ sphere G u i ↔ G.edist u v = i := by
  simp [sphere]

lemma sphere_zero (u : V) : sphere G u 0 = {u} := by
  ext w
  simp only [mem_sphere G, mem_singleton]
  constructor
  · intro h
    have : G.edist u w = 0 := by simpa using h
    exact (edist_eq_zero_iff.mp this).symm
  · intro h
    subst w
    simp [SimpleGraph.edist_self]

lemma sphere_one (u : V) : sphere G u 1 = G.neighborFinset u := by
  ext w
  simp [mem_sphere G, mem_neighborFinset, edist_eq_one_iff_adj]

lemma card_sphere_zero (u : V) : (sphere G u 0).card = 1 := by
  simp [sphere_zero G]

lemma disjoint_sphere {u : V} {i j : ℕ} (h : i ≠ j) :
    Disjoint (sphere G u i) (sphere G u j) := by
  rw [Finset.disjoint_left]
  intro v hi hj
  rw [mem_sphere G] at hi hj
  exact h (Nat.cast_injective (hi.symm.trans hj))

lemma card_biUnion_sphere (u : V) (s : Finset ℕ) :
    (s.biUnion (sphere G u)).card = ∑ i ∈ s, (sphere G u i).card :=
  card_biUnion (fun _ _ _ _ hij => disjoint_sphere G hij)

lemma sum_range_succ' (n : ℕ) (f : ℕ → ℕ) :
    ∑ i ∈ range (n + 1), f i = f 0 + ∑ i ∈ range n, f (i + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, sum_range_succ, add_assoc]

/-! ## Shortest-path prefixes / suffixes -/

lemma exists_prefix_walk {u v : V} (p : G.Walk u v) (j : ℕ) (hj : j ≤ p.length) :
    ∃ q : G.Walk u (p.getVert j), q.length = j := by
  induction p generalizing j with
  | nil =>
    have hj0 : j = 0 := by simp at hj; exact hj
    subst j
    exact ⟨Walk.nil, rfl⟩
  | cons h p ih =>
    cases j with
    | zero => exact ⟨Walk.nil, rfl⟩
    | succ j =>
      obtain ⟨q, hq⟩ := ih j (by simpa using hj)
      exact ⟨Walk.cons h q, by simp [hq]⟩

lemma exists_suffix_walk {u v : V} (p : G.Walk u v) (j : ℕ) (hj : j ≤ p.length) :
    ∃ q : G.Walk (p.getVert j) v, q.length = p.length - j := by
  induction p generalizing j with
  | nil =>
    have hj0 : j = 0 := by simp at hj; exact hj
    subst j
    exact ⟨Walk.nil, by simp⟩
  | cons h p ih =>
    cases j with
    | zero => exact ⟨Walk.cons h p, by simp⟩
    | succ j =>
      simpa using ih j (by simpa using hj)

lemma exists_shortest_path {u v : V} {i : ℕ} (h : G.edist u v = i) :
    ∃ p : G.Walk u v, p.IsPath ∧ p.length = i := by
  obtain ⟨p, hp⟩ := exists_walk_of_edist_eq_coe h
  have hdist : SimpleGraph.dist G u v = i := by
    simp [SimpleGraph.dist, h]
  exact ⟨p, p.isPath_of_length_eq_dist (hp.trans hdist.symm), hp⟩

lemma edist_getVert_eq {u v : V} {p : G.Walk u v} {i : ℕ}
    (hlen : p.length = i) (hedist : G.edist u v = i) (j : ℕ) (hj : j ≤ i) :
    G.edist u (p.getVert j) = j := by
  have hle : G.edist u (p.getVert j) ≤ (j : ℕ∞) := by
    obtain ⟨q, hq⟩ := exists_prefix_walk G p j (hlen ▸ hj)
    simpa [hq] using edist_le q
  refine le_antisymm hle ?_
  by_contra hnot
  have hlt : G.edist u (p.getVert j) < (j : ℕ∞) :=
    lt_iff_le_not_le.mpr ⟨hle, hnot⟩
  have hjpos : 1 ≤ j := by
    cases j with
    | zero =>
      have : (0 : ℕ∞) ≤ G.edist u (p.getVert 0) := bot_le
      exact (hnot this).elim
    | succ _ => exact Nat.succ_le_succ (Nat.zero_le _)
  have hne : G.edist u (p.getVert j) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.coe_ne_top j) hle
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hne
  have hmlt : m < j := by
    rw [← hm] at hlt
    exact Nat.cast_lt.mp hlt
  have hmle : m ≤ j - 1 := Nat.le_pred_of_lt hmlt
  obtain ⟨s, hs⟩ := exists_suffix_walk G p j (hlen ▸ hj)
  have htail : G.edist (p.getVert j) v ≤ ((i - j) : ℕ∞) := by
    simpa [hs, hlen] using edist_le s
  have htri : G.edist u v ≤ G.edist u (p.getVert j) + G.edist (p.getVert j) v :=
    SimpleGraph.edist_triangle
  have hsum : G.edist u v ≤ ((j - 1) + (i - j) : ℕ) := by
    calc
      G.edist u v ≤ G.edist u (p.getVert j) + G.edist (p.getVert j) v := htri
      _ ≤ (m : ℕ∞) + (i - j : ℕ) := by
          rw [← hm]
          exact add_le_add_left htail _
      _ ≤ ((j - 1) + (i - j) : ℕ) := by
          simp only [Nat.cast_add]
          exact add_le_add_right (Nat.cast_le.mpr hmle) _
  have hsub : (j - 1) + (i - j) = i - 1 := by omega
  have : (i : ℕ∞) ≤ (i - 1 : ℕ) := by
    rw [hedist] at hsum
    simpa [hsub] using hsum
  have hi : 1 ≤ i := le_trans hjpos hj
  have : i ≤ i - 1 := Nat.cast_le.mp this
  omega

lemma exists_parent {u v : V} {i : ℕ} (hi : 1 ≤ i) (hv : G.edist u v = i) :
    ∃ x : V, G.Adj v x ∧ G.edist u x = i - 1 := by
  obtain ⟨p, _, hlen⟩ := exists_shortest_path G hv
  refine ⟨p.getVert (i - 1), ?_, ?_⟩
  · have hlt : i - 1 < p.length := by omega
    have hadj := p.adj_getVert_succ hlt
    have hvj : p.getVert i = v := by
      have : p.getVert p.length = v := p.getVert_length
      simpa [hlen] using this
    have : p.getVert (i - 1 + 1) = v := by
      simpa [Nat.sub_add_cancel hi] using hvj
    simpa [this] using hadj.symm
  · exact edist_getVert_eq G hlen hv (i - 1) (Nat.sub_le _ _)

lemma edist_le_of_mem_support {u x z : V} (p : G.Walk u x) (hz : z ∈ p.support) :
    G.edist u z ≤ p.length := by
  have := edist_le (p.takeUntil z hz)
  exact le_trans this (Nat.cast_le.mpr (p.length_takeUntil_le hz))

/-! ## Cycle extraction (length-controlled; uses `Path.cons_isCycle`) -/

lemma exists_cycle_of_walk_avoiding_edge {x y : V} (hxy : G.Adj x y)
    (p : G.Walk x y) (hp : s(x, y) ∉ p.edges) :
    ∃ (z : V) (c : G.Walk z z), c.IsCycle ∧ c.length ≤ p.length + 1 := by
  refine ⟨y, Walk.cons hxy.symm ↑p.toPath, ?_, ?_⟩
  · refine Path.cons_isCycle p.toPath hxy.symm ?_
    intro hmem
    exact hp (Walk.edges_toPath_subset p (by simpa [Sym2.eq_swap] using hmem))
  · simp only [Walk.length_cons]
    exact Nat.succ_le_succ (p.length_bypass_le)

lemma not_cycle_length_le {t : ℕ} (hg : (2 * t + 1 : ℕ∞) ≤ G.egirth)
    {z : V} {c : G.Walk z z} (hc : c.IsCycle) (hle : c.length ≤ 2 * t) :
    False := by
  have : 2 * t + 1 ≤ c.length := Nat.cast_le.mp (le_egirth.mp hg z c hc)
  omega

lemma edge_not_mem_shortest {u x y : V} {p : G.Walk u x} {i : ℕ}
    (hlen : p.length = i) (hedist : G.edist u x = i)
    (hy : G.edist u y = i) (hxy : G.Adj x y) :
    s(x, y) ∉ p.edges := by
  intro hmem
  have hyp : y ∈ p.support := Walk.snd_mem_support_of_mem_edges p hmem
  have : G.edist u y ≤ i := by
    simpa [hlen] using edist_le_of_mem_support G p hyp
  have hyi : (i : ℕ∞) ≤ i := le_rfl
  have : y = x := by
    have hy0 : G.edist u y = i := hy
    -- y on a shortest u–x path of length i, and edist u y = i, so y is the
    -- endpoint: otherwise a strictly shorter walk to x would exist.
    obtain ⟨j, rfl, hj⟩ := (Walk.mem_support_iff_exists_getVert).mp hyp
    have hj' : j ≤ i := by simpa [hlen] using hj
    have : G.edist u (p.getVert j) = j := edist_getVert_eq G hlen hedist j hj'
    have hj_eq : j = i := by
      have : (j : ℕ∞) = i := this.symm.trans hy0
      exact Nat.cast_injective this
    subst hj_eq
    have : p.getVert p.length = x := p.getVert_length
    simpa [hlen] using this
  exact (G.ne_of_adj hxy).symm this

/-! ## Collision lemmas inside radius `t` -/

/-- Two distinct neighbours in the previous layer of a vertex at distance
`j ≤ t` yield a cycle of length `≤ 2j ≤ 2t`. -/
lemma no_two_parents {u v : V} {t j : ℕ} (hj : 1 ≤ j) (hjt : j ≤ t)
    (hv : v ∈ sphere G u j) {x y : V} (hxy : x ≠ y)
    (hx : x ∈ sphere G u (j - 1)) (hy : y ∈ sphere G u (j - 1))
    (hvx : G.Adj v x) (hvy : G.Adj v y)
    (hg : (2 * t + 1 : ℕ∞) ≤ G.egirth) : False := by
  rw [mem_sphere G] at hv hx hy
  obtain ⟨px, _, hlenx⟩ := exists_shortest_path G hx
  obtain ⟨py, _, hleny⟩ := exists_shortest_path G hy
  let wlk : G.Walk x v := px.reverse.append (py.concat hvy.symm)
  have hlen : wlk.length = 2 * j - 1 := by
    simp [wlk, hlenx, hleny]
    omega
  have hnot : s(x, v) ∉ wlk.edges := by
    intro hmem
    have hmem' :
        s(x, v) ∈ px.reverse.edges ∨ s(x, v) ∈ (py.concat hvy.symm).edges := by
      simpa [wlk, Walk.edges_append, List.mem_append] using hmem
    rcases hmem' with hpx | hpy
    · have : s(x, v) ∈ px.edges := by
        simpa [Walk.edges_reverse, List.mem_reverse] using hpx
      have hvsup : v ∈ px.support := Walk.snd_mem_support_of_mem_edges px this
      have : G.edist u v ≤ (j - 1 : ℕ) := by
        simpa [hlenx] using edist_le_of_mem_support G px hvsup
      have : (j : ℕ∞) ≤ (j - 1 : ℕ) := hv ▸ this
      have : j ≤ j - 1 := Nat.cast_le.mp this
      omega
    · have hmem2 :
          s(x, v) ∈ py.edges ∨ s(x, v) = s(y, v) := by
        simpa [Walk.edges_concat, List.mem_append, List.mem_singleton] using hpy
      rcases hmem2 with hpy' | heq
      · have hvsup : v ∈ py.support := Walk.snd_mem_support_of_mem_edges py hpy'
        have : G.edist u v ≤ (j - 1 : ℕ) := by
          simpa [hleny] using edist_le_of_mem_support G py hvsup
        have : (j : ℕ∞) ≤ (j - 1 : ℕ) := hv ▸ this
        have : j ≤ j - 1 := Nat.cast_le.mp this
        omega
      · have : x = y := by
          simpa [Sym2.eq_iff, hvx.ne, hvy.ne] using heq
        exact hxy this
  obtain ⟨z, c, hc, hcle⟩ := exists_cycle_of_walk_avoiding_edge G hvx.symm wlk hnot
  have : c.length ≤ 2 * t := by
    have : c.length ≤ 2 * j := by
      have : wlk.length + 1 = 2 * j := by omega
      omega
    omega
  exact not_cycle_length_le G hg hc this

/-- An edge inside layer `i < t` yields a cycle of length `≤ 2i + 1 ≤ 2t`. -/
lemma no_layer_edge {u : V} {t i : ℕ} (_hi0 : 1 ≤ i) (hit : i < t)
    {x y : V} (hxy : G.Adj x y)
    (hx : x ∈ sphere G u i) (hy : y ∈ sphere G u i)
    (hg : (2 * t + 1 : ℕ∞) ≤ G.egirth) : False := by
  rw [mem_sphere G] at hx hy
  obtain ⟨px, _, hlenx⟩ := exists_shortest_path G hx
  obtain ⟨py, _, hleny⟩ := exists_shortest_path G hy
  let wlk : G.Walk x y := px.reverse.append py
  have hlen : wlk.length = 2 * i := by
    simp [wlk, hlenx, hleny]
    omega
  have hnot : s(x, y) ∉ wlk.edges := by
    intro hmem
    have hmem' : s(x, y) ∈ px.reverse.edges ∨ s(x, y) ∈ py.edges := by
      simpa [wlk, Walk.edges_append, List.mem_append] using hmem
    rcases hmem' with hpx | hpy
    · have : s(x, y) ∈ px.edges := by
        simpa [Walk.edges_reverse, List.mem_reverse] using hpx
      exact edge_not_mem_shortest G hlenx hx hy hxy this
    · exact edge_not_mem_shortest G hleny hy hx hxy.symm (by
        simpa [Sym2.eq_swap] using hpy)
  obtain ⟨z, c, hc, hcle⟩ := exists_cycle_of_walk_avoiding_edge G hxy wlk hnot
  have : c.length ≤ 2 * t := by
    have : c.length ≤ 2 * i + 1 := by omega
    have : 2 * i + 1 ≤ 2 * t := by omega
    omega
  exact not_cycle_length_le G hg hc this

/-! ## Neighbour trichotomy at distance `i` -/

lemma neighbor_mem_adj_spheres {u v w : V} {i : ℕ}
    (hv : v ∈ sphere G u i) (hw : G.Adj v w) :
    w ∈ sphere G u (i - 1) ∨ w ∈ sphere G u i ∨ w ∈ sphere G u (i + 1) := by
  rw [mem_sphere G] at hv ⊢
  have hle : G.edist u w ≤ (i + 1 : ℕ) := by
    calc
      G.edist u w ≤ G.edist u v + G.edist v w := SimpleGraph.edist_triangle
      _ = (i : ℕ∞) + 1 := by
          rw [hv, edist_eq_one_iff_adj.mpr hw]
  have hge : (i : ℕ∞) ≤ G.edist u w + 1 := by
    calc
      (i : ℕ∞) = G.edist u v := hv.symm
      _ ≤ G.edist u w + G.edist w v := SimpleGraph.edist_triangle
      _ = G.edist u w + 1 := by rw [edist_eq_one_iff_adj.mpr hw.symm]
  have hne : G.edist u w ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.coe_ne_top (i + 1)) hle
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hne
  have hm_le : m ≤ i + 1 := by
    have := hle
    rw [← hm] at this
    exact Nat.cast_le.mp this
  have hm_ge : i ≤ m + 1 := by
    have := hge
    rw [← hm] at this
    exact Nat.cast_le.mp this
  have : m = i - 1 ∨ m = i ∨ m = i + 1 := by omega
  rcases this with h | h | h
  · left; simp [mem_sphere G, ← hm, h]
  · right; left; simp [mem_sphere G, ← hm, h]
  · right; right; simp [mem_sphere G, ← hm, h]

lemma neighborFinset_subset_adj_spheres {u v : V} {i : ℕ}
    (hv : v ∈ sphere G u i) :
    G.neighborFinset v ⊆
      sphere G u (i - 1) ∪ sphere G u i ∪ sphere G u (i + 1) := by
  intro w hw
  rw [mem_neighborFinset] at hw
  rcases neighbor_mem_adj_spheres G hv hw with h | h | h
  · exact mem_union.2 (Or.inl (mem_union.2 (Or.inl h)))
  · exact mem_union.2 (Or.inl (mem_union.2 (Or.inr h)))
  · exact mem_union.2 (Or.inr h)

/-! ## Children in the next layer -/

def children (u v : V) (i : ℕ) : Finset V :=
  (G.neighborFinset v).filter (fun w => w ∈ sphere G u (i + 1))

lemma mem_children {u v w : V} {i : ℕ} :
    w ∈ children G u v i ↔ G.Adj v w ∧ w ∈ sphere G u (i + 1) := by
  simp [children, mem_neighborFinset]

lemma children_subset_sphere {u v : V} {i : ℕ} :
    children G u v i ⊆ sphere G u (i + 1) := by
  intro w hw
  exact (mem_filter.mp hw).2

lemma parents_card_eq_one {u v : V} {t i : ℕ} (hi0 : 1 ≤ i) (hit : i ≤ t)
    (hv : v ∈ sphere G u i) (hg : (2 * t + 1 : ℕ∞) ≤ G.egirth) :
    ((G.neighborFinset v).filter (fun w => w ∈ sphere G u (i - 1))).card = 1 := by
  obtain ⟨x, hxv, hxed⟩ := exists_parent G hi0 ((mem_sphere G).mp hv)
  have hx : x ∈ (G.neighborFinset v).filter (fun w => w ∈ sphere G u (i - 1)) := by
    simp [mem_neighborFinset, mem_sphere G, hxv, hxed]
  have huniq : ∀ y ∈ (G.neighborFinset v).filter (fun w => w ∈ sphere G u (i - 1)),
      y = x := by
    intro y hy
    simp only [mem_filter, mem_neighborFinset] at hy
    by_contra hne
    exact no_two_parents G hi0 hit hv (Ne.symm hne)
      (by simpa [mem_sphere G] using hxed)
      hy.2 hxv hy.1 hg
  refine le_antisymm ?_ (Nat.succ_le_iff.mpr (card_pos.2 ⟨x, hx⟩))
  have hsub : (G.neighborFinset v).filter (fun w => w ∈ sphere G u (i - 1)) ⊆ {x} := by
    intro y hy
    simpa using huniq y hy
  exact (card_le_card hsub).trans (by simp)

lemma same_layer_empty {u v : V} {t i : ℕ} (hi0 : 1 ≤ i) (hit : i < t)
    (hv : v ∈ sphere G u i) (hg : (2 * t + 1 : ℕ∞) ≤ G.egirth) :
    (G.neighborFinset v).filter (fun w => w ∈ sphere G u i) = ∅ := by
  ext w
  simp only [mem_filter, mem_neighborFinset, not_mem_empty, iff_false, not_and]
  intro hw hw'
  exact no_layer_edge G hi0 hit hw hv hw' hg

lemma children_card_ge {k t i : ℕ} {u v : V}
    (hk : 2 ≤ k) (hδ : k ≤ G.minDegree) (hi0 : 1 ≤ i) (hit : i < t)
    (hv : v ∈ sphere G u i) (hg : (2 * t + 1 : ℕ∞) ≤ G.egirth) :
    k - 1 ≤ (children G u v i).card := by
  have hdeg : k ≤ G.degree v := le_trans hδ (G.minDegree_le_degree v)
  have hsub := neighborFinset_subset_adj_spheres G hv
  have hsplit :
      G.neighborFinset v =
        (G.neighborFinset v).filter (fun w => w ∈ sphere G u (i - 1)) ∪
          (G.neighborFinset v).filter (fun w => w ∈ sphere G u i) ∪
            children G u v i := by
    ext w
    constructor
    · intro hw
      have hw' := hsub hw
      simp only [mem_union, mem_filter, children, hw, true_and] at hw' ⊢
      exact hw'
    · intro hw
      simp only [mem_union, mem_filter, children] at hw
      rcases hw with (h | h) | h <;> exact h.1
  have hdisj₁ :
      Disjoint
        ((G.neighborFinset v).filter (fun w => w ∈ sphere G u (i - 1)))
        ((G.neighborFinset v).filter (fun w => w ∈ sphere G u i)) := by
    rw [disjoint_left]
    intro w hw1 hw2
    simp only [mem_filter] at hw1 hw2
    exact Finset.disjoint_left.mp (disjoint_sphere G (by omega : i - 1 ≠ i)) hw1.2 hw2.2
  have hdisj₂ :
      Disjoint
        (((G.neighborFinset v).filter (fun w => w ∈ sphere G u (i - 1))) ∪
          (G.neighborFinset v).filter (fun w => w ∈ sphere G u i))
        (children G u v i) := by
    rw [disjoint_union_left]
    constructor
    · rw [disjoint_left]
      intro w hw1 hw2
      simp only [mem_filter, children] at hw1 hw2
      exact Finset.disjoint_left.mp
        (disjoint_sphere G (by omega : i - 1 ≠ i + 1)) hw1.2 hw2.2
    · rw [disjoint_left]
      intro w hw1 hw2
      simp only [mem_filter, children] at hw1 hw2
      exact Finset.disjoint_left.mp
        (disjoint_sphere G (by omega : i ≠ i + 1)) hw1.2 hw2.2
  have hsame := same_layer_empty G hi0 hit hv hg
  have hpar := parents_card_eq_one G hi0 (le_of_lt hit) hv hg
  let A := (G.neighborFinset v).filter (fun w => w ∈ sphere G u (i - 1))
  let B := (G.neighborFinset v).filter (fun w => w ∈ sphere G u i)
  let C := children G u v i
  have hdegA : G.degree v = (A ∪ B ∪ C).card := by
    rw [← card_neighborFinset_eq_degree]
    exact congrArg Finset.card hsplit
  have hcards : (A ∪ B ∪ C).card = A.card + B.card + C.card := by
    rw [card_union_of_disjoint hdisj₂, card_union_of_disjoint hdisj₁]
  have hA : A.card = 1 := hpar
  have hB : B.card = 0 := by simp [B, hsame]
  have : G.degree v = 1 + (children G u v i).card := by
    calc
      G.degree v = (A ∪ B ∪ C).card := hdegA
      _ = A.card + B.card + C.card := hcards
      _ = 1 + 0 + C.card := by rw [hA, hB]
      _ = 1 + C.card := rfl
      _ = 1 + (children G u v i).card := rfl
  omega

lemma children_pairwiseDisjoint {u : V} {t i : ℕ} (hit : i < t)
    (hg : (2 * t + 1 : ℕ∞) ≤ G.egirth) :
    ∀ v ∈ sphere G u i, ∀ v' ∈ sphere G u i, v ≠ v' →
      Disjoint (children G u v i) (children G u v' i) := by
  intro v hv v' hv' hne
  rw [Finset.disjoint_left]
  intro w hw hw'
  have hw1 := (mem_children G).mp hw
  have hw2 := (mem_children G).mp hw'
  have : 1 ≤ i + 1 := Nat.succ_le_succ (Nat.zero_le _)
  exact no_two_parents G this (Nat.succ_le_iff.mpr hit) hw1.2 hne
    (by simpa [Nat.add_sub_cancel] using hv)
    (by simpa [Nat.add_sub_cancel] using hv')
    hw1.1.symm hw2.1.symm hg

lemma card_sphere_succ {k t i : ℕ} {u : V}
    (hk : 2 ≤ k) (hδ : k ≤ G.minDegree) (hi0 : 1 ≤ i) (hit : i < t)
    (hg : (2 * t + 1 : ℕ∞) ≤ G.egirth) :
    (k - 1) * (sphere G u i).card ≤ (sphere G u (i + 1)).card := by
  have hsub : (sphere G u i).biUnion (fun v => children G u v i) ⊆
      sphere G u (i + 1) := by
    intro w hw
    obtain ⟨v, _, hw'⟩ := mem_biUnion.mp hw
    exact children_subset_sphere G hw'
  have hcard := card_le_card hsub
  have hdisj := children_pairwiseDisjoint G (u := u) (t := t) (i := i) hit hg
  have hbu : ((sphere G u i).biUnion (fun v => children G u v i)).card =
      ∑ v ∈ sphere G u i, (children G u v i).card :=
    card_biUnion hdisj
  have hsum : ∑ v ∈ sphere G u i, (k - 1) ≤
      ∑ v ∈ sphere G u i, (children G u v i).card :=
    sum_le_sum fun v hv => children_card_ge G hk hδ hi0 hit hv hg
  have hconst : ∑ v ∈ sphere G u i, (k - 1) = (k - 1) * (sphere G u i).card := by
    simp [mul_comm, sum_const, nsmul_eq_mul]
  nlinarith

lemma card_sphere_one_ge {k : ℕ} {u : V} (hδ : k ≤ G.minDegree) :
    k ≤ (sphere G u 1).card := by
  rw [sphere_one, card_neighborFinset_eq_degree]
  exact le_trans hδ (G.minDegree_le_degree u)

lemma card_sphere_ge {k t : ℕ} {u : V}
    (hk : 2 ≤ k) (hδ : k ≤ G.minDegree) (ht : 1 ≤ t)
    (hg : (2 * t + 1 : ℕ∞) ≤ G.egirth) :
    ∀ i, 1 ≤ i → i ≤ t → k * (k - 1) ^ (i - 1) ≤ (sphere G u i).card := by
  intro i hi0 hit
  -- Index from 0: bound on layer (n+1) for n < t.
  have hlayers : ∀ n, n ≤ t - 1 →
      k * (k - 1) ^ n ≤ (sphere G u (n + 1)).card := by
    intro n
    induction n with
    | zero =>
      intro _
      simpa using card_sphere_one_ge G (u := u) hδ
    | succ n ih =>
      intro hn
      have hn' : n ≤ t - 1 := by omega
      have ih' := ih hn'
      have hi1 : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le _)
      have hit' : n + 1 < t := by omega
      have hsucc := card_sphere_succ G (k := k) (t := t) (i := n + 1) (u := u)
        hk hδ hi1 hit' hg
      have : k * (k - 1) ^ (n + 1) ≤ (sphere G u (n + 1 + 1)).card := by
        have : (k - 1) * (k * (k - 1) ^ n) ≤
            (k - 1) * (sphere G u (n + 1)).card :=
          Nat.mul_le_mul_left _ ih'
        have hpow : (k - 1) * (k * (k - 1) ^ n) = k * (k - 1) ^ (n + 1) := by
          ring
        nlinarith
      simpa [Nat.add_assoc] using this
  have := hlayers (i - 1) (by omega)
  simpa [Nat.sub_add_cancel hi0] using this

/-! ## Level B namesake

Fix a vertex `u`. Walks of length `≤ t` starting at `u` cannot close or
collide (any collision yields a cycle of length `≤ 2t < 2t+1 ≤ egirth`).
Branching at least `k` at `u` and at least `k−1` thereafter, the closed
ball of radius `t` therefore has at least `1 + k Σ_{i<t} (k−1)^i`
vertices.

Equality cases (`C_{2t+1}`, Petersen, Hoffman–Singleton) are comments,
not theorems. The 57-regular Moore graph is open — out of v1. -/

theorem moore_bound_odd_girth
    {k t : ℕ} (hk : 2 ≤ k) (ht : 1 ≤ t)
    (hδ : k ≤ G.minDegree)
    (hg : 2 * t + 1 ≤ G.egirth) :
    1 + k * ∑ i ∈ Finset.range t, (k - 1) ^ i ≤ Fintype.card V := by
  haveI := nonempty_of_two_le_minDegree G hk hδ
  obtain ⟨u⟩ := ‹Nonempty V›
  have hge : ∀ i ∈ range t,
      k * (k - 1) ^ i ≤ (sphere G u (i + 1)).card := by
    intro i hi
    have hi' : i + 1 ≤ t := Nat.succ_le_iff.mpr (mem_range.mp hi)
    have hcard := card_sphere_ge G (k := k) (t := t) (u := u)
      hk hδ ht hg (i + 1) (Nat.succ_le_succ (Nat.zero_le _)) hi'
    simpa [Nat.add_sub_cancel] using hcard
  have hsum :
      ∑ i ∈ range t, k * (k - 1) ^ i ≤
        ∑ i ∈ range t, (sphere G u (i + 1)).card :=
    sum_le_sum hge
  have hconst :
      ∑ i ∈ range t, k * (k - 1) ^ i = k * ∑ i ∈ range t, (k - 1) ^ i := by
    simp [mul_sum]
  have hball :
      (range (t + 1)).biUnion (sphere G u) ⊆ univ := subset_univ _
  have hcard_ball :
      ∑ i ∈ range (t + 1), (sphere G u i).card ≤ Fintype.card V := by
    have := card_le_card hball
    simpa [card_biUnion_sphere G u, card_univ] using this
  have hsplit :
      ∑ i ∈ range (t + 1), (sphere G u i).card =
        (sphere G u 0).card + ∑ i ∈ range t, (sphere G u (i + 1)).card :=
    sum_range_succ' t (fun i => (sphere G u i).card)
  calc
    1 + k * ∑ i ∈ range t, (k - 1) ^ i
        = (sphere G u 0).card + k * ∑ i ∈ range t, (k - 1) ^ i := by
            simp [card_sphere_zero G u]
    _ ≤ (sphere G u 0).card + ∑ i ∈ range t, (sphere G u (i + 1)).card :=
          Nat.add_le_add_left (hconst ▸ hsum) _
    _ = ∑ i ∈ range (t + 1), (sphere G u i).card := hsplit.symm
    _ ≤ Fintype.card V := hcard_ball

/-- `k = 2, t = 2`: min-degree ≥ 2 and girth ≥ 5 ⇒ `n ≥ 5`.
`C5` saturates (ProofLab Mycielski already has `C5`, **not** labelled
Moore). Corollary of the namesake, not a uniqueness theorem. -/
theorem moore_bound_k_two_t_two
    (hδ : 2 ≤ G.minDegree) (hg : 5 ≤ G.egirth) :
    5 ≤ Fintype.card V := by
  have h := moore_bound_odd_girth G (k := 2) (t := 2) (by decide) (by decide)
    hδ (by exact_mod_cast hg)
  -- 1 + 2 * (1^0 + 1^1) = 5
  simp at h
  exact h

/-- `k = 3, t = 2`: min-degree ≥ 3 and girth ≥ 5 ⇒ `n ≥ 10`.
Petersen tightness is a **comment**, not a uniqueness theorem. -/
theorem moore_bound_k_three_t_two
    (hδ : 3 ≤ G.minDegree) (hg : 5 ≤ G.egirth) :
    10 ≤ Fintype.card V := by
  have h := moore_bound_odd_girth G (k := 3) (t := 2) (by decide) (by decide)
    hδ (by exact_mod_cast hg)
  -- 1 + 3 * (2^0 + 2^1) = 10
  simp at h
  exact h

end ProofLab.MooreDegreeGirth
