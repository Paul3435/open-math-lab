/-
Ore 1960 — Level A only (n=3 / complete / connectedness-from-degree-sum /
longest-path neighbourhood glue). **Not labelled Ore.**

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 has `Walk.IsHamiltonian` / `IsHamiltonianCycle` /
`SimpleGraph.IsHamiltonian` / `degree` and ZERO named Ore Hamiltonian
theorem. Completing the Level A glue is the gap this ticket lands.
The Level B namesake `ore_hamiltonian` (cycle-closing under the
nonadjacent degree-sum hypothesis) is **out of this ticket** and is
**not** sorry-ed. Bondy–Chvátal closure is residual.

Pin: `catalog/problems/ore-hamiltonian/STATEMENT.md` (OPE-1100; Scout
OPE-1095 prime; Director OPE-1099). Encoding: Mathlib `IsHamiltonian` +
`degree`. Zero `sorry`. Do not import `Archive.*`.

This is **not** Dirac (`ProofLab/Dirac.lean` `dirac_hamiltonian`, PRs
#44+#45) — minDegree special case; **USE encoding**
(`isHamiltonian_complete`, longest-path dictionary), **do not re-prove
`dirac_hamiltonian`**, do not revive Dirac. This is **not**
Bondy–Chvátal / Chvátal sequence / Pósa / Tutte. This is **not**
AES Level B / ostrowski-q Level B / König matching / König
line-colouring (`bipartite-chromatic-index` leftover) / Vizing /
greedy / Brooks. This is **not** frobenius-real-division Level B /
noether-normalization Level B / krenn-gu / hou-zeng-pfc / sun-135.
Do not re-prime the consumed mill. Leave OPE-403 alone.

v1 is the undirected simple cycle theorem only. **Do not label any
theorem Ore.** `3 ≤ n` is load-bearing (`K₂` landmine). Restriction to
**nonadjacent** `u ≠ v` is load-bearing (the difference from Dirac).
`Fintype V` and `DecidableRel G.Adj` are load-bearing.

Level A: n=3 is K₃ or a path of length 2 (the path fails the
degree-sum hyp); complete graphs are Hamiltonian; degree-sum on
nonadjacent pairs ⇒ connected; a longest path P has N(u), N(v) ⊆ V(P).
**Not** labelled Ore.

Transcribed classical argument (O. Ore, Amer. Math. Monthly 67 (1960)
55; Bondy–Murty / Diestel). Compact form: Wikipedia *Ore's theorem*.
Dirac is a different consumed special case, not this claim.
-/
import ProofLab.Dirac

open Finset Function SimpleGraph

namespace ProofLab.OreHamiltonian

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

local notation "n" => Fintype.card V

/-! ## Degree-sum hypothesis (not labelled Ore) -/

/-- Nonadjacent degree-sum hypothesis. Not labelled Ore. -/
def DegreeSumOnNonadj (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ ⦃u v : V⦄, u ≠ v → ¬ G.Adj u v → n ≤ G.degree u + G.degree v

/-- Optional cheap glue (not labelled Ore, not a Dirac re-proof):
`2 * minDegree ≥ n` implies the nonadjacent degree-sum bound. -/
lemma degreeSumOnNonadj_of_minDegree (hδ : n ≤ 2 * G.minDegree) :
    DegreeSumOnNonadj G := by
  intro u v _ _
  have := Nat.add_le_add (G.minDegree_le_degree u) (G.minDegree_le_degree v)
  omega

/-! ## Level A: complete graphs (`⊤`) are Hamiltonian for `n ≥ 3`

Reuses the already-landed complete-graph encoding in `ProofLab.Dirac`
(`isHamiltonian_complete`). That lemma is **not** `dirac_hamiltonian`. -/

theorem complete_isHamiltonian (hn : 3 ≤ n) :
    (⊤ : SimpleGraph V).IsHamiltonian :=
  ProofLab.Dirac.isHamiltonian_complete hn

/-! ## Level A: `n = 3` — the path of length 2 fails the hyp; remainder is `K₃` -/

/-- If `u, v` are distinct and nonadjacent, neighbours of `u` miss both
`u` and `v`, so `deg u ≤ n - 2`. -/
lemma degree_le_card_sub_two_of_nonadj {u v : V} (hne : u ≠ v)
    (hnadj : ¬ G.Adj u v) : G.degree u ≤ n - 2 := by
  have hsub : G.neighborFinset u ⊆ (univ.erase u).erase v := by
    intro w hw
    have hadj : G.Adj u w := (mem_neighborFinset G u w).mp hw
    refine mem_erase.mpr ⟨?_, mem_erase.mpr ⟨hadj.ne.symm, mem_univ w⟩⟩
    intro h
    subst h
    exact hnadj hadj
  have hv : v ∈ univ.erase u := mem_erase.mpr ⟨hne.symm, mem_univ v⟩
  have hn2 : 2 ≤ n := by
    have hpair : ({u, v} : Finset V).card = 2 := card_pair hne
    exact hpair.symm.le.trans (card_le_card (subset_univ _))
  have hcard : ((univ.erase u).erase v).card = n - 2 := by
    rw [card_erase_of_mem hv, card_erase_of_mem (mem_univ u), card_univ]
    omega
  rw [← card_neighborFinset_eq_degree]
  exact (card_le_card hsub).trans hcard.le

lemma degree_le_one_of_nonadj_of_card_three {u v : V} (hn : n = 3)
    (hne : u ≠ v) (hnadj : ¬ G.Adj u v) : G.degree u ≤ 1 := by
  have := degree_le_card_sub_two_of_nonadj (G := G) hne hnadj
  rw [hn] at this
  simpa using this

/-- On three vertices the degree-sum hyp forbids a nonadjacent pair, so `G = ⊤`.
A path of length 2 has endpoint degrees `1+1 = 2 < 3` and fails the hyp. -/
lemma eq_top_of_card_eq_three (hn : n = 3) (hOre : DegreeSumOnNonadj G) :
    G = ⊤ := by
  ext u v
  simp only [top_adj]
  constructor
  · exact Adj.ne
  · intro hne
    by_contra hnadj
    have hu := degree_le_one_of_nonadj_of_card_three (G := G) hn hne hnadj
    have hv := degree_le_one_of_nonadj_of_card_three (G := G) hn hne.symm
      (fun h => hnadj h.symm)
    have hsum := hOre hne hnadj
    rw [hn] at hsum
    omega

/-- Degree-sum hyp on `n = 3` forces `K₃`, which is Hamiltonian.
Not labelled Ore. -/
theorem hamiltonian_of_card_eq_three (hn : n = 3) (hOre : DegreeSumOnNonadj G) :
    G.IsHamiltonian := by
  rw [eq_top_of_card_eq_three hn hOre]
  exact complete_isHamiltonian (by omega)

/-! ## Level A: degree-sum on nonadjacent pairs ⇒ connected -/

lemma neighborFinset_subset_component_erase (u : V) :
    G.neighborFinset u ⊆ (univ.filter fun w => G.Reachable u w).erase u := by
  intro w hw
  have hadj : G.Adj u w := (mem_neighborFinset G u w).mp hw
  exact mem_erase.mpr ⟨hadj.ne.symm,
    mem_filter.mpr ⟨mem_univ w, Adj.reachable hadj⟩⟩

lemma degree_le_component_pred (u : V) :
    G.degree u ≤ (univ.filter fun w => G.Reachable u w).card - 1 := by
  let C := univ.filter fun w => G.Reachable u w
  have hu : u ∈ C := mem_filter.mpr ⟨mem_univ u, Reachable.refl u⟩
  have : (C.erase u).card = C.card - 1 := card_erase_of_mem hu
  rw [← this, ← card_neighborFinset_eq_degree]
  exact card_le_card (neighborFinset_subset_component_erase u)

/-- A component missing a vertex cannot meet the nonadjacent degree-sum:
neighbours live in the component, so `deg u + deg v ≤ n - 2`.
Not labelled Ore. -/
theorem connected_of_degree_sum_on_nonadj (hn : 3 ≤ n)
    (hOre : DegreeSumOnNonadj G) : G.Connected := by
  have hpos : 0 < n := lt_of_lt_of_le (by decide : 0 < 3) hn
  haveI : Nonempty V := Fintype.card_pos_iff.mp hpos
  refine { preconnected := ?_ }
  intro u v
  by_contra hnr
  have hne : u ≠ v := fun h => hnr (h ▸ Reachable.refl u)
  have hnadj : ¬ G.Adj u v := fun h => hnr (Adj.reachable h)
  have hsum := hOre hne hnadj
  let C := univ.filter fun w => G.Reachable u w
  let D := univ.filter fun w => G.Reachable v w
  have hu : u ∈ C := mem_filter.mpr ⟨mem_univ u, Reachable.refl u⟩
  have hv : v ∈ D := mem_filter.mpr ⟨mem_univ v, Reachable.refl v⟩
  have hdisj : Disjoint C D := by
    rw [disjoint_left]
    intro x hxC hxD
    exact hnr ((mem_filter.mp hxC).2.trans (mem_filter.mp hxD).2.symm)
  have hCD : C.card + D.card ≤ n := by
    have : (C ∪ D).card = C.card + D.card := card_union_of_disjoint hdisj
    rw [← this]
    exact card_le_card (subset_univ _)
  have hdu : G.degree u ≤ C.card - 1 := degree_le_component_pred u
  have hdv : G.degree v ≤ D.card - 1 := degree_le_component_pred v
  have hCpos : 1 ≤ C.card := card_pos.mpr ⟨u, hu⟩
  have hDpos : 1 ≤ D.card := card_pos.mpr ⟨v, hv⟩
  omega

/-! ## Level A: longest-path endpoints have `N(u), N(v) ⊆ V(P)`

Reuses the longest-path *dictionary* from consumed Dirac
(`exists_longest_path`, `adj_start_mem_support_of_maximal`,
`adj_end_mem_support_of_maximal`). That dictionary is an internal tool,
**not** `dirac_hamiltonian`. Cycle-closing is Level B residual. -/

theorem neighborFinset_start_subset_longest_support {u v : V}
    {p : G.Walk u v} (hp : p.IsPath)
    (hmax : ∀ {u' v' : V} (q : G.Walk u' v'), q.IsPath → q.length ≤ p.length) :
    G.neighborFinset u ⊆ p.support.toFinset := by
  intro w hw
  exact List.mem_toFinset.mpr <|
    ProofLab.Dirac.adj_start_mem_support_of_maximal hp hmax
      ((mem_neighborFinset G u w).mp hw)

theorem neighborFinset_end_subset_longest_support {u v : V}
    {p : G.Walk u v} (hp : p.IsPath)
    (hmax : ∀ {u' v' : V} (q : G.Walk u' v'), q.IsPath → q.length ≤ p.length) :
    G.neighborFinset v ⊆ p.support.toFinset := by
  intro w hw
  exact List.mem_toFinset.mpr <|
    ProofLab.Dirac.adj_end_mem_support_of_maximal hp hmax
      ((mem_neighborFinset G v w).mp hw)

/-- Packaged Level A glue: some globally longest path has
`N(u), N(v) ⊆ V(P)`. Not labelled Ore. -/
theorem longest_path_endpoint_neighbors_subset_support (hV : Nonempty V) :
    ∃ (u v : V) (p : G.Walk u v),
      p.IsPath ∧
        (∀ {u' v' : V} (q : G.Walk u' v'), q.IsPath → q.length ≤ p.length) ∧
          G.neighborFinset u ⊆ p.support.toFinset ∧
            G.neighborFinset v ⊆ p.support.toFinset := by
  obtain ⟨u, v, p, hp, hmax⟩ := ProofLab.Dirac.exists_longest_path (G := G) hV
  exact ⟨u, v, p, hp, hmax,
    neighborFinset_start_subset_longest_support hp hmax,
    neighborFinset_end_subset_longest_support hp hmax⟩

/-- Same glue under the Level A `n ≥ 3` pin (nonempty from card). -/
theorem longest_path_endpoint_neighbors_subset_support_of_card (hn : 3 ≤ n) :
    ∃ (u v : V) (p : G.Walk u v),
      p.IsPath ∧
        (∀ {u' v' : V} (q : G.Walk u' v'), q.IsPath → q.length ≤ p.length) ∧
          G.neighborFinset u ⊆ p.support.toFinset ∧
            G.neighborFinset v ⊆ p.support.toFinset := by
  have hpos : 0 < n := lt_of_lt_of_le (by decide : 0 < 3) hn
  haveI : Nonempty V := Fintype.card_pos_iff.mp hpos
  exact longest_path_endpoint_neighbors_subset_support inferInstance

/-
Residual / out of this ticket (comment, **not** `sorry`):

Level B namesake `ore_hamiltonian`: under `DegreeSumOnNonadj` and `3 ≤ n`,
a longest path's nonadjacent endpoints force a cycle-closing index on P
(`v — xᵢ` and `u — xᵢ₊₁`); that cycle is spanning. Not landed. Not labelled
Ore in this file. Bondy–Chvátal closure is leftover-risk of this id — do
not expand. Do not re-prove `dirac_hamiltonian`.
-/

end ProofLab.OreHamiltonian
