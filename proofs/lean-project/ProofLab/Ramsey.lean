import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

open SimpleGraph Finset

namespace ProofLab.Ramsey

/-!
# Finite graph Ramsey numbers — R(3,3)=6 + lower bounds (formalize-only, OPE-44)

A red/blue edge-colouring of the complete graph `K_n` is represented by a
`SimpleGraph (Fin n)` (the "red" edges); the complement graph is "blue".

## Main definitions

* `HasClique G k`: `G` contains a `k`-clique (a set of `k` pairwise-adjacent
  vertices).
* `RamseyUpper k l n`: every red/blue colouring of `K_n` has a red `K_k` or a
  blue `K_l` (i.e. `R(k,l) ≤ n`).
* `edgeIndex`, `Red6`: certification encoding of a colouring of `K_6` by
  booleans on the 15 edges.

## Main results (zero `sorry`)

* `ramsey33_le_6` / `ramsey33_fin6`: `R(3,3) ≤ 6` (exhaustive + hand pigeonhole).
* `not_ramsey33_5` / `ramsey33_gt_5`: `R(3,3) > 5` via the 5-cycle.
* `ramsey34_gt_8`: `R(3,4) > 8` (explicit witness; lower bound only).
* `ramsey44_gt_17`: `R(4,4) > 17` (Paley-17; lower bound only).
* `ramseyUpper_swap`: colour-role symmetry.
* Support for the open upper bounds: degree-sum parity (`not_five_regular_fin9`) and
  induced Fin-6 transfer (`ramsey33_comap_embedding`, `ramsey33_on_finset`).
* **Not yet proved:** `R(3,4) ≤ 9`, `R(4,4) ≤ 18`.
-/

/-! ## Definition of the Ramsey predicate -/

/-- A graph `G` contains a `k`-clique when some set of `k` vertices is
`G`-adjacent pair by pair. -/
def HasClique (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ s : Finset V, G.IsNClique k s

/-- `R(k,l) ≤ n`: every red/blue colouring of `K_n` (red edges = `G`) has a
red `K_k` (a `k`-clique in `G`) or a blue `K_l` (an `l`-clique in `Gᶜ`). -/
def RamseyUpper (k l n : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), HasClique G k ∨ HasClique Gᶜ l

/-- Decidable form of `HasClique` once a finite graph with decidable adjacency
is given: `G` has a `k`-clique iff `G.cliqueFinset k` is nonempty. -/
lemma hasClique_iff_cliqueFinset (G : SimpleGraph V) (k : ℕ) [Fintype V]
    [DecidableEq V] [DecidableRel G.Adj] :
    HasClique G k ↔ (G.cliqueFinset k).Nonempty := by
  simp [HasClique, Finset.Nonempty, mem_cliqueFinset_iff]

/-! ## Certified enumeration of colourings of `K_6`

`Red6 r` encodes a colouring by a boolean function `r : Fin 15 → Bool` on the
15 unordered edges of `K_6`.  The edge `{u,v}` is red iff `r` holds at the
lexicographic index of the pair, where pair `(i,j)` with `0 ≤ i < j ≤ 5` is
indexed as `idx(i,j) = 5i - i(i-1)/2 + (j-1-i)`, mapping
`(0,1),(0,2),…,(0,5),(1,2),…,(4,5)` bijectively to `0..14`. -/

/-- Lexicographic index of the unordered pair `{u,v}` (used only for `u ≠ v`;
for `u = v` the value is irrelevant because graphs are loopless). -/
def edgeIndex (u v : Fin 6) : Fin 15 := by
  let i : Nat := min u.val v.val
  let j : Nat := max u.val v.val
  exact ⟨(5 * i - i * (i - 1) / 2 + (j - 1 - i)) % 15, Nat.mod_lt _ (by norm_num)⟩

/-- Adjacency of the red graph described by edge booleans `r`. -/
def red6Adj (r : Fin 15 → Bool) (u v : Fin 6) : Prop :=
  u ≠ v ∧ (r (edgeIndex u v) = true ∨ r (edgeIndex v u) = true)

/-- The red/blue colouring of `K_6` described by booleans on the 15 edges. -/
def Red6 (r : Fin 15 → Bool) : SimpleGraph (Fin 6) where
  Adj := red6Adj r
  symm := by
    intro u v h
    rcases h with ⟨hne, hrel⟩
    refine ⟨hne.symm, ?_⟩
    rcases hrel with h1 | h2
    · exact Or.inr h1
    · exact Or.inl h2
  loopless := by
    intro u hu
    exact (hu.1 rfl).elim

instance (r : Fin 15 → Bool) : DecidableRel (Red6 r).Adj := by
  unfold Red6 red6Adj
  infer_instance

/-- **R(3,3) ≤ 6**, certified: every one of the `2^15` red/blue colourings of
`K_6` has a red triangle or a blue triangle.  Zero `sorry`. -/
theorem ramsey33_le_6 :
    ∀ r : Fin 15 → Bool,
      ((Red6 r).cliqueFinset 3).Nonempty ∨ ((Red6 r)ᶜ.cliqueFinset 3).Nonempty := by
  native_decide

/-- `R(3,3) ≤ 6` in the abstract Ramsey predicate vocabulary. -/
theorem ramsey33_le_6_abs :
    ∀ r : Fin 15 → Bool, HasClique (Red6 r) 3 ∨ HasClique (Red6 r)ᶜ 3 := by
  intro r
  rw [hasClique_iff_cliqueFinset (Red6 r) 3]
  rw [hasClique_iff_cliqueFinset (Red6 r)ᶜ 3]
  exact ramsey33_le_6 r

/-! ## Lower bound: `R(3,3) > 5`

The red 5-cycle on 5 vertices is triangle-free, and its complement (also a
5-cycle) is triangle-free; so `K_5` admits a red/blue colouring with no
monochromatic triangle. -/

/-- Adjacency of the 5-cycle: `u` is adjacent to `u+1` and `u-1` (mod 5). -/
def fiveAdj (u v : Fin 5) : Prop :=
  u ≠ v ∧ ((u.val + 1) % 5 = v.val ∨ (v.val + 1) % 5 = u.val)

/-- The 5-cycle graph on `Fin 5`. -/
def FiveCycle : SimpleGraph (Fin 5) where
  Adj := fiveAdj
  symm := by
    intro u v h
    rcases h with ⟨hne, hrel⟩
    refine ⟨hne.symm, ?_⟩
    rcases hrel with h1 | h2
    · exact Or.inr h1
    · exact Or.inl h2
  loopless := by
    intro u hu
    exact (hu.1 rfl).elim

instance : DecidableRel FiveCycle.Adj := by
  unfold FiveCycle fiveAdj
  infer_instance

/-- **R(3,3) > 5**, certified: the 5-cycle colouring of `K_5` has no red
triangle and no blue triangle.  Zero `sorry`. -/
theorem not_ramsey33_5 :
    ¬(FiveCycle.cliqueFinset 3).Nonempty ∧ ¬(FiveCycleᶜ.cliqueFinset 3).Nonempty := by
  native_decide

/-- **R(3,3) > 5**, in the `RamseyUpper` vocabulary. -/
theorem ramsey33_gt_5 : ¬ RamseyUpper 3 3 5 := by
  intro h
  have hred : ¬HasClique FiveCycle 3 := by
    have hc := (not_ramsey33_5).1
    intro hcl
    exact hc (by simpa using (hasClique_iff_cliqueFinset FiveCycle 3).1 hcl)
  have hblue : ¬HasClique (FiveCycleᶜ) 3 := by
    have hc := (not_ramsey33_5).2
    intro hcl
    exact hc (by simpa using (hasClique_iff_cliqueFinset (FiveCycleᶜ) 3).1 hcl)
  rcases h FiveCycle with hcor | hcor
  · exact hred hcor
  · exact hblue hcor

/-! ## Certified lower-bound witnesses

The R(3,3)>5 witness above was hand-constructed (the 5-cycle).  The lower
bounds R(3,4)>8 and R(4,4)>17 use concrete explicit colourings that are
certified by exhaustive decision (`native_decide`): each is a *single* finite
graph, so `native_decide` enumerates its (small) set of cliques and closes the
goal with no `sorry`. -/

/-- Red pairs of a (3,4)-Ramsey colouring of `K_8`: triangle-free, complement
`K_4`-free (verified by the theorem below).  Found by random search; 10 edges. -/
def red34Pairs : List (Nat × Nat) :=
  [(0,4), (0,5), (1,2), (1,5), (1,6), (2,3), (2,4), (3,5), (3,7), (6,7)]

/-- Red adjacency of the (3,4;8) witness: `u` red-adjacent to `v` iff the
unordered pair `{u,v}` is in `red34Pairs`. -/
def red34Adj (u v : Fin 8) : Prop :=
  u ≠ v ∧ ((u.val, v.val) ∈ red34Pairs ∨ (v.val, u.val) ∈ red34Pairs)

/-- The `K_8` colouring witnessing `R(3,4) > 8` (red = this graph). -/
def Ramsey34Wit : SimpleGraph (Fin 8) where
  Adj := red34Adj
  symm := by
    intro u v h
    rcases h with ⟨hne, hrel⟩
    refine ⟨hne.symm, ?_⟩
    rcases hrel with h1 | h2
    · exact Or.inr h1
    · exact Or.inl h2
  loopless := by
    intro u hu
    exact (hu.1 rfl).elim

instance : DecidableRel (Ramsey34Wit.Adj) := by
  unfold Ramsey34Wit red34Adj
  infer_instance

/-- **R(3,4) > 8**, certified: the witness colouring of `K_8` has no red
triangle and no blue `K_4`.  Zero `sorry`. -/
theorem not_ramsey34_8 :
    ¬(Ramsey34Wit.cliqueFinset 3).Nonempty ∧ ¬(Ramsey34Witᶜ.cliqueFinset 4).Nonempty := by
  native_decide

/-- **R(3,4) > 8** in the `RamseyUpper` vocabulary. -/
theorem ramsey34_gt_8 : ¬ RamseyUpper 3 4 8 := by
  intro h
  have hred : ¬HasClique Ramsey34Wit 3 := by
    have hc := (not_ramsey34_8).1
    intro hcl
    exact hc (by simpa using (hasClique_iff_cliqueFinset Ramsey34Wit 3).1 hcl)
  have hblue : ¬HasClique (Ramsey34Witᶜ) 4 := by
    have hc := (not_ramsey34_8).2
    intro hcl
    exact hc (by simpa using (hasClique_iff_cliqueFinset (Ramsey34Witᶜ) 4).1 hcl)
  rcases h Ramsey34Wit with hcor | hcor
  · exact hred hcor
  · exact hblue hcor

/-- Quadratic-residue neighbours in `ℤ/17`: the Paley graph on `Fin 17`.  The
Paley(17) graph is self-complementary and both it and its complement are
`K_4`-free, so it witnesses `R(4,4) > 17`. -/
def paley17QR : List Nat := [1, 2, 4, 8, 9, 13, 15, 16]

/-- Distance `(v - u) mod 17` in `[0,16]`. -/
def paleyDist (u v : Fin 17) : Nat := (17 + v.val - u.val) % 17

/-- Paley-17 adjacency: `u` red-adjacent to `v` iff their (signed) difference
mod 17 is a quadratic residue.  The residue set is closed under negation, so
checking both orientations makes the relation manifestly symmetric. -/
def paley17Adj (u v : Fin 17) : Prop :=
  u ≠ v ∧ (paleyDist u v ∈ paley17QR ∨ paleyDist v u ∈ paley17QR)

/-- The `K_17` colouring witnessing `R(4,4) > 17`. -/
def Ramsey44Wit : SimpleGraph (Fin 17) where
  Adj := paley17Adj
  symm := by
    intro u v h
    rcases h with ⟨hne, hrel⟩
    exact ⟨hne.symm, by simpa [or_comm] using hrel⟩
  loopless := by
    intro u hu
    exact (hu.1 rfl).elim

instance : DecidableRel (Ramsey44Wit.Adj) := by
  unfold Ramsey44Wit paley17Adj
  infer_instance

/-- **R(4,4) > 17**, certified: the Paley-17 colouring of `K_17` has no red
`K_4` and no blue `K_4`.  Zero `sorry`. -/
theorem not_ramsey44_17 :
    ¬(Ramsey44Wit.cliqueFinset 4).Nonempty ∧ ¬(Ramsey44Witᶜ.cliqueFinset 4).Nonempty := by
  native_decide

/-- **R(4,4) > 17** in the `RamseyUpper` vocabulary. -/
theorem ramsey44_gt_17 : ¬ RamseyUpper 4 4 17 := by
  intro h
  have hred : ¬HasClique Ramsey44Wit 4 := by
    have hc := (not_ramsey44_17).1
    intro hcl
    exact hc (by simpa using (hasClique_iff_cliqueFinset Ramsey44Wit 4).1 hcl)
  have hblue : ¬HasClique (Ramsey44Witᶜ) 4 := by
    have hc := (not_ramsey44_17).2
    intro hcl
    exact hc (by simpa using (hasClique_iff_cliqueFinset (Ramsey44Witᶜ) 4).1 hcl)
  rcases h Ramsey44Wit with hcor | hcor
  · exact hred hcor
  · exact hblue hcor

/-- Exchange the two colour roles: since `(Gᶜ)ᶜ = G`, an `l`-clique on the blue
(complement) side of `G` is a `k`-clique on the red side once colours are
swapped.  Hence `RamseyUpper k l n` and `RamseyUpper l k n` are equivalent (so,
in particular, `R(4,3) = R(3,4)`). -/
theorem ramseyUpper_swap (k l n : ℕ) : RamseyUpper k l n ↔ RamseyUpper l k n := by
  constructor
  · intro h G
    rcases h Gᶜ with hk | hl
    · exact Or.inr hk
    · exact Or.inl (by simpa using hl)
  · intro h G
    rcases h Gᶜ with hl | hk
    · exact Or.inr hl
    · exact Or.inl (by simpa using hk)

/-- Extract three pairwise-distinct elements from a Finset of card ≥ 3. -/
lemma extract3 {α : Type*} [DecidableEq α] {s : Finset α} (h : 3 ≤ s.card) :
    ∃ a b c : α, a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  classical
  have hpos1 : 0 < s.card := by omega
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos1
  have he1 : (s.erase a).card = s.card - 1 := Finset.card_erase_of_mem ha
  have hge2 : 2 ≤ (s.erase a).card := by rw [he1]; omega
  have hpos2 : 0 < (s.erase a).card := by omega
  obtain ⟨b, hb⟩ := Finset.card_pos.mp hpos2
  have hb_mem : b ∈ s := mem_of_mem_erase hb
  have hb_ne_a : b ≠ a := (Finset.mem_erase.mp hb).1
  have he2 : ((s.erase a).erase b).card = (s.erase a).card - 1 := Finset.card_erase_of_mem hb
  have hge1 : 1 ≤ ((s.erase a).erase b).card := by rw [he2]; omega
  have hpos3 : 0 < ((s.erase a).erase b).card := by omega
  obtain ⟨c, hc⟩ := Finset.card_pos.mp hpos3
  have hc_mem_erase2 : c ∈ (s.erase a).erase b := hc
  have hc_mem : c ∈ s := mem_of_mem_erase (mem_of_mem_erase hc_mem_erase2)
  have hc_ne_b : c ≠ b := (Finset.mem_erase.mp hc_mem_erase2).1
  have hc_in_erase_a : c ∈ s.erase a := (Finset.mem_erase.mp hc_mem_erase2).2
  have hc_ne_a : c ≠ a := (Finset.mem_erase.mp hc_in_erase_a).1
  exact ⟨a, b, c, ha, hb_mem, hc_mem, hb_ne_a.symm, hc_ne_a.symm, hc_ne_b.symm⟩

/-- Three explicit pairwise-adjacent vertices build a 3-clique. -/
lemma clique3_of_adj {V : Type*} [DecidableEq V] (G : SimpleGraph V) {a b c : V}
    (hne1 : a ≠ b) (hne2 : a ≠ c) (hne3 : b ≠ c)
    (h1 : G.Adj a b) (h2 : G.Adj a c) (h3 : G.Adj b c) :
    HasClique G 3 := by
  refine ⟨{a, b, c}, ?_⟩
  rw [SimpleGraph.isNClique_iff]
  constructor
  · -- G.IsClique {a,b,c} : pairwise adjacency
    intro x hx y hy hxy
    simp at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> simp_all
      <;> try (apply G.symm <;> simp_all)
  · simp [hne1, hne2, hne3]

/-- **R(3,3) ≤ 6, hand pigeonhole**: any red/blue colouring of `K_6` has a
red triangle or a blue triangle.  Pick a vertex `z`; of its 5 other vertices at
least 3 share a colour to `z`; if two of those share an edge the colour-mate of
`z` closes a monochromatic triangle, else all are pairwise the other colour and
form a monochromatic triangle among themselves. -/
theorem ramsey33_fin6 : ∀ G : SimpleGraph (Fin 6), HasClique G 3 ∨ HasClique Gᶜ 3 := by
  classical
  intro G
  let z : Fin 6 := 0
  let R : Finset (Fin 6) := Finset.univ.filter (fun u => G.Adj z u)
  let B : Finset (Fin 6) := Finset.univ.filter (fun u => u ≠ z ∧ ¬ G.Adj z u)
  -- R and B are disjoint and R ∪ B = univ \ {z}, so R.card + B.card = 5
  have hdisj : Disjoint R B := by
    rw [Finset.disjoint_left]
    intro u huR huB
    rw [Finset.mem_filter] at huR huB
    exact (huB.2.2) huR.2
  have hRB : R ∪ B = Finset.univ.erase z := by
    ext u
    by_cases hz : u = z
    · subst u
      simp [R, B]
    · simp [R, B, hz]
      by_cases h : G.Adj z u
      · simp [h]
      · simp [h]
  have hcard : R.card + B.card = 5 := by
    have hc := Finset.card_union_of_disjoint hdisj
    have hzmem : z ∈ (Finset.univ : Finset (Fin 6)) := by simp
    have hez : (Finset.univ.erase z).card = 5 := by
      rw [Finset.card_erase_of_mem hzmem]
      norm_num
    rw [← hc, hRB]
    exact hez
  -- pigeonhole: at least 3 of the 5 neighbours share a colour with z
  by_cases hR : 3 ≤ R.card
  · -- three red neighbours a,b,c of z
    rcases extract3 hR with ⟨a, b, c, haR, hbR, hcR, hab, hac, hbc⟩
    have hzaA : G.Adj z a := by simpa [R] using haR
    have hzbA : G.Adj z b := by simpa [R] using hbR
    have hzcA : G.Adj z c := by simpa [R] using hcR
    have hza : z ≠ a := G.ne_of_adj hzaA
    have hzb : z ≠ b := G.ne_of_adj hzbA
    have hzc : z ≠ c := G.ne_of_adj hzcA
    by_cases h1 : G.Adj a b
    · left; exact clique3_of_adj G hza hzb hab hzaA hzbA h1
    · by_cases h2 : G.Adj a c
      · left; exact clique3_of_adj G hza hzc hac hzaA hzcA h2
      · by_cases h3 : G.Adj b c
        · left; exact clique3_of_adj G hzb hzc hbc hzbA hzcA h3
        · right; exact clique3_of_adj (Gᶜ) hab hac hbc (by simpa [h1]) (by simpa [h2]) (by simpa [h3])
  · -- at most 2 red neighbours, so at least 3 blue neighbours (≠z)
    have hB : 3 ≤ B.card := by omega
    rcases extract3 hB with ⟨a, b, c, haB, hbB, hcB, hab, hac, hbc⟩
    have haA : ¬G.Adj z a := (Finset.mem_filter.mp haB).2.2
    have hbA : ¬G.Adj z b := (Finset.mem_filter.mp hbB).2.2
    have hcA : ¬G.Adj z c := (Finset.mem_filter.mp hcB).2.2
    have hza : z ≠ a := (Finset.mem_filter.mp haB).2.1.symm
    have hzb : z ≠ b := (Finset.mem_filter.mp hbB).2.1.symm
    have hzc : z ≠ c := (Finset.mem_filter.mp hcB).2.1.symm
    have hzaC : (Gᶜ).Adj z a := by simpa [haA]
    have hzbC : (Gᶜ).Adj z b := by simpa [hbA]
    have hzcC : (Gᶜ).Adj z c := by simpa [hcA]
    by_cases h1 : ¬ G.Adj a b
    · right; exact clique3_of_adj (Gᶜ) hza hzb hab hzaC hzbC (by simpa [h1])
    · by_cases h2 : ¬ G.Adj a c
      · right; exact clique3_of_adj (Gᶜ) hza hzc hac hzaC hzcC (by simpa [h2])
      · by_cases h3 : ¬ G.Adj b c
        · right; exact clique3_of_adj (Gᶜ) hzb hzc hbc hzbC hzcC (by simpa [h3])
        · left; exact clique3_of_adj G hab hac hbc
            (Classical.not_not.mp h1) (Classical.not_not.mp h2) (Classical.not_not.mp h3)

/-! ## Support lemmas for the R(3,4) ≤ 9 degree-parity hand proof

The classical argument needs:
1. **degree-sum / handshake** — `∑ degree = 2 · #edges` is even, so a 5-regular
   colouring on 9 vertices is impossible (sum 45 odd).
2. **induced Fin-6 transfer** — if a colouring of `K_n` has a 6-vertex set `S`,
   the induced colouring on `S` inherits `R(3,3) ≤ 6` from `ramsey33_fin6`
   (via pullback along an embedding `Fin 6 ↪ V`), and monochromatic triangles
   on `S` push forward to monochromatic triangles in the ambient graph.

These lemmas do **not** yet close `RamseyUpper 3 4 9`; they only factor the
reusable infrastructure. Zero `sorry`. -/

/-- Degree-sum formula specialized: the sum of degrees is always even. -/
theorem sum_degrees_even {V : Type*} (G : SimpleGraph V) [Fintype V]
    [DecidableRel G.Adj] [Fintype (Sym2 V)] :
    Even (∑ v : V, G.degree v) := by
  rw [G.sum_degrees_eq_twice_card_edges]
  exact even_two_mul _

/-- If every vertex has the same degree `d`, the degree sum is `#V * d`. -/
theorem sum_degrees_of_regular {V : Type*} (G : SimpleGraph V) [Fintype V]
    [DecidableRel G.Adj] (d : ℕ) (h : ∀ v : V, G.degree v = d) :
    ∑ v : V, G.degree v = Fintype.card V * d := by
  simp [h]

/-- Handshake parity obstruction: no graph on an odd number of vertices can be
regular of odd degree (classical step 3 of the R(3,4)≤9 proof: 9 · 5 = 45). -/
theorem not_regular_odd_of_odd_card {V : Type*} (G : SimpleGraph V) [Fintype V]
    [DecidableRel G.Adj] [Fintype (Sym2 V)] (d : ℕ)
    (hcard : Odd (Fintype.card V)) (hd : Odd d)
    (hreg : ∀ v : V, G.degree v = d) : False := by
  have hsum := sum_degrees_even G
  rw [sum_degrees_of_regular G d hreg] at hsum
  exact Nat.odd_iff_not_even.mp (Odd.mul hcard hd) hsum

/-- Concrete form used by the R(3,4)≤9 plan: no 5-regular simple graph on
`Fin 9` (would force blue-degree sum 45, odd). -/
theorem not_five_regular_fin9 (G : SimpleGraph (Fin 9)) [DecidableRel G.Adj]
    (h : ∀ v : Fin 9, G.degree v = 5) : False := by
  haveI : Fintype (Sym2 (Fin 9)) := inferInstance
  exact not_regular_odd_of_odd_card G 5 (by decide) (by decide) h

/-- Complement degrees: blue-degree = n − 1 − red-degree (Mathlib `degree_compl`). -/
theorem degree_compl_fin {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    [DecidableEq (Fin n)] (v : Fin n) :
    Gᶜ.degree v = n - 1 - G.degree v := by
  simpa using (G.degree_compl (v := v))

/-- Pulling adjacency back along an injective map preserves the complement:
`(G.comap f)ᶜ = Gᶜ.comap f`. -/
theorem comap_compl_eq_of_injective {V W : Type*} (f : V ↪ W) (G : SimpleGraph W) :
    (G.comap f)ᶜ = Gᶜ.comap f := by
  ext a b
  simp only [compl_adj, comap_adj]
  constructor
  · rintro ⟨hne, hna⟩
    exact ⟨fun h => hne (f.injective h), hna⟩
  · rintro ⟨hne, hna⟩
    exact ⟨fun h => hne (by simp [h]), hna⟩

/-- A `k`-clique in a pullback graph pushes forward along the embedding to a
`k`-clique in the ambient graph. -/
theorem hasClique_of_hasClique_comap {V W : Type*} [DecidableEq V] [DecidableEq W]
    (f : V ↪ W) (G : SimpleGraph W) {k : ℕ}
    (h : HasClique (G.comap f) k) : HasClique G k := by
  obtain ⟨s, hs⟩ := h
  refine ⟨s.map f, ?_⟩
  rw [isNClique_iff] at hs ⊢
  refine ⟨?_, by simp [hs.2]⟩
  intro x hx y hy hxy
  rcases Finset.mem_map.mp hx with ⟨a, ha, rfl⟩
  rcases Finset.mem_map.mp hy with ⟨b, hb, rfl⟩
  have hab : a ≠ b := fun h => hxy (by simp [h])
  have hadj : (G.comap f).Adj a b := hs.1 ha hb hab
  simpa [comap_adj] using hadj

/-- **Induced Fin-6 transfer**: any pullback of a colouring along `Fin 6 ↪ V`
has a monochromatic triangle (red or blue), by `ramsey33_fin6`. -/
theorem ramsey33_comap_embedding {V : Type*} (G : SimpleGraph V) (f : Fin 6 ↪ V)
    [DecidableRel G.Adj] :
    HasClique (G.comap f) 3 ∨ HasClique (Gᶜ.comap f) 3 := by
  classical
  have h := ramsey33_fin6 (G.comap f)
  rwa [comap_compl_eq_of_injective f G] at h

/-- Same transfer, pushing the monochromatic triangle into the ambient graph. -/
theorem hasMonoTriangle3_of_embedding {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (f : Fin 6 ↪ V) [DecidableRel G.Adj] :
    HasClique G 3 ∨ HasClique Gᶜ 3 := by
  classical
  rcases ramsey33_comap_embedding G f with h | h
  · exact Or.inl (hasClique_of_hasClique_comap f G h)
  · exact Or.inr (hasClique_of_hasClique_comap f Gᶜ h)

/-- **Finset form**: any 6-vertex set in a linearly ordered vertex type induces
a monochromatic triangle under any red/blue colouring (via `orderEmbOfFin`). -/
theorem ramsey33_on_finset {V : Type*} [LinearOrder V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (hS : S.card = 6) :
    HasClique G 3 ∨ HasClique Gᶜ 3 := by
  classical
  exact hasMonoTriangle3_of_embedding G (S.orderEmbOfFin hS).toEmbedding

/-- Specialization: a 6-element finset of `Fin n` yields a monochromatic
triangle. Used when the blue-neighbourhood of a vertex in `K_9` has size ≥ 6. -/
theorem ramsey33_on_finset_fin {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) (hS : S.card = 6) :
    HasClique G 3 ∨ HasClique Gᶜ 3 :=
  ramsey33_on_finset G S hS

/-- Monochromatic triangle **inside** a 6-set (keeps the clique as a subset so
it can be extended by a common neighbour). -/
theorem ramsey33_clique_inside_finset {V : Type*} [LinearOrder V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (hS : S.card = 6) :
    (∃ t ⊆ S, G.IsNClique 3 t) ∨ (∃ t ⊆ S, Gᶜ.IsNClique 3 t) := by
  classical
  let f : Fin 6 ↪ V := (S.orderEmbOfFin hS).toEmbedding
  have f_mem : ∀ i, f i ∈ S := fun i => by
    -- orderEmbOfFin lands in S
    simpa using Finset.orderEmbOfFin_mem S hS i
  rcases ramsey33_fin6 (G.comap f) with h | h
  · left
    obtain ⟨s, hs⟩ := h
    refine ⟨s.map f, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_map.mp hx with ⟨i, _, rfl⟩
      exact f_mem i
    · rw [isNClique_iff] at hs ⊢
      refine ⟨?_, by simp [hs.2]⟩
      intro x hx y hy hxy
      rcases Finset.mem_map.mp hx with ⟨a, ha, rfl⟩
      rcases Finset.mem_map.mp hy with ⟨b, hb, rfl⟩
      have hab : a ≠ b := fun e => hxy (by simp [e])
      have hadj : (G.comap f).Adj a b := hs.1 ha hb hab
      simpa [comap_adj] using hadj
  · right
    -- h : HasClique (G.comap f)ᶜ 3; rewrite to Gᶜ.comap f
    have h' : HasClique (Gᶜ.comap f) 3 := by
      rwa [← comap_compl_eq_of_injective f G]
    obtain ⟨s, hs⟩ := h'
    refine ⟨s.map f, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_map.mp hx with ⟨i, _, rfl⟩
      exact f_mem i
    · rw [isNClique_iff] at hs ⊢
      refine ⟨?_, by simp [hs.2]⟩
      intro x hx y hy hxy
      rcases Finset.mem_map.mp hx with ⟨a, ha, rfl⟩
      rcases Finset.mem_map.mp hy with ⟨b, hb, rfl⟩
      have hab : a ≠ b := fun e => hxy (by simp [e])
      have hadj : (Gᶜ.comap f).Adj a b := hs.1 ha hb hab
      simpa [comap_adj] using hadj

/-- Extract four pairwise-distinct elements from a Finset of card ≥ 4. -/
lemma extract4 {α : Type*} [DecidableEq α] {s : Finset α} (h : 4 ≤ s.card) :
    ∃ a b c d : α,
      a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ d ∈ s ∧
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  classical
  have h3 : 3 ≤ s.card := by omega
  rcases extract3 h3 with ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩
  have hsub : ({a, b, c} : Finset α) ⊆ s := by
    intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> assumption
  have hc3 : ({a, b, c} : Finset α).card = 3 := by
    simp [hab, hac, hbc]
  have hrest : 1 ≤ (s \ {a, b, c}).card := by
    have hcard := card_sdiff hsub
    omega
  have hpos : 0 < (s \ {a, b, c}).card := by omega
  obtain ⟨d, hd⟩ := Finset.card_pos.mp hpos
  have hd_mem : d ∈ s := (mem_sdiff.mp hd).1
  have hd_not : d ∉ ({a, b, c} : Finset α) := (mem_sdiff.mp hd).2
  have hne : d ≠ a ∧ d ≠ b ∧ d ≠ c := by
    simpa using hd_not
  exact ⟨a, b, c, d, ha, hb, hc, hd_mem, hab, hac, hne.1.symm, hbc, hne.2.1.symm, hne.2.2.symm⟩

/-- Four pairwise-adjacent vertices form a 4-clique. -/
lemma clique4_of_adj {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    {a b c d : V}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (eab : G.Adj a b) (eac : G.Adj a c) (ead : G.Adj a d)
    (ebc : G.Adj b c) (ebd : G.Adj b d) (ecd : G.Adj c d) :
    HasClique G 4 := by
  refine ⟨{a, b, c, d}, ?_⟩
  rw [isNClique_iff]
  constructor
  · intro x hx y hy hxy
    simp at hx hy
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      first
      | exact (hxy rfl).elim
      | assumption
      | apply G.symm; assumption
  · simp [hab, hac, had, hbc, hbd, hcd]

/-- Insert a common neighbour onto an `n`-clique to get an `(n+1)`-clique. -/
lemma hasClique_insert_common {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    {v : V} {n : ℕ} {t : Finset V} (ht : G.IsNClique n t)
    (hv : ∀ x ∈ t, G.Adj v x) : HasClique G (n + 1) :=
  ⟨insert v t, ht.insert hv⟩

/-! ## R(3,4) ≤ 9 by degree parity -/

/-- In a red-triangle-free / blue-`K_4`-free colouring of `K_9`, every red
degree is ≤ 3. -/
lemma red_degree_le_three_of_no_cliques (G : SimpleGraph (Fin 9))
    [DecidableRel G.Adj]
    (hno3 : ¬ HasClique G 3) (hno4 : ¬ HasClique Gᶜ 4) (v : Fin 9) :
    G.degree v ≤ 3 := by
  classical
  by_contra hgt
  have hge : 4 ≤ G.degree v := by omega
  have hN : 4 ≤ (G.neighborFinset v).card := by
    simpa [card_neighborFinset_eq_degree] using hge
  rcases extract4 hN with ⟨a, b, c, d, ha, hb, hc, hd, hab, hac, had, hbc, hbd, hcd⟩
  have hva : G.Adj v a := (mem_neighborFinset _ _).mp ha
  have hvb : G.Adj v b := (mem_neighborFinset _ _).mp hb
  have hvc : G.Adj v c := (mem_neighborFinset _ _).mp hc
  have hvd : G.Adj v d := (mem_neighborFinset _ _).mp hd
  by_cases eab : G.Adj a b
  · exact hno3 (clique3_of_adj G (G.ne_of_adj hva) (G.ne_of_adj hvb) hab hva hvb eab)
  by_cases eac : G.Adj a c
  · exact hno3 (clique3_of_adj G (G.ne_of_adj hva) (G.ne_of_adj hvc) hac hva hvc eac)
  by_cases ead : G.Adj a d
  · exact hno3 (clique3_of_adj G (G.ne_of_adj hva) (G.ne_of_adj hvd) had hva hvd ead)
  by_cases ebc : G.Adj b c
  · exact hno3 (clique3_of_adj G (G.ne_of_adj hvb) (G.ne_of_adj hvc) hbc hvb hvc ebc)
  by_cases ebd : G.Adj b d
  · exact hno3 (clique3_of_adj G (G.ne_of_adj hvb) (G.ne_of_adj hvd) hbd hvb hvd ebd)
  by_cases ecd : G.Adj c d
  · exact hno3 (clique3_of_adj G (G.ne_of_adj hvc) (G.ne_of_adj hvd) hcd hvc hvd ecd)
  exact hno4 (clique4_of_adj (Gᶜ) hab hac had hbc hbd hcd
    (by simpa [eab]) (by simpa [eac]) (by simpa [ead])
    (by simpa [ebc]) (by simpa [ebd]) (by simpa [ecd]))

/-- In a red-triangle-free / blue-`K_4`-free colouring of `K_9`, every blue
degree is ≤ 5. -/
lemma blue_degree_le_five_of_no_cliques (G : SimpleGraph (Fin 9))
    [DecidableRel G.Adj]
    (hno3 : ¬ HasClique G 3) (hno4 : ¬ HasClique Gᶜ 4) (v : Fin 9) :
    Gᶜ.degree v ≤ 5 := by
  classical
  by_contra hgt
  have hge : 6 ≤ Gᶜ.degree v := by omega
  have hN : 6 ≤ (Gᶜ.neighborFinset v).card := by
    simpa [card_neighborFinset_eq_degree] using hge
  obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hN
  rcases ramsey33_clique_inside_finset G S hScard with hred | hblue
  · rcases hred with ⟨t, _, ht⟩
    exact hno3 ⟨t, ht⟩
  · rcases hblue with ⟨t, ht_sub, ht⟩
    have hv_adj : ∀ x ∈ t, Gᶜ.Adj v x := by
      intro x hx
      have hxS : x ∈ S := ht_sub hx
      have hxN : x ∈ Gᶜ.neighborFinset v := hSsub hxS
      exact (mem_neighborFinset _ _).mp hxN
    exact hno4 (hasClique_insert_common (Gᶜ) ht hv_adj)

/-- **R(3,4) ≤ 9**: every red/blue colouring of `K_9` has a red triangle or a
blue `K_4`. -/
theorem ramsey34_le_9 : RamseyUpper 3 4 9 := by
  classical
  intro G
  letI : DecidableRel G.Adj := Classical.decRel _
  by_cases h3 : HasClique G 3
  · exact Or.inl h3
  by_cases h4 : HasClique Gᶜ 4
  · exact Or.inr h4
  have hred : ∀ v, G.degree v ≤ 3 := fun v =>
    red_degree_le_three_of_no_cliques G h3 h4 v
  have hblue_le : ∀ v, Gᶜ.degree v ≤ 5 := fun v =>
    blue_degree_le_five_of_no_cliques G h3 h4 v
  have hsum : ∀ v, G.degree v + Gᶜ.degree v = 8 := by
    intro v
    have hdc := degree_compl_fin G v
    omega
  have hblue_eq : ∀ v, Gᶜ.degree v = 5 := by
    intro v
    have := hsum v
    have := hred v
    have := hblue_le v
    omega
  exact (not_five_regular_fin9 (Gᶜ) hblue_eq).elim

/-- **R(3,4) = 9** as a pair of bounds (`> 8` and `≤ 9`). -/
theorem ramsey34_eq_9 : (¬ RamseyUpper 3 4 8) ∧ RamseyUpper 3 4 9 :=
  ⟨ramsey34_gt_8, ramsey34_le_9⟩

/-! ## Transfer of `RamseyUpper` onto arbitrary finsets / types -/

/-- `RamseyUpper k l n` lifts along any type of cardinality `n`. -/
theorem ramseyUpper_of_card {k l n : ℕ} (hR : RamseyUpper k l n)
    {V : Type*} [Fintype V] [DecidableEq V] (hcard : Fintype.card V = n)
    (G : SimpleGraph V) : HasClique G k ∨ HasClique Gᶜ l := by
  classical
  let e : V ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let f : Fin n ↪ V := e.symm.toEmbedding
  let G0 : SimpleGraph (Fin n) := G.comap f
  rcases hR G0 with hk | hl
  · exact Or.inl (hasClique_of_hasClique_comap f G hk)
  · have hl' : HasClique (Gᶜ.comap f) l := by
      rwa [← comap_compl_eq_of_injective f G]
    exact Or.inr (hasClique_of_hasClique_comap f Gᶜ hl')

/-- Clique-inside form of `RamseyUpper` on an `n`-element finset. -/
theorem ramseyUpper_clique_inside_finset {k l n : ℕ} (hR : RamseyUpper k l n)
    {V : Type*} [LinearOrder V] [DecidableEq V]
    (S : Finset V) (hS : S.card = n) (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∃ t ⊆ S, G.IsNClique k t) ∨ (∃ t ⊆ S, Gᶜ.IsNClique l t) := by
  classical
  let f : Fin n ↪ V := (S.orderEmbOfFin hS).toEmbedding
  have f_mem : ∀ i, f i ∈ S := fun i => by
    simpa using Finset.orderEmbOfFin_mem S hS i
  let G0 : SimpleGraph (Fin n) := G.comap f
  rcases hR G0 with hk | hl
  · left
    obtain ⟨s, hs⟩ := hk
    refine ⟨s.map f, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_map.mp hx with ⟨i, _, rfl⟩
      exact f_mem i
    · rw [isNClique_iff] at hs ⊢
      refine ⟨?_, by simp [hs.2]⟩
      intro x hx y hy hxy
      rcases Finset.mem_map.mp hx with ⟨a, ha, rfl⟩
      rcases Finset.mem_map.mp hy with ⟨b, hb, rfl⟩
      have hab : a ≠ b := fun e => hxy (by simp [e])
      have hadj : G0.Adj a b := hs.1 ha hb hab
      simpa [G0, comap_adj] using hadj
  · right
    have hl' : HasClique (Gᶜ.comap f) l := by
      rwa [← comap_compl_eq_of_injective f G]
    obtain ⟨s, hs⟩ := hl'
    refine ⟨s.map f, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_map.mp hx with ⟨i, _, rfl⟩
      exact f_mem i
    · rw [isNClique_iff] at hs ⊢
      refine ⟨?_, by simp [hs.2]⟩
      intro x hx y hy hxy
      rcases Finset.mem_map.mp hx with ⟨a, ha, rfl⟩
      rcases Finset.mem_map.mp hy with ⟨b, hb, rfl⟩
      have hab : a ≠ b := fun e => hxy (by simp [e])
      have hadj : (Gᶜ.comap f).Adj a b := hs.1 ha hb hab
      simpa [comap_adj] using hadj

/-! ## Classical recurrence R(k,l) ≤ R(k-1,l) + R(k,l-1) -/

/-- The classical Ramsey recurrence. -/
theorem ramseyUpper_add {k l a b : ℕ}
    (hk : 2 ≤ k) (hl : 2 ≤ l)
    (ha : RamseyUpper (k - 1) l a) (hb : RamseyUpper k (l - 1) b) :
    RamseyUpper k l (a + b) := by
  classical
  intro G
  letI : DecidableRel G.Adj := Classical.decRel _
  let v : Fin (a + b) := ⟨0, by omega⟩
  let R := G.neighborFinset v
  let B := Gᶜ.neighborFinset v
  have hdisj : Disjoint R B := by
    rw [disjoint_left]
    intro x hxR hxB
    have h1 := (mem_neighborFinset G v x).mp hxR
    have h2 := (mem_neighborFinset Gᶜ v x).mp hxB
    simp [compl_adj] at h2
    exact h2.2 h1
  have hcard_sum : R.card + B.card = a + b - 1 := by
    have hzmem : v ∈ (univ : Finset (Fin (a + b))) := mem_univ v
    have hez : ((univ : Finset (Fin (a + b))).erase v).card = a + b - 1 := by
      rw [card_erase_of_mem hzmem, card_univ, Fintype.card_fin]
    have hRB : R ∪ B = (univ : Finset (Fin (a + b))).erase v := by
      ext x
      by_cases hx : x = v
      · subst x
        simp [R, B, mem_neighborFinset, SimpleGraph.irrefl]
      · have hxv : x ≠ v := hx
        simp [R, B, mem_neighborFinset, compl_adj, hxv, Ne.symm hxv]
        constructor
        · intro h
          cases h with
          | inl hr => exact Or.inl hr
          | inr hb' => exact Or.inr hb'.2
        · intro h
          cases h with
          | inl hr => exact Or.inl hr
          | inr hb' => exact Or.inr ⟨Ne.symm hxv, hb'⟩
    have hc := card_union_of_disjoint hdisj
    rw [← hc, hRB, hez]
  by_cases hRge : a ≤ R.card
  · obtain ⟨s, hs_sub, hs_card⟩ := Finset.exists_subset_card_eq hRge
    rcases ramseyUpper_clique_inside_finset ha s hs_card G with hred | hblue
    · rcases hred with ⟨t, ht_sub, ht⟩
      have hv_adj : ∀ x ∈ t, G.Adj v x := by
        intro x hx
        exact (mem_neighborFinset _ _).mp (hs_sub (ht_sub hx))
      have hkm : k - 1 + 1 = k := by omega
      have hcl : G.IsNClique k (insert v t) := by
        have hins := ht.insert hv_adj
        simpa [hkm] using hins
      exact Or.inl ⟨insert v t, hcl⟩
    · rcases hblue with ⟨t, _, ht⟩
      exact Or.inr ⟨t, ht⟩
  · have hBge : b ≤ B.card := by omega
    obtain ⟨s, hs_sub, hs_card⟩ := Finset.exists_subset_card_eq hBge
    rcases ramseyUpper_clique_inside_finset hb s hs_card G with hred | hblue
    · rcases hred with ⟨t, _, ht⟩
      exact Or.inl ⟨t, ht⟩
    · rcases hblue with ⟨t, ht_sub, ht⟩
      have hv_adj : ∀ x ∈ t, Gᶜ.Adj v x := by
        intro x hx
        exact (mem_neighborFinset _ _).mp (hs_sub (ht_sub hx))
      have hlm : l - 1 + 1 = l := by omega
      have hcl : Gᶜ.IsNClique l (insert v t) := by
        have hins := ht.insert hv_adj
        simpa [hlm] using hins
      exact Or.inr ⟨insert v t, hcl⟩

/-- **R(4,4) ≤ 18** via `R(4,4) ≤ R(3,4) + R(4,3) = 9 + 9`. -/
theorem ramsey44_le_18 : RamseyUpper 4 4 18 := by
  have h34 : RamseyUpper 3 4 9 := ramsey34_le_9
  have h43 : RamseyUpper 4 3 9 := (ramseyUpper_swap 3 4 9).1 h34
  simpa using ramseyUpper_add (k := 4) (l := 4) (a := 9) (b := 9)
    (by norm_num) (by norm_num) h34 h43

/-- **R(4,4) = 18** as a pair of bounds. -/
theorem ramsey44_eq_18 : (¬ RamseyUpper 4 4 17) ∧ RamseyUpper 4 4 18 :=
  ⟨ramsey44_gt_17, ramsey44_le_18⟩

/-- **R(3,3) = 6** as a pair of bounds. -/
theorem ramsey33_eq_6 : (¬ RamseyUpper 3 3 5) ∧ RamseyUpper 3 3 6 :=
  ⟨ramsey33_gt_5, ramsey33_fin6⟩

end ProofLab.Ramsey
