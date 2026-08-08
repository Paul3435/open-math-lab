import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

open SimpleGraph Finset

namespace ProofLab.Ramsey

/-!
# Finite graph Ramsey numbers — R(3,3)=6 (formalize-only, OPE-44)

A red/blue edge-colouring of the complete graph `K_n` is represented by a
`SimpleGraph (Fin n)` (the "red" edges); the complement graph is "blue".

## Main definitions

* `HasClique G k`: `G` contains a `k`-clique (a set of `k` pairwise-adjacent
  vertices).
* `RamseyUpper k l n`: every red/blue colouring of `K_n` has a red `K_k` or a
  blue `K_l` (i.e. `R(k,l) ≤ n`).
* `edgeIndex`, `Red6`: certification encoding of a colouring of `K_6` by
  booleans on the 15 edges.

## Main results (certified, zero `sorry`)

* `ramsey33_le_6`: `R(3,3) ≤ 6`.  Exhaustive search over the `2^15` red/blue
  colourings of `K_6`: a boolean function on the 15 edges of `K_6` is a finite
  decidable object, so `native_decide` closes the goal.
* `not_ramsey33_5`: `R(3,3) > 5`, witnessed by the 5-cycle colouring of `K_5`
  (no monochromatic triangle), certified by exhaustive decision.
* `ramsey33_gt_5`: `¬ RamseyUpper 3 3 5`, derived from `not_ramsey33_5`.

`R(3,4)=9` and `R(4,4)=18` are stated in issue OPE-44 but not yet proved here:
a direct `native_decide` enumeration would need to decide `2^36` resp. `2^153`
colourings, which is not tractable; see `problems/ramsey-r33/ATTACK_LOG.md`
for the reduction plan (backtracking/SAT-style search or a Greenwood–Gleason
structural argument).
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

end ProofLab.Ramsey