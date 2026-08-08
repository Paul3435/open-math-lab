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

end ProofLab.Ramsey