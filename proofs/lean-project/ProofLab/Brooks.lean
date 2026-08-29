/-
Brooks' theorem scaffolding: χ ≤ Δ except complete graphs and odd cycles.

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 has `Colorable` / `chromaticNumber` / `maxDegree` /
`chromaticNumber_top` / `Walk.three_le_chromaticNumber_of_odd_loop`
but ZERO `brooks` (Mathlib+Archive) and ZERO `cycleGraph`.

Pin: `catalog/problems/brooks-coloring/STATEMENT.md` (OPE-651).
Encoding: Mathlib `Colorable` + `maxDegree` + `⊤`. Odd-cycle pin is the
ProofLab predicate `IsOddCycle` (connected + odd `card V` + 2-regular).
Do **not** invent `cycleGraph` as a Mathlib-gap claim.
Zero `sorry`. Do not import `Archive.*`.
This is **not** greedy (`χ ≤ Δ+1` always). Reuse
`ProofLab.GreedyChromatic.greedy_colorable`; do not re-prove Δ+1.
This is **not** Vizing / 4CT / 5CT / list-colouring Brooks.

Level A: exception families (`⊤` has `χ = Δ+1`; odd cycle has `χ = 3 = Δ+1`)
+ greedy lemma by dependence. Zero sorry.
Level B namesake `brooks_colorable` is residual (Kempe / critical-graph
budget sink; named proof is Brooks 1941 / Diestel / Lovász contraction —
not brute-forced this heartbeat).
-/
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.ConcreteColorings
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Trails
import Mathlib.Tactic
import ProofLab.Eulerian
import ProofLab.GreedyChromatic

open Finset Function SimpleGraph

noncomputable section

namespace ProofLab.Brooks

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## Odd-cycle pin (no `cycleGraph`) -/

/-- Connected, odd order, 2-regular. Equivalent (not a second theorem):
Hamiltonian cycle whose edge-set is `G.edgeSet`, of odd length. -/
def IsOddCycle (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  G.Connected ∧ Odd (Fintype.card V) ∧ ∀ v : V, G.degree v = 2

/-! ## Greedy Δ+1, reused (not Brooks) -/

/-- Folklore / Diestel `χ ≤ Δ+1`. Not Brooks. -/
theorem greedy_colorable : G.Colorable (G.maxDegree + 1) :=
  ProofLab.GreedyChromatic.greedy_colorable

lemma chromaticNumber_le_maxDegree_add_one :
    G.chromaticNumber ≤ G.maxDegree + 1 :=
  greedy_colorable.chromaticNumber_le

/-! ## Level A: complete-graph exception (`χ = Δ+1`) -/

lemma maxDegree_top [Nonempty V] :
    (⊤ : SimpleGraph V).maxDegree = Fintype.card V - 1 :=
  ProofLab.GreedyChromatic.maxDegree_top

/-- Load-bearing exception: nonempty complete graphs need `Δ+1` colours.
Dropping `G ≠ ⊤` makes Brooks false. -/
lemma chromaticNumber_top_eq_maxDegree_add_one [Nonempty V] :
    (⊤ : SimpleGraph V).chromaticNumber =
      ((⊤ : SimpleGraph V).maxDegree + 1 : ℕ) :=
  ProofLab.GreedyChromatic.chromaticNumber_top_eq_maxDegree_add_one

/-! ## Level A: 2-regular glue -/

lemma maxDegree_eq_two_of_two_regular [Nonempty V] (hdeg : ∀ v, G.degree v = 2) :
    G.maxDegree = 2 :=
  le_antisymm
    (G.maxDegree_le_of_forall_degree_le 2 fun v => (hdeg v).le)
    (by
      obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
      rw [hv, hdeg])

lemma oddDeg_card_zero_of_two_regular (hdeg : ∀ v, G.degree v = 2) :
    Fintype.card { v : V | Odd (G.degree v) } = 0 := by
  rw [Fintype.card_eq_zero_iff]
  refine ⟨fun ⟨v, hv⟩ => ?_⟩
  have hv' : Odd (G.degree v) := hv
  rw [hdeg v] at hv'
  exact (by decide : ¬ Odd (2 : ℕ)) hv'

lemma card_edgeFinset_eq_card_of_two_regular (hdeg : ∀ v, G.degree v = 2) :
    G.edgeFinset.card = Fintype.card V := by
  have hsum := G.sum_degrees_eq_twice_card_edges
  have hconst : ∑ v : V, G.degree v = ∑ _v : V, (2 : ℕ) :=
    Finset.sum_congr rfl fun v _ => hdeg v
  have htwo : ∑ _v : V, (2 : ℕ) = 2 * Fintype.card V := by
    simp [sum_const, card_univ, nsmul_eq_mul, mul_comm]
  have : 2 * G.edgeFinset.card = 2 * Fintype.card V := by
    rw [← hsum, hconst, htwo]
  exact Nat.mul_left_cancel (by decide : 0 < 2) this

lemma edgeSet_nonempty_of_two_regular (hConn : G.Connected)
    (hdeg : ∀ v, G.degree v = 2) : G.edgeSet.Nonempty := by
  haveI := hConn.nonempty
  obtain ⟨v⟩ := hConn.nonempty
  have hpos : 0 < G.degree v := by
    rw [hdeg]
    exact two_pos
  obtain ⟨w, hw⟩ := (G.degree_pos_iff_exists_adj (v := v)).mp hpos
  exact ⟨s(v, w), hw⟩

/-! ## Level A: odd closed walk from the 2-regular pin -/

/-- Hierholzer circuit (reused, not re-proved) of a 2-regular connected graph
has length `|V|`. Odd order ⇒ odd closed walk. -/
lemma exists_odd_loop_of_isOddCycle (h : IsOddCycle G) :
    ∃ (u : V) (p : G.Walk u u), Odd p.length := by
  obtain ⟨hConn, hOdd, hdeg⟩ := h
  have hodd0 := oddDeg_card_zero_of_two_regular hdeg
  have hE := edgeSet_nonempty_of_two_regular hConn hdeg
  obtain ⟨u, p, hEul, _hCirc⟩ :=
    ProofLab.Eulerian.eulerian_hierholzer_circuit hConn hodd0 hE
  refine ⟨u, p, ?_⟩
  have hlen : p.length = Fintype.card V := by
    have hcard : p.length = G.edgeFinset.card := by
      have heq := hEul.edgesFinset_eq
      have hpcard : p.edges.length = G.edgeFinset.card := by
        simpa [Walk.IsTrail.edgesFinset] using congrArg Finset.card heq
      exact (Walk.length_edges p).symm.trans hpcard
    exact hcard.trans (card_edgeFinset_eq_card_of_two_regular hdeg)
  simpa [hlen] using hOdd

lemma three_le_chromaticNumber_of_isOddCycle (h : IsOddCycle G) :
    3 ≤ G.chromaticNumber := by
  obtain ⟨u, p, hodd⟩ := exists_odd_loop_of_isOddCycle h
  exact Walk.three_le_chromaticNumber_of_odd_loop p hodd

/-- 2-regular ⇒ `Δ = 2`; greedy supplies the 3-colouring. Not Brooks. -/
lemma colorable_three_of_isOddCycle (h : IsOddCycle G) : G.Colorable 3 := by
  haveI := h.1.nonempty
  have hΔ : G.maxDegree = 2 := maxDegree_eq_two_of_two_regular h.2.2
  simpa [hΔ] using (greedy_colorable : G.Colorable (G.maxDegree + 1))

/-- Load-bearing exception: odd cycles need `Δ+1 = 3` colours.
Dropping `¬ IsOddCycle` makes Brooks false. -/
lemma chromaticNumber_eq_three_of_isOddCycle (h : IsOddCycle G) :
    G.chromaticNumber = 3 :=
  le_antisymm (colorable_three_of_isOddCycle h).chromaticNumber_le
    (three_le_chromaticNumber_of_isOddCycle h)

lemma chromaticNumber_eq_maxDegree_add_one_of_isOddCycle (h : IsOddCycle G) :
    G.chromaticNumber = (G.maxDegree + 1 : ℕ) := by
  haveI := h.1.nonempty
  rw [chromaticNumber_eq_three_of_isOddCycle h,
    maxDegree_eq_two_of_two_regular h.2.2]
  norm_cast

/-! ## Level B residual (namesake)

Named human-scale proof (Brooks 1941 / Diestel): for connected `G` that is
not complete and not an odd cycle, pick a degree-`Δ` vertex whose
neighbourhood is not a clique covering the rest; colour `G−v` with `Δ`
colours; extend, Kempe-swap only if needed. Lovász contraction is the
published alternative.

That argument is the known critical-graph / Kempe budget sink. This
heartbeat does **not** brute-force it and does **not** `sorry` a false
`brooks_colorable`. Cap two levels; honest Level A close.

Intended namesake (not proved here):

```text
theorem brooks_colorable
    (hConn : G.Connected)
    (hNotComplete : G ≠ ⊤)
    (hNotOddCycle : ¬ IsOddCycle G) :
    G.Colorable G.maxDegree
```

Do not label `greedy_colorable` as Brooks.
-/

end ProofLab.Brooks
