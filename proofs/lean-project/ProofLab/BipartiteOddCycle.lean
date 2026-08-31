/-
Bipartite characterisation: Colorable 2 iff no odd closed walk.

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 has `Colorable` / `chromaticNumber` / `Walk` / `Reachable` /
`Walk.three_le_chromaticNumber_of_odd_loop` / `Coloring.odd_length_iff_not_congr`
/ `dist` and ZERO `IsBipartite` / `colorable_two_iff`. Completing the namesake
is the gap.

Pin: `catalog/problems/bipartite-odd-cycle/STATEMENT.md` (OPE-775; Scout
OPE-770 prime; Director OPE-774). Encoding: Mathlib `SimpleGraph` +
`Colorable 2` + closed `Walk` (not a new `IsBipartite`; not a second
`IsCycle` namesake). Zero `sorry`. Do not import `Archive.*`.

This is **not** König `ν = τ` (`ProofLab/Konig.lean`, PRs #48/#50). König
*assumes* `Colorable 2`; this theorem *characterises* it.
This is **not** Brooks (`ProofLab/Brooks.lean`, PRs #58/#59). No `Δ` bound;
not the 2-regular `IsOddCycle` exception.
This is **not** greedy `χ ≤ Δ+1` (`ProofLab/GreedyChromatic.lean`, PR #57).
This is **not** Mycielski (`ProofLab/Mycielski.lean`, PR #65). `C5` may be
a landmine *comment* (odd loop ⇒ `¬ Colorable 2`), **not** this namesake.
This is **not** the already-upstream special cases
`completeBipartiteGraph.chromaticNumber = 2` and `pathGraph.bicoloring`
(glue, not labelled namesake).
This is **not** Vizing / 4CT / five-colour / planar / `χ' = Δ`.
This is **not** Moore / Stirling / KST / pentagonal / sunflower / CNS /
Kruskal–Katona / Oddtown / Cayley / Friendship / Havel / Menger / Dilworth /
Eulerian / Dirac / EKR.
This is **not** Euclid–Euler even-perfect (OPE-770 leftover, unassigned).
Leave OPE-403 alone.

v1 is **finite graphs only**. Walk pin, not cycle-extraction. Infinite
compactness 2-colourability is out of v1.

Level A: easy `Colorable 2 → no odd closed walk` via the contrapositive of
`three_le_chromaticNumber_of_odd_loop` (**not** labelled namesake). Empty /
edgeless / `K₂` / even cycle `C₄` are `Colorable 2`. **`K₃` is the
load-bearing negative.** Zero sorry.
Level B: namesake `colorable_two_iff_no_odd_walk`. Hard direction: colour
each connected component by the parity of `dist root v`. Well-defined
because two walks of different parity concatenate to an odd closed walk.
Adjacent vertices have opposite parity. Cap two levels.
-/
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.ConcreteColorings
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Tactic

set_option maxHeartbeats 400000
set_option linter.unusedVariables false

open Function SimpleGraph

noncomputable section
open Classical

namespace ProofLab.BipartiteOddCycle

/-! ## Level A — easy direction (not labelled namesake) -/

/-- Odd closed walk ⇒ `χ ≥ 3` ⇒ not `Colorable 2`. Mathlib glue; **not**
the namesake. -/
theorem colorable_two_imp_no_odd_walk {V : Type*} {G : SimpleGraph V}
    (h : G.Colorable 2) :
    ∀ ⦃u : V⦄ (p : G.Walk u u), ¬ Odd p.length := by
  intro u p hp
  have h3 : (3 : ℕ∞) ≤ G.chromaticNumber :=
    Walk.three_le_chromaticNumber_of_odd_loop p hp
  have hle : G.chromaticNumber ≤ 2 := h.chromaticNumber_le
  have : (3 : ℕ∞) ≤ 2 := le_trans h3 hle
  norm_cast at this

/-- Empty vertex type is `Colorable 2`. -/
theorem colorable_two_of_isEmpty {V : Type*} [IsEmpty V] (G : SimpleGraph V) :
    G.Colorable 2 :=
  colorable_of_isEmpty _ _

/-- Edgeless graph is `Colorable 2` (in fact `Colorable 1`). -/
theorem colorable_two_bot {V : Type*} [Fintype V] :
    (⊥ : SimpleGraph V).Colorable 2 := by
  refine Colorable.mono (by decide : (1 : ℕ) ≤ 2) ⟨Coloring.mk (fun _ => 0) ?_⟩
  intro v w h
  exact ((bot_adj v w).mp h).elim

/-- `K₂ = ⊤` on `Fin 2` is `Colorable 2`. Glue, **not** the namesake.
(Mathlib `pathGraph.bicoloring` is the already-upstream special case.) -/
theorem colorable_two_k2 : (⊤ : SimpleGraph (Fin 2)).Colorable 2 :=
  colorable_of_fintype _

/-- Path bicoloring is already upstream. Glue, **not** labelled namesake. -/
theorem colorable_two_pathGraph (n : ℕ) : (pathGraph n).Colorable 2 :=
  (pathGraph.bicoloring n).colorable

/-! ### Even 4-cycle (not labelled namesake) -/

/-- Cycle `C₄` on `Fin 4`. Wrap-around is `Fin` addition (`3 + 1 = 0`). -/
def C4 : SimpleGraph (Fin 4) where
  Adj i j := i + 1 = j ∨ j + 1 = i
  symm := fun _ _ h => Or.symm h
  loopless := by
    intro i h
    have h10 : (1 : Fin 4) ≠ 0 := by decide
    have : i + 1 = i := by
      rcases h with h | h <;> exact h
    exact h10 (add_left_cancel (this.trans (add_zero i).symm))

instance : DecidableRel C4.Adj :=
  fun i j => inferInstanceAs (Decidable (i + 1 = j ∨ j + 1 = i))

/-- Parity colouring of `C₄`. Adjacent vertices differ by 1 mod 4. -/
def c4Bicoloring : C4.Coloring Bool :=
  Coloring.mk (fun u => u.val % 2 == 0) <| by
    intro u v h
    fin_cases u <;> fin_cases v <;> simp [C4] at h ⊢

/-- Even cycle `C₄` is `Colorable 2`. Not the namesake. -/
theorem colorable_two_c4 : C4.Colorable 2 :=
  c4Bicoloring.colorable

/-! ### `K₃` landmine (load-bearing negative, not labelled namesake) -/

/-- Closed walk of length 3 around `K₃ = ⊤` on `Fin 3`. -/
def k3OddLoop : (⊤ : SimpleGraph (Fin 3)).Walk 0 0 :=
  Walk.cons (by decide : (⊤ : SimpleGraph (Fin 3)).Adj 0 1)
    (Walk.cons (by decide : (⊤ : SimpleGraph (Fin 3)).Adj 1 2)
      (Walk.cons (by decide : (⊤ : SimpleGraph (Fin 3)).Adj 2 0) Walk.nil))

lemma k3OddLoop_length : k3OddLoop.length = 3 := rfl

lemma k3OddLoop_odd : Odd k3OddLoop.length := by
  rw [k3OddLoop_length]
  decide

/-- Odd closed walk ⇒ `χ ≥ 3`. Mathlib glue, **not** the namesake. -/
lemma three_le_chromaticNumber_k3 :
    3 ≤ (⊤ : SimpleGraph (Fin 3)).chromaticNumber :=
  Walk.three_le_chromaticNumber_of_odd_loop k3OddLoop k3OddLoop_odd

/-- Load-bearing negative: `K₃` is not 2-colourable. Same graph as the
König matching landmine; **different theorem**. -/
theorem k3_not_colorable_two : ¬ (⊤ : SimpleGraph (Fin 3)).Colorable 2 := by
  intro h
  have hle : (⊤ : SimpleGraph (Fin 3)).chromaticNumber ≤ 2 := h.chromaticNumber_le
  have : (3 : ℕ∞) ≤ 2 := le_trans three_le_chromaticNumber_k3 hle
  norm_cast at this

/-
Landmine comment only (not labelled this namesake): Mycielski already
shows `C5` is `¬ Colorable 2` via the same odd-loop glue
(`ProofLab/Mycielski.lean` `c5_not_colorable_two`). That is Mycielski
Level A, not this characterisation.
-/

/-! ## Level B engine — walk-parity and component roots -/

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Two `u–v` walks have the same length parity: concatenating one with
the reverse of the other is a closed walk at `u`. -/
theorem even_length_eq_of_no_odd_walk
    (hno : ∀ ⦃u : V⦄ (p : G.Walk u u), ¬ Odd p.length)
    {u v : V} (p q : G.Walk u v) :
    Even p.length ↔ Even q.length := by
  have hclosed : ¬ Odd (p.append q.reverse).length := hno _
  rw [Walk.length_append, Walk.length_reverse, Nat.odd_iff_not_even] at hclosed
  have heven : Even (p.length + q.length) := not_not.mp hclosed
  rwa [Nat.even_add] at heven

/-- `dist` realises the unique walk-length parity (when reachable). -/
theorem even_dist_iff_even_walk
    (hno : ∀ ⦃u : V⦄ (p : G.Walk u u), ¬ Odd p.length)
    {u v : V} (hv : G.Reachable u v) (p : G.Walk u v) :
    Even (G.dist u v) ↔ Even p.length := by
  obtain ⟨q, hq⟩ := hv.exists_walk_length_eq_dist
  rw [← hq]
  exact even_length_eq_of_no_odd_walk G hno q p

/-- A representative of a connected component. -/
noncomputable def componentOut (c : G.ConnectedComponent) : V :=
  Classical.choose (Quot.exists_rep c)

lemma componentOut_spec (c : G.ConnectedComponent) :
    G.connectedComponentMk (componentOut G c) = c :=
  Classical.choose_spec (Quot.exists_rep c)

/-- Root of the component of `v`. Same root for adjacent vertices. -/
noncomputable def componentRoot (v : V) : V :=
  componentOut G (G.connectedComponentMk v)

lemma reachable_componentRoot (v : V) :
    G.Reachable (componentRoot G v) v :=
  ConnectedComponent.eq.mp (componentOut_spec G (G.connectedComponentMk v))

lemma componentRoot_eq_of_adj {u v : V} (h : G.Adj u v) :
    componentRoot G u = componentRoot G v := by
  simp only [componentRoot]
  rw [ConnectedComponent.connectedComponentMk_eq_of_adj h]

/-- Adjacent vertices have opposite `dist`-parity from a common root. -/
theorem even_dist_adj
    (hno : ∀ ⦃u : V⦄ (p : G.Walk u u), ¬ Odd p.length)
    {r u v : V} (hru : G.Reachable r u) (huv : G.Adj u v) :
    Even (G.dist r u) ↔ ¬ Even (G.dist r v) := by
  have hrv : G.Reachable r v := hru.trans huv.reachable
  obtain ⟨p, hp⟩ := hru.exists_walk_length_eq_dist
  let q : G.Walk r v := p.concat huv
  have hqlen : q.length = p.length + 1 := Walk.length_concat p huv
  have hvpar : Even (G.dist r v) ↔ Even q.length :=
    even_dist_iff_even_walk G hno hrv q
  have hupar : Even (G.dist r u) ↔ Even p.length := by
    rw [← hp]
  rw [hupar, hvpar, hqlen, Nat.even_add_one]
  simp

/-- Colour `v` by the parity of `dist` from its component root. -/
noncomputable def parityColor (v : V) : Bool :=
  decide (Even (G.dist (componentRoot G v) v))

lemma decide_even_ne {m n : ℕ} (h : Even m ↔ ¬ Even n) :
    decide (Even m) ≠ decide (Even n) := by
  intro heq
  by_cases hm : Even m
  · have hn : ¬ Even n := h.mp hm
    rw [decide_eq_true hm, decide_eq_false hn] at heq
    cases heq
  · have hn : Even n := not_not.mp fun hn => hm (h.mpr hn)
    rw [decide_eq_false hm, decide_eq_true hn] at heq
    cases heq

lemma parityColor_valid
    (hno : ∀ ⦃u : V⦄ (p : G.Walk u u), ¬ Odd p.length) :
    ∀ ⦃u v : V⦄, G.Adj u v → parityColor G u ≠ parityColor G v := by
  intro u v hadj
  have hroot : componentRoot G u = componentRoot G v :=
    componentRoot_eq_of_adj G hadj
  have hpar : Even (G.dist (componentRoot G u) u) ↔
      ¬ Even (G.dist (componentRoot G u) v) :=
    even_dist_adj G hno (reachable_componentRoot G u) hadj
  unfold parityColor
  rw [hroot]
  refine decide_even_ne ?_
  simpa [hroot] using hpar

/-- Dist-parity colouring when there is no odd closed walk. -/
noncomputable def parityColoring
    (hno : ∀ ⦃u : V⦄ (p : G.Walk u u), ¬ Odd p.length) :
    G.Coloring Bool :=
  Coloring.mk (parityColor G) (fun {_ _} h => parityColor_valid G hno h)

theorem colorable_two_of_no_odd_walk
    (hno : ∀ ⦃u : V⦄ (p : G.Walk u u), ¬ Odd p.length) :
    G.Colorable 2 :=
  (parityColoring G hno).colorable

/-- Namesake (STATEMENT pin). Finite simple graphs only. Encoding is
`Colorable 2`, not a new `IsBipartite`. Walk pin, not cycle-extraction.
Not König `ν = τ`, not Brooks, not greedy, not Mycielski. -/
theorem colorable_two_iff_no_odd_walk :
    G.Colorable 2 ↔ ∀ ⦃u : V⦄ (p : G.Walk u u), ¬ Odd p.length :=
  ⟨colorable_two_imp_no_odd_walk, colorable_two_of_no_odd_walk G⟩

end ProofLab.BipartiteOddCycle
