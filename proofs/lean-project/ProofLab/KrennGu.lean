/-
Krenn–Gu inherited-vertex equation system, Level A only (encoding + known
positive witness). Formalize-only finite slice — **not** the prize.

status: open problem, encoding+witness only, **no novelty claim**,
**default no claim**. Do **not** describe this as collecting €3,000.

Mathlib v4.10.0 pin `a719ba5c3115` has `SimpleGraph.Subgraph.IsMatching` /
`IsPerfectMatching`, `Complex`, `Fin n` as **infra**. ZERO named Krenn /
EqSystem / inherited-vertex / monochromatic quantum-graph theorem under
`Mathlib/` or `Archive/`. Completing a finite encoding + known witness is
the gap. Do **not** import `Archive.*` or `google-deepmind/formal-conjectures`.

Pin: `catalog/problems/krenn-gu/STATEMENT.md` (OPE-1033; Scout OPE-1028
prime; Director OPE-1032). Encoding: `EqSystem` = `pmSum ι = 1` on constant
colourings and `= 0` otherwise. Weights live in the decidable subring `ℤ`
(stop-rule fallback; known witnesses use `{0,1}`). `Complex` is imported as
the pin's coefficient field and is the same shape via `ℤ → ℂ`. Zero `sorry`.

This is **not** König `ν = τ` (consumed). **Not** Ramsey r33/r35/r333 /
erdos-ramsey-lower (#94). **Not** Friendship / Moore / expander-mixing (#98).
**Not** mason-stothers (#97). **Not** matching-index `μ(G)` (Chandran–
Gajjala–Illickan is literature, not this namesake). **Not** AlphaProof
`d ≥ n` / Kevin M. `n=4,d≥4` / Bogdanov positive-reals as namesake.
**Not** hou-zeng-pfc / sun-135.

Level A (this module, **not** labelled Krenn–Gu / **not** the prize):
encoding compiles; even-cycle `C₄` with `D=2` is a known positive witness
(`EqSystem 4 2 cycle4Weight`). Zero sorry.
Level B finite nonexistence XOR timeboxed `(N,D)=(8,3)` search is **out of
this ticket**. Namesake `∀ even N≥6, ∀ D≥3, ¬ ∃ W, EqSystem N D W` is
**out of v1**. Not sorry-ed.

Transcribed classical even-cycle example (Krenn–Gu–Soltész arXiv:1902.06023
§2; MO 311325). No novelty claim. Default no claim.
-/
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option maxHeartbeats 800000

open Finset SimpleGraph
open scoped BigOperators

namespace ProofLab.KrennGu

/-! ## Encoding (not labelled Krenn–Gu) -/

/-- Bicolored edge weights on labelled vertices `Fin N` with `D` colours,
taking values in a ring `R`. Pin allows `ℂ` or a decidable subring; Level A
uses `ℤ`. `W i j a b` is the weight of the edge between `i` and `j` that
colours `i` with `a` and `j` with `b`. -/
abbrev Weight (N D : ℕ) (R : Type*) := Fin N → Fin N → Fin D → Fin D → R

/-- Complex weights (shape of the STATEMENT pin). Unused by the `ℤ` witness. -/
abbrev Weightℂ (N D : ℕ) := Weight N D ℂ

/-- Computational perfect-matching predicate on a finite edge set of `K_N`:
loopless, and every vertex lies in exactly one edge. Glue
`isPerfectMatchingEdges_imp` identifies this with Mathlib
`Subgraph.IsPerfectMatching` of `matchingSubgraph`. Do **not** re-prove
`IsMatching`. -/
def IsPerfectMatchingEdges {N : ℕ} (M : Finset (Sym2 (Fin N))) : Prop :=
  (∀ e ∈ M, ¬ e.IsDiag) ∧
  (∀ v : Fin N, (M.filter (fun e => v ∈ e)).card = 1)

instance {N : ℕ} (M : Finset (Sym2 (Fin N))) :
    Decidable (IsPerfectMatchingEdges M) := by
  dsimp [IsPerfectMatchingEdges]
  infer_instance

/-- Spanning subgraph of `completeGraph (Fin N)` with edge set `M`
(loops dropped by `fromEdgeSet`). -/
def matchingSubgraph {N : ℕ} (M : Finset (Sym2 (Fin N))) :
    (completeGraph (Fin N)).Subgraph :=
  SimpleGraph.toSubgraph (fromEdgeSet (M : Set (Sym2 (Fin N)))) (fun _ _ h => h.2)

lemma matchingSubgraph_adj {N : ℕ} {M : Finset (Sym2 (Fin N))} {a b : Fin N} :
    (matchingSubgraph M).Adj a b ↔ s(a, b) ∈ M ∧ a ≠ b :=
  Iff.rfl

/-- Mathlib glue (infra reuse, not a re-proof of matching). Not labelled
Krenn–Gu. -/
theorem isPerfectMatchingEdges_imp {N : ℕ} {M : Finset (Sym2 (Fin N))}
    (h : IsPerfectMatchingEdges M) :
    (matchingSubgraph M).IsPerfectMatching := by
  refine (Subgraph.isPerfectMatching_iff (M := matchingSubgraph M)).2 ?_
  intro v
  obtain ⟨e, heq⟩ := card_eq_one.mp (h.2 v)
  have hfilter : e ∈ M ∧ v ∈ e := by
    have : e ∈ M.filter (fun e => v ∈ e) := by simp [heq]
    simpa using this
  obtain ⟨w, hw⟩ := (Sym2.mem_iff_exists).mp hfilter.2
  have hne : v ≠ w := by
    intro hEq
    subst hEq
    exact h.1 e hfilter.1 (by rw [hw]; exact (Sym2.mk_isDiag_iff).2 rfl)
  refine ⟨w, ?_, ?_⟩
  · exact matchingSubgraph_adj.mpr ⟨hw ▸ hfilter.1, hne⟩
  · intro w' hw'
    replace hw' := matchingSubgraph_adj.mp hw'
    have : s(v, w') ∈ M.filter (fun e => v ∈ e) := by
      simp [hw'.1]
    have hs : s(v, w') = e := by
      have : s(v, w') ∈ ({e} : Finset _) := by simpa [heq] using this
      simpa using this
    have heq' : s(v, w') = s(v, w) := hs.trans hw
    rcases (Sym2.eq_iff).mp heq' with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact h2
    · exact (hne h1).elim

/-- Weight of undirected edge `e = s(i,j)` at colouring `ι`, reading `W`
with the smaller-index endpoint first. Computational; no symmetry
hypothesis required for well-definedness. -/
def edgeWeight {N D : ℕ} (W : Weight N D ℤ) (ι : Fin N → Fin D)
    (e : Sym2 (Fin N)) : ℤ :=
  ∑ i : Fin N, ∑ j : Fin N,
    if i ≤ j ∧ s(i, j) = e then W i j (ι i) (ι j) else 0

/-- Sum, over perfect matchings of `K_N`, of the product of induced
bicolored edge weights at vertex colouring `ι`. STATEMENT `pmSum`. -/
def pmSum {N D : ℕ} (W : Weight N D ℤ) (ι : Fin N → Fin D) : ℤ :=
  ∑ M : Finset (Sym2 (Fin N)),
    if IsPerfectMatchingEdges M then ∏ e ∈ M, edgeWeight W ι e else 0

/-- Constant (monochromatic) vertex colouring. -/
def IsConstant {N D : ℕ} (ι : Fin N → Fin D) : Prop :=
  ∀ i j : Fin N, ι i = ι j

instance {N D : ℕ} (ι : Fin N → Fin D) : Decidable (IsConstant ι) := by
  dsimp [IsConstant]
  infer_instance

/-- Equation system of the STATEMENT pin, over `ℤ`. **Not** labelled
Krenn–Gu / **not** the prize: `pmSum ι = 1` on constant colourings and
`= 0` otherwise. -/
def EqSystem (N D : ℕ) (W : Weight N D ℤ) : Prop :=
  ∀ ι : Fin N → Fin D, pmSum W ι = if IsConstant ι then (1 : ℤ) else 0

instance (N D : ℕ) (W : Weight N D ℤ) : Decidable (EqSystem N D W) := by
  dsimp [EqSystem]
  infer_instance

/-! ## Level A witness — even cycle `C₄`, `D = 2` (not labelled Krenn–Gu) -/

/-- Undirected pair of vertex labels, for the cycle-edge lookup. -/
def pairNat {N : ℕ} (i j : Fin N) : Finset ℕ := {i.val, j.val}

/-- Alternating monochromatic 2-colouring of `C₄` with unit weights
(Krenn–Gu–Soltész even-cycle `d = 2` example). Edges `{0,1}` and `{2,3}`
are colour `0` at both ends; `{1,2}` and `{0,3}` are colour `1` at both
ends; every other bicolored edge is weight `0`. **Not** labelled
Krenn–Gu. -/
def cycle4Weight : Weight 4 2 ℤ := fun i j a b =>
  if i = j ∨ a ≠ b then 0
  else if a = 0 ∧ (pairNat i j = ({0, 1} : Finset ℕ) ∨
      pairNat i j = ({2, 3} : Finset ℕ)) then 1
  else if a = 1 ∧ (pairNat i j = ({1, 2} : Finset ℕ) ∨
      pairNat i j = ({0, 3} : Finset ℕ)) then 1
  else 0

/-- Known positive witness: `C₄` with two colours. Glue, **not** labelled
Krenn–Gu, **not** the prize. Zero `sorry`. -/
theorem cycle4_eqSystem : EqSystem 4 2 cycle4Weight := by
  native_decide

end ProofLab.KrennGu
