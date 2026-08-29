/-
Dilworth (1950): min chain-partition size = max antichain size (width)
on finite posets.

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 has `IsChain` / `IsAntichain` definitions only — no width,
no chain-partition number, no Dilworth. ProofLab `konig_bipartite` is the
*engine*, not the claim. Do not re-prove König. Not Hall. Not Mirsky.
Finite only. `PartialOrder`, not `Preorder`. Split graph uses strict `<`.
Do not König the comparability graph.

Pin: `catalog/problems/dilworth-poset/STATEMENT.md` (OPE-619 / OPE-626 / Scout OPE-613).
Level A: easy inequality + empty / 2-element / total-chain / antichain-poset.
Level B (this module, OPE-626): ∀ finite poset via Fulkerson split + matching
→ chain partition; `ProofLab.Konig.konig_bipartite` is the *engine*, not the claim.
Zero `sorry`. Do not import `Archive.*`.
-/
import Mathlib.Order.Chain
import Mathlib.Order.Antichain
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Sort
import Mathlib.Logic.Relation
import Mathlib.Tactic
import ProofLab.Konig

open Finset Function SimpleGraph

noncomputable section
open Classical

namespace ProofLab.Dilworth

variable {α : Type*} [Fintype α] [DecidableEq α] [PartialOrder α]
variable [DecidableRel ((· : α) ≤ ·)]

/-! ## Chain / antichain Finset wrappers (STATEMENT pin) -/

def IsChainSet (C : Finset α) : Prop :=
  IsChain (· ≤ ·) (C : Set α)

def IsAntichainSet (A : Finset α) : Prop :=
  IsAntichain (· ≤ ·) (A : Set α)

lemma isChainSet_empty : IsChainSet (∅ : Finset α) := by
  intro a ha b _hb
  simp at ha

lemma isAntichainSet_empty : IsAntichainSet (∅ : Finset α) := by
  intro a ha b _hb
  simp at ha

lemma isChainSet_singleton (a : α) : IsChainSet ({a} : Finset α) := by
  intro x hx y hy hne
  simp only [mem_coe, mem_singleton] at hx hy
  exact (hne (hx.trans hy.symm)).elim

lemma isAntichainSet_singleton (a : α) : IsAntichainSet ({a} : Finset α) := by
  intro x hx y hy hne
  simp only [mem_coe, mem_singleton] at hx hy
  exact (hne (hx.trans hy.symm)).elim

/-- Pairwise-disjoint family of chains covering `univ`. -/
def IsChainPartition {n : ℕ} (chains : Fin n → Finset α) : Prop :=
  (∀ i, IsChainSet (chains i)) ∧
  (∀ i j, i ≠ j → Disjoint (chains i) (chains j)) ∧
  (∀ x, ∃ i, x ∈ chains i)

/-- Width = max antichain cardinality. -/
def width : ℕ :=
  (univ : Finset (Finset α)).sup fun A => if IsAntichainSet A then A.card else 0

lemma le_width {A : Finset α} (hA : IsAntichainSet A) : A.card ≤ width (α := α) := by
  have h :=
    Finset.le_sup (s := (univ : Finset (Finset α)))
      (f := fun B : Finset α => if IsAntichainSet B then B.card else 0) (mem_univ A)
  simpa [width, hA] using h

lemma width_le_of_forall {n : ℕ} (h : ∀ A : Finset α, IsAntichainSet A → A.card ≤ n) :
    width (α := α) ≤ n := by
  refine Finset.sup_le (s := (univ : Finset (Finset α))) ?_
  intro A _
  by_cases hA : IsAntichainSet A
  · simp [hA, h A hA]
  · simp [hA]

lemma antichain_inter_chain_card_le_one {A C : Finset α}
    (hA : IsAntichainSet A) (hC : IsChainSet C) :
    (A ∩ C).card ≤ 1 := by
  refine (card_le_one_iff (s := A ∩ C)).mpr ?_
  intro x y hx hy
  have hxA : x ∈ A := (mem_inter.mp hx).1
  have hyA : y ∈ A := (mem_inter.mp hy).1
  have hxC : x ∈ C := (mem_inter.mp hx).2
  have hyC : y ∈ C := (mem_inter.mp hy).2
  by_cases hxy : x = y
  · exact hxy
  · have hcmp : x ≤ y ∨ y ≤ x := hC hxC hyC hxy
    rcases hcmp with hle | hle
    · exact hA.eq hxA hyA hle
    · exact (hA.eq hyA hxA hle).symm

/-- Level A: any antichain meets each chain in at most one point, so
`width ≤` the size of any chain partition. -/
theorem width_le_chainPartition {n : ℕ} {chains : Fin n → Finset α}
    (hP : IsChainPartition chains) : width (α := α) ≤ n := by
  refine width_le_of_forall ?_
  intro A hA
  obtain ⟨hchain, _hdisj, hcov⟩ := hP
  let idx : α → Fin n := fun x => Classical.choose (hcov x)
  have hmem : ∀ x, x ∈ chains (idx x) := fun x => Classical.choose_spec (hcov x)
  have hinj : Set.InjOn idx (A : Set α) := by
    intro x hx y hy hidx
    have hxC : x ∈ chains (idx x) := hmem x
    have hyC : y ∈ chains (idx x) := by simpa [hidx] using hmem y
    have hle := antichain_inter_chain_card_le_one hA (hchain (idx x))
    have hxI : x ∈ A ∩ chains (idx x) := mem_inter.mpr ⟨hx, hxC⟩
    have hyI : y ∈ A ∩ chains (idx x) := mem_inter.mpr ⟨hy, hyC⟩
    exact (card_le_one_iff.mp hle) hxI hyI
  have hcard : (A.image idx).card = A.card := card_image_of_injOn hinj
  have hle : (A.image idx).card ≤ (univ : Finset (Fin n)).card := card_le_card (subset_univ _)
  simpa [hcard, card_univ, Fintype.card_fin] using hle

lemma width_eq_zero_of_isEmpty [IsEmpty α] : width (α := α) = 0 := by
  refine le_antisymm ?_ (Nat.zero_le _)
  refine width_le_of_forall ?_
  intro A _
  have : A = ∅ := eq_empty_of_forall_not_mem fun x _ => (IsEmpty.false x).elim
  simp [this]

/-- Empty poset: width 0, empty partition. -/
theorem dilworth_empty [IsEmpty α] :
    ∃ (n : ℕ) (chains : Fin n → Finset α) (A : Finset α),
      IsChainPartition chains ∧ IsAntichainSet A ∧ A.card = n ∧ n = width (α := α) := by
  let chains : Fin 0 → Finset α := fun i => Fin.elim0 i
  refine ⟨0, chains, ∅, ⟨?hc, ?hd, ?hu⟩, isAntichainSet_empty, card_empty,
    width_eq_zero_of_isEmpty.symm⟩
  · intro i; exact Fin.elim0 i
  · intro i; exact Fin.elim0 i
  · intro x; exact (IsEmpty.false x).elim

lemma width_eq_one_of_isChain_univ (hC : IsChainSet (univ : Finset α))
    (hne : Nonempty α) : width (α := α) = 1 := by
  obtain ⟨a⟩ := hne
  apply le_antisymm
  · refine width_le_of_forall ?_
    intro A hA
    refine (card_le_one_iff (s := A)).mpr ?_
    intro x y hx hy
    by_cases hxy : x = y
    · exact hxy
    · have hcmp : x ≤ y ∨ y ≤ x := hC (mem_univ x) (mem_univ y) hxy
      rcases hcmp with hle | hle
      · exact hA.eq hx hy hle
      · exact (hA.eq hy hx hle).symm
  · simpa using le_width (isAntichainSet_singleton a)

/-- Total chain: width 1 (or 0 if empty). -/
theorem dilworth_of_isChain_univ (hC : IsChainSet (univ : Finset α)) :
    ∃ (n : ℕ) (chains : Fin n → Finset α) (A : Finset α),
      IsChainPartition chains ∧ IsAntichainSet A ∧ A.card = n ∧ n = width (α := α) := by
  cases isEmpty_or_nonempty α with
  | inl _ => exact dilworth_empty
  | inr hne =>
    obtain ⟨a⟩ := hne
    have hw : width (α := α) = 1 := width_eq_one_of_isChain_univ hC ⟨a⟩
    refine ⟨1, fun _ => univ, {a}, ?_, isAntichainSet_singleton a, by simp, hw.symm⟩
    refine ⟨fun _ => hC, ?_, fun x => ⟨0, mem_univ x⟩⟩
    intro i j hij
    exact (hij (Subsingleton.elim i j)).elim

lemma width_eq_card_of_isAntichain_univ (hA : IsAntichainSet (univ : Finset α)) :
    width (α := α) = Fintype.card α := by
  apply le_antisymm
  · exact width_le_of_forall fun A _ => card_le_univ A
  · simpa [card_univ] using le_width hA

/-- Antichain poset: width = `card α`, singleton chains. -/
theorem dilworth_of_isAntichain_univ (hA : IsAntichainSet (univ : Finset α)) :
    ∃ (n : ℕ) (chains : Fin n → Finset α) (A : Finset α),
      IsChainPartition chains ∧ IsAntichainSet A ∧ A.card = n ∧ n = width (α := α) := by
  let e : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  let chains : Fin (Fintype.card α) → Finset α := fun i => {e.symm i}
  have hP : IsChainPartition chains := by
    refine ⟨fun i => isChainSet_singleton _, ?_, ?_⟩
    · intro i j hij
      refine disjoint_left.mpr ?_
      intro x hxi hxj
      have : e.symm i = e.symm j :=
        (eq_of_mem_singleton hxi).symm.trans (eq_of_mem_singleton hxj)
      exact hij (e.symm.injective this)
    · intro x
      refine ⟨e x, ?_⟩
      simp [chains]
  refine ⟨Fintype.card α, chains, univ, hP, hA, card_univ,
    (width_eq_card_of_isAntichain_univ hA).symm⟩

lemma fin2_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  revert i
  decide

lemma isChain_or_isAntichain_of_card_eq_two (hα : Fintype.card α = 2) :
    IsChainSet (univ : Finset α) ∨ IsAntichainSet (univ : Finset α) := by
  let e : α ≃ Fin 2 := Fintype.equivFinOfCardEq hα
  let a := e.symm 0
  let b := e.symm 1
  have mem_ab : ∀ x : α, x = a ∨ x = b := by
    intro x
    rcases fin2_cases (e x) with hx | hx
    · left
      exact (Equiv.symm_apply_apply e x).symm.trans (congrArg e.symm hx)
    · right
      exact (Equiv.symm_apply_apply e x).symm.trans (congrArg e.symm hx)
  by_cases hcmp : a ≤ b ∨ b ≤ a
  · refine Or.inl ?_
    intro x _hx y _hy hxy
    rcases mem_ab x with rfl | rfl <;> rcases mem_ab y with rfl | rfl
    · exact (hxy rfl).elim
    · exact hcmp
    · exact Or.symm hcmp
    · exact (hxy rfl).elim
  · refine Or.inr ?_
    intro x _hx y _hy hxy hle
    rcases mem_ab x with rfl | rfl <;> rcases mem_ab y with rfl | rfl
    · exact hxy rfl
    · exact hcmp (Or.inl hle)
    · exact hcmp (Or.inr hle)
    · exact hxy rfl

/-- 2-element poset: either a 2-chain (width 1) or a 2-antichain (width 2). -/
theorem dilworth_card_eq_two (hα : Fintype.card α = 2) :
    ∃ (n : ℕ) (chains : Fin n → Finset α) (A : Finset α),
      IsChainPartition chains ∧ IsAntichainSet A ∧ A.card = n ∧ n = width (α := α) := by
  rcases isChain_or_isAntichain_of_card_eq_two hα with hC | hA
  · exact dilworth_of_isChain_univ hC
  · exact dilworth_of_isAntichain_univ hA

/-! ## Fulkerson split graph (Level B engine; not the comparability graph) -/

def splitAdj : (α ⊕ α) → (α ⊕ α) → Prop
  | .inl a, .inr b => a < b
  | .inr b, .inl a => a < b
  | .inl _, .inl _ => False
  | .inr _, .inr _ => False

lemma splitAdj_symm : Symmetric (splitAdj (α := α)) := by
  intro u v h
  cases u <;> cases v <;> simp [splitAdj] at h ⊢ <;> exact h

lemma splitAdj_irrefl : Irreflexive (splitAdj (α := α)) := by
  intro u
  cases u <;> simp [splitAdj]

/-- Split graph on `α ⊕ α`. Edges are **strict** `<` only. Not comparability. -/
def splitGraph : SimpleGraph (α ⊕ α) where
  Adj := splitAdj
  symm := splitAdj_symm
  loopless := splitAdj_irrefl

lemma splitGraph_adj_inl_inr {a b : α} :
    (splitGraph : SimpleGraph (α ⊕ α)).Adj (.inl a) (.inr b) ↔ a < b := by
  simp [splitGraph, splitAdj]

lemma splitGraph_colorable : (splitGraph : SimpleGraph (α ⊕ α)).Colorable 2 :=
  ⟨Coloring.mk (fun v => match v with | .inl _ => 0 | .inr _ => 1) (by
    intro u v h
    cases u <;> cases v <;> simp [splitGraph, splitAdj] at h ⊢)⟩

lemma exists_max_matching (G : SimpleGraph (α ⊕ α)) :
    ∃ M : Subgraph G, M.IsMatching ∧
      ProofLab.Konig.matchingCard M = ProofLab.Konig.matchingNumber G := by
  have hmem : ProofLab.Konig.matchingNumber G ∈ ProofLab.Konig.matchingSizes G :=
    Nat.sSup_mem (ProofLab.Konig.matchingSizes_nonempty G)
      (ProofLab.Konig.bddAbove_matchingSizes G)
  simpa [ProofLab.Konig.matchingSizes] using hmem

lemma exists_min_cover (G : SimpleGraph (α ⊕ α)) :
    ∃ C : Finset (α ⊕ α), ProofLab.Konig.IsVertexCover G C ∧
      C.card = ProofLab.Konig.vertexCoverNumber G := by
  have hmem : ProofLab.Konig.vertexCoverNumber G ∈ ProofLab.Konig.coverSizes G :=
    Nat.sInf_mem (ProofLab.Konig.coverSizes_nonempty G)
  simpa [ProofLab.Konig.coverSizes] using hmem

/-- Uncovered ground-set of a vertex cover of the split graph. -/
def uncovered (C : Finset (α ⊕ α)) : Finset α :=
  univ.filter fun x => Sum.inl x ∉ C ∧ Sum.inr x ∉ C

lemma uncovered_isAntichain {C : Finset (α ⊕ α)}
    (hC : ProofLab.Konig.IsVertexCover (splitGraph : SimpleGraph (α ⊕ α)) C) :
    IsAntichainSet (uncovered C) := by
  intro x hx y hy hne hle
  have hx' := (mem_filter.mp hx).2
  have hy' := (mem_filter.mp hy).2
  have hlt : x < y := lt_of_le_of_ne hle hne
  have hadj : (splitGraph : SimpleGraph (α ⊕ α)).Adj (.inl x) (.inr y) :=
    splitGraph_adj_inl_inr.mpr hlt
  rcases hC hadj with hxC | hyC
  · exact hx'.1 hxC
  · exact hy'.2 hyC

lemma card_touched_le (C : Finset (α ⊕ α)) :
    (univ.filter fun x : α => Sum.inl x ∈ C ∨ Sum.inr x ∈ C).card ≤ C.card := by
  let S := univ.filter fun x : α => Sum.inl x ∈ C ∨ Sum.inr x ∈ C
  let pick : { x // x ∈ S } → { v // v ∈ C } := fun ⟨x, hx⟩ =>
    if h : Sum.inl x ∈ C then ⟨.inl x, h⟩
    else
      ⟨.inr x, by
        have hx' := (mem_filter.mp hx).2
        exact hx'.resolve_left h⟩
  have hshape : ∀ x hx, (pick ⟨x, hx⟩ : α ⊕ α) = Sum.inl x ∨
      (pick ⟨x, hx⟩ : α ⊕ α) = Sum.inr x := by
    intro x hx
    dsimp [pick]
    split_ifs <;> simp
  have hinj : Injective pick := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ h
    apply Subtype.ext
    have hv : (pick ⟨x, hx⟩ : α ⊕ α) = pick ⟨y, hy⟩ := congrArg Subtype.val h
    rcases hshape x hx with hx' | hx' <;> rcases hshape y hy with hy' | hy'
    · exact Sum.inl.inj (hx'.symm.trans (hv.trans hy'))
    · cases hx'.symm.trans (hv.trans hy')
    · cases hx'.symm.trans (hv.trans hy')
    · exact Sum.inr.inj (hx'.symm.trans (hv.trans hy'))
  have hle := Fintype.card_le_of_injective pick hinj
  exact (Fintype.card_coe S).symm.trans_le (hle.trans_eq (Fintype.card_coe C))

lemma uncovered_card_add (C : Finset (α ⊕ α)) :
    (uncovered C).card + (univ.filter fun x : α => Sum.inl x ∈ C ∨ Sum.inr x ∈ C).card =
      Fintype.card α := by
  dsimp [uncovered]
  have := filter_card_add_filter_neg_card_eq_card
    (s := (univ : Finset α)) (p := fun x : α => Sum.inl x ∈ C ∨ Sum.inr x ∈ C)
  -- uncovered = filter (¬ (inl ∈ C ∨ inr ∈ C))
  have hneg : (univ.filter fun x : α => ¬ (Sum.inl x ∈ C ∨ Sum.inr x ∈ C)) =
      univ.filter fun x => Sum.inl x ∉ C ∧ Sum.inr x ∉ C := by
    ext x
    simp [not_or]
  simpa [hneg, card_univ, add_comm] using this

lemma le_uncovered_card (C : Finset (α ⊕ α)) :
    Fintype.card α ≤ (uncovered C).card + C.card := by
  have h := uncovered_card_add C
  have hle := card_touched_le C
  omega

/-! ## Level B: matching in `splitGraph` → chain partition of size `width`

Fulkerson: a matching edge `inl a — inr b` (so `a < b`) is a successor step.
The functional graph of that successor is a disjoint union of paths (no cycles:
strict `<`). Unmatched-on-the-right vertices are sources of those paths. The
number of paths is `|α| − ν(splitGraph)`. König `ν = τ` on the split graph
(engine, not the claim) plus the uncovered antichain gives `|chains| = width`.
-/

open Relation

section MatchingChains

variable {M : Subgraph (splitGraph : SimpleGraph (α ⊕ α))}

lemma split_adj_form {u v : α ⊕ α}
    (h : (splitGraph : SimpleGraph (α ⊕ α)).Adj u v) :
    ∃ a b : α, a < b ∧
      ((u = Sum.inl a ∧ v = Sum.inr b) ∨ (u = Sum.inr b ∧ v = Sum.inl a)) := by
  cases u with
  | inl a =>
    cases v with
    | inl _ => simp [splitGraph, splitAdj] at h
    | inr b =>
      refine ⟨a, b, ?_, Or.inl ⟨rfl, rfl⟩⟩
      simpa [splitGraph, splitAdj] using h
  | inr b =>
    cases v with
    | inl a =>
      refine ⟨a, b, ?_, Or.inr ⟨rfl, rfl⟩⟩
      simpa [splitGraph, splitAdj] using h
    | inr _ => simp [splitGraph, splitAdj] at h

/-- Successor along a matching: `a ↦ b` when `inl a` is matched to `inr b`. -/
def succRel (M : Subgraph (splitGraph : SimpleGraph (α ⊕ α))) (a b : α) : Prop :=
  M.Adj (Sum.inl a) (Sum.inr b)

def hasPred (M : Subgraph (splitGraph : SimpleGraph (α ⊕ α))) (x : α) : Prop :=
  ∃ a, succRel M a x

/-- Right-unmatched ground vertices: sources of Fulkerson chains. -/
def sources (M : Subgraph (splitGraph : SimpleGraph (α ⊕ α))) : Finset α :=
  univ.filter fun x => ¬ hasPred M x

def matchedRight (M : Subgraph (splitGraph : SimpleGraph (α ⊕ α))) : Finset α :=
  univ.filter fun x => hasPred M x

/-- Elements reachable from `s` by following matching successors. -/
def chainFrom (M : Subgraph (splitGraph : SimpleGraph (α ⊕ α))) (s : α) : Finset α :=
  univ.filter fun y => ReflTransGen (succRel M) s y

lemma succRel_lt {a b : α} (h : succRel M a b) : a < b := by
  have := M.adj_sub h
  simpa [splitGraph, splitAdj] using this

lemma succRel_right_unique (hM : M.IsMatching) :
    Relator.RightUnique (succRel M) := by
  intro a b c hb hc
  have hv : Sum.inl a ∈ M.verts := M.edge_vert hb
  obtain ⟨w, _hw, huniq⟩ := hM hv
  have hb' := huniq (Sum.inr b) hb
  have hc' := huniq (Sum.inr c) hc
  exact Sum.inr.inj (hb'.trans hc'.symm)

lemma succRel_left_unique (hM : M.IsMatching) :
    Relator.LeftUnique (succRel M) := by
  intro a a' b ha ha'
  have hv : Sum.inr b ∈ M.verts := M.edge_vert (M.symm ha)
  obtain ⟨w, _hw, huniq⟩ := hM hv
  have h1 := huniq (Sum.inl a) (M.symm ha)
  have h2 := huniq (Sum.inl a') (M.symm ha')
  exact Sum.inl.inj (h1.trans h2.symm)

lemma rtg_le {a b : α} (h : ReflTransGen (succRel M) a b) : a ≤ b := by
  induction h with
  | refl => exact le_rfl
  | tail _ hab ih => exact ih.trans (le_of_lt (succRel_lt hab))

lemma exists_inl_inr_of_mem_edgeSet {e : Sym2 (α ⊕ α)} (he : e ∈ M.edgeSet) :
    ∃ a b : α, e = s(Sum.inl a, Sum.inr b) ∧ M.Adj (Sum.inl a) (Sum.inr b) := by
  revert he
  refine Sym2.inductionOn e fun u v he => ?_
  have hadj : M.Adj u v := SimpleGraph.Subgraph.mem_edgeSet.mp he
  have hG := M.adj_sub hadj
  cases u with
  | inl a =>
    cases v with
    | inl _ => simp [splitGraph, splitAdj] at hG
    | inr b => exact ⟨a, b, rfl, hadj⟩
  | inr b =>
    cases v with
    | inl a =>
      refine ⟨a, b, Sym2.eq_swap, M.symm hadj⟩
    | inr _ => simp [splitGraph, splitAdj] at hG

noncomputable def leftOfEdge (e : M.edgeSet) : α :=
  (exists_inl_inr_of_mem_edgeSet e.2).choose

noncomputable def rightOfEdge (e : M.edgeSet) : α :=
  (exists_inl_inr_of_mem_edgeSet e.2).choose_spec.choose

lemma left_right_of_edge (e : M.edgeSet) :
    (e : Sym2 (α ⊕ α)) = s(Sum.inl (leftOfEdge e), Sum.inr (rightOfEdge e)) ∧
      M.Adj (Sum.inl (leftOfEdge e)) (Sum.inr (rightOfEdge e)) :=
  (exists_inl_inr_of_mem_edgeSet e.2).choose_spec.choose_spec

lemma matchingCard_eq_matchedRight (hM : M.IsMatching) :
    ProofLab.Konig.matchingCard M = (matchedRight M).card := by
  let pickR : { x // x ∈ matchedRight M } → M.edgeSet := fun ⟨x, hx⟩ =>
    ⟨s(Sum.inl (Classical.choose (mem_filter.mp hx).2), Sum.inr x),
      SimpleGraph.Subgraph.mem_edgeSet.mpr (Classical.choose_spec (mem_filter.mp hx).2)⟩
  have hinjR : Injective pickR := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ h
    apply Subtype.ext
    have hv : (pickR ⟨x, hx⟩ : Sym2 (α ⊕ α)) = pickR ⟨y, hy⟩ := congrArg Subtype.val h
    rw [Sym2.eq_iff] at hv
    rcases hv with ⟨_, hxy⟩ | ⟨hbad, _⟩
    · exact Sum.inr.inj hxy
    · cases hbad
  let pickE : M.edgeSet → { x // x ∈ matchedRight M } := fun e =>
    ⟨rightOfEdge e,
      mem_filter.mpr ⟨mem_univ _, ⟨leftOfEdge e, (left_right_of_edge e).2⟩⟩⟩
  have hinjE : Injective pickE := by
    intro e1 e2 h
    apply Subtype.ext
    have hr : rightOfEdge e1 = rightOfEdge e2 := congrArg Subtype.val h
    have h1 := left_right_of_edge e1
    have h2 := left_right_of_edge e2
    have ha : leftOfEdge e1 = leftOfEdge e2 :=
      succRel_left_unique hM h1.2 (hr ▸ h2.2)
    calc (e1 : Sym2 (α ⊕ α))
        = s(Sum.inl (leftOfEdge e1), Sum.inr (rightOfEdge e1)) := h1.1
      _ = s(Sum.inl (leftOfEdge e2), Sum.inr (rightOfEdge e2)) := by rw [ha, hr]
      _ = e2 := h2.1.symm
  have hle1 := Fintype.card_le_of_injective pickR hinjR
  have hle2 := Fintype.card_le_of_injective pickE hinjE
  apply le_antisymm
  · simpa [ProofLab.Konig.matchingCard, Fintype.card_coe] using hle2
  · simpa [ProofLab.Konig.matchingCard, Fintype.card_coe] using hle1

lemma sources_card_add_matchedRight :
    (sources M).card + (matchedRight M).card = Fintype.card α := by
  have := filter_card_add_filter_neg_card_eq_card
    (s := (univ : Finset α)) (p := hasPred M)
  simpa [sources, matchedRight, card_univ, add_comm] using this

lemma sources_card_add_matching (hM : M.IsMatching) :
    (sources M).card + ProofLab.Konig.matchingCard M = Fintype.card α := by
  rw [matchingCard_eq_matchedRight hM, sources_card_add_matchedRight]

lemma chainFrom_isChain (hM : M.IsMatching) (s : α) :
    IsChainSet (chainFrom M s) := by
  intro x hx y hy _hne
  have hx' : ReflTransGen (succRel M) s x := (mem_filter.mp hx).2
  have hy' : ReflTransGen (succRel M) s y := (mem_filter.mp hy).2
  rcases ReflTransGen.total_of_right_unique (succRel_right_unique hM) hx' hy' with h | h
  · exact Or.inl (rtg_le h)
  · exact Or.inr (rtg_le h)

lemma source_unique (hM : M.IsMatching) {s : α} (hs : ¬ hasPred M s) :
    ∀ {y t : α}, ReflTransGen (succRel M) s y → ¬ hasPred M t →
      ReflTransGen (succRel M) t y → s = t := by
  intro y t hsy
  induction hsy generalizing t with
  | refl =>
    intro _ht hty
    rcases ReflTransGen.cases_tail hty with h | ⟨c, _, hcs⟩
    · exact h
    · exact (hs ⟨c, hcs⟩).elim
  | tail _hpath hstep ih =>
    intro ht hty
    rcases ReflTransGen.cases_tail hty with h | ⟨c, htc, hcy⟩
    · subst h
      exact (ht ⟨_, hstep⟩).elim
    · have hc := succRel_left_unique hM hcy hstep
      subst hc
      exact ih ht htc

lemma chainFrom_disjoint (hM : M.IsMatching) {s t : α}
    (hs : ¬ hasPred M s) (ht : ¬ hasPred M t) (hst : s ≠ t) :
    Disjoint (chainFrom M s) (chainFrom M t) := by
  refine disjoint_left.mpr ?_
  intro y hys hyt
  have hy1 : ReflTransGen (succRel M) s y := (mem_filter.mp hys).2
  have hy2 : ReflTransGen (succRel M) t y := (mem_filter.mp hyt).2
  exact (hst (source_unique hM hs hy1 ht hy2)).elim

lemma exists_source (x : α) :
    ∃ s, ¬ hasPred M s ∧ ReflTransGen (succRel M) s x := by
  let S : Finset α := univ.filter fun y => ReflTransGen (succRel M) y x
  have hx : x ∈ S := mem_filter.mpr ⟨mem_univ x, ReflTransGen.refl⟩
  obtain ⟨s, hsS, hmin⟩ :=
    S.exists_min_image (fun y : α => (univ.filter fun z : α => z < y).card) ⟨x, hx⟩
  have hs : ReflTransGen (succRel M) s x := (mem_filter.mp hsS).2
  refine ⟨s, ?_, hs⟩
  rintro ⟨a, ha⟩
  have hlt : a < s := succRel_lt ha
  have haS : a ∈ S :=
    mem_filter.mpr ⟨mem_univ a, ReflTransGen.head ha hs⟩
  have hle : (univ.filter fun z : α => z < s).card ≤
      (univ.filter fun z : α => z < a).card := hmin a haS
  have hsub : (univ.filter fun z : α => z < a) ⊆
      univ.filter fun z : α => z < s := by
    intro z hz
    exact mem_filter.mpr ⟨mem_univ z, lt_trans (mem_filter.mp hz).2 hlt⟩
  have hanot : a ∉ univ.filter (fun z : α => z < a) := by
    intro hz
    exact lt_irrefl a (mem_filter.mp hz).2
  have hnotsub : ¬ (univ.filter fun z : α => z < s) ⊆
      univ.filter fun z : α => z < a := by
    intro hts
    exact hanot (hts (mem_filter.mpr ⟨mem_univ a, hlt⟩))
  have hssub : (univ.filter fun z : α => z < a) ⊂
      univ.filter fun z : α => z < s := ⟨hsub, hnotsub⟩
  exact (Nat.not_le.mpr (card_lt_card hssub)) hle

lemma mem_chainFrom_source (x : α) :
    ∃ s ∈ sources M, x ∈ chainFrom M s := by
  obtain ⟨s, hs, hrtg⟩ := exists_source (M := M) x
  exact ⟨s, mem_filter.mpr ⟨mem_univ s, hs⟩, mem_filter.mpr ⟨mem_univ x, hrtg⟩⟩

noncomputable def sourceEquiv (M : Subgraph (splitGraph : SimpleGraph (α ⊕ α))) :
    { x // x ∈ sources M } ≃ Fin (sources M).card :=
  Fintype.equivFinOfCardEq (Fintype.card_coe (sources M))

lemma matching_isChainPartition (hM : M.IsMatching) :
    IsChainPartition (fun i : Fin (sources M).card =>
      chainFrom M ((sourceEquiv M).symm i).1) := by
  refine ⟨?hchain, ?hdisj, ?hcov⟩
  · intro i
    exact chainFrom_isChain hM _
  · intro i j hij
    have hsi : ¬ hasPred M ((sourceEquiv M).symm i).1 :=
      (mem_filter.mp ((sourceEquiv M).symm i).2).2
    have hsj : ¬ hasPred M ((sourceEquiv M).symm j).1 :=
      (mem_filter.mp ((sourceEquiv M).symm j).2).2
    have hne : ((sourceEquiv M).symm i).1 ≠ ((sourceEquiv M).symm j).1 := by
      intro h
      exact hij ((sourceEquiv M).symm.injective (Subtype.ext h))
    exact chainFrom_disjoint hM hsi hsj hne
  · intro x
    obtain ⟨s, hs, hx⟩ := mem_chainFrom_source (M := M) x
    refine ⟨sourceEquiv M ⟨s, hs⟩, ?_⟩
    simpa using hx

end MatchingChains

/-- Dilworth 1950, finite posets: a chain partition of `univ` of size `width`.
Fulkerson split + maximum matching builds the chains; König `ν=τ` on
`splitGraph` is the *engine* (not a citation of König/Hall as Dilworth).
Not Mirsky. Not comparability-graph König. Finite `PartialOrder` only. -/
theorem dilworth :
    ∃ (n : ℕ) (chains : Fin n → Finset α) (A : Finset α),
      IsChainPartition chains ∧ IsAntichainSet A ∧ A.card = n ∧ n = width (α := α) := by
  obtain ⟨M, hM, hMcard⟩ := exists_max_matching (splitGraph : SimpleGraph (α ⊕ α))
  obtain ⟨C, hC, hCcard⟩ := exists_min_cover (splitGraph : SimpleGraph (α ⊕ α))
  have hντ :
      ProofLab.Konig.matchingNumber (splitGraph : SimpleGraph (α ⊕ α)) =
        ProofLab.Konig.vertexCoverNumber (splitGraph : SimpleGraph (α ⊕ α)) :=
    ProofLab.Konig.konig_bipartite splitGraph_colorable
  have hMc : ProofLab.Konig.matchingCard M = C.card := by
    rw [hMcard, hντ, hCcard]
  let S := sources M
  let chains : Fin S.card → Finset α := fun i =>
    chainFrom M ((sourceEquiv M).symm i).1
  have hP : IsChainPartition chains := matching_isChainPartition hM
  have hA : IsAntichainSet (uncovered C) := uncovered_isAntichain hC
  have hsum : S.card + C.card = Fintype.card α := by
    simpa [S, hMc] using sources_card_add_matching hM
  have hleA : S.card ≤ (uncovered C).card := by
    have huc := le_uncovered_card C
    omega
  have hwidth_le : width (α := α) ≤ S.card := width_le_chainPartition hP
  have hle_width : S.card ≤ width (α := α) := hleA.trans (le_width hA)
  have hn : S.card = width (α := α) := le_antisymm hle_width hwidth_le
  have hAcard : (uncovered C).card = S.card :=
    le_antisymm ((le_width hA).trans_eq hn.symm) hleA
  exact ⟨S.card, chains, uncovered C, hP, hA, hAcard, hn⟩

end ProofLab.Dilworth
