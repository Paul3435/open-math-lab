/-
Dilworth (1950): min chain-partition size = max antichain size (width)
on finite posets.

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 has `IsChain` / `IsAntichain` definitions only — no width,
no chain-partition number, no Dilworth. ProofLab `konig_bipartite` is the
*engine*, not the claim. Do not re-prove König. Not Hall. Not Mirsky.
Finite only. `PartialOrder`, not `Preorder`. Split graph uses strict `<`.
Do not König the comparability graph.

Pin: `catalog/problems/dilworth-poset/STATEMENT.md` (OPE-619 / Scout OPE-613).
Level A: easy inequality + empty / 2-element / total-chain / antichain-poset.
Level B: ∀ finite poset via Fulkerson split + `ProofLab.Konig.konig_bipartite`.
Zero `sorry`. Do not import `Archive.*`.
-/
import Mathlib.Order.Chain
import Mathlib.Order.Antichain
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Sort
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

end ProofLab.Dilworth
