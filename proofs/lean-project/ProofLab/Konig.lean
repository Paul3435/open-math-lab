/-
Kőnig (1931): matching number = vertex-cover number on bipartite graphs.

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 has `Subgraph.IsMatching` / `IsPerfectMatching` and
`Colorable 2`, but no vertex-cover predicate and no `ν = τ`.

Pin: `catalog/problems/konig-bipartite/STATEMENT.md` (OPE-580).
Encoding: Mathlib `SimpleGraph.Subgraph.IsMatching` + `Colorable 2`.
Zero `sorry`. Do not import `Archive.*`. Not Hall. Not edge-chromatic
Kőnig (`χ' = Δ`). Not König's lemma. Not Tutte. Not Dilworth.

Level A (this module): `IsVertexCover`; easy `ν ≤ τ` for *all* finite
graphs; empty / `K_{1,n}` / complete-bipartite equality.
Level B residual: full `Colorable 2 → ν = τ` (alternating paths or
Hall reduction). `K_3` is the load-bearing bipartite counterexample
(`ν = 1`, `τ = 2`).
-/
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

open Finset Function SimpleGraph
open SimpleGraph.Subgraph (mem_edgeSet)

noncomputable section
open Classical

namespace ProofLab.Konig

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

/-! ## Vertex covers and numerical invariants -/

/-- Vertex cover: every edge is incident to `C`. ProofLab definition;
Mathlib v4.10.0 has none. -/
def IsVertexCover (G : SimpleGraph V) (C : Finset V) : Prop :=
  ∀ ⦃u v⦄, G.Adj u v → u ∈ C ∨ v ∈ C

lemma univ_isVertexCover (G : SimpleGraph V) : IsVertexCover G univ := by
  intro _ _ _; exact Or.inl (mem_univ _)

lemma empty_isVertexCover_bot : IsVertexCover (⊥ : SimpleGraph V) ∅ := by
  intro _ _ h
  exact (bot_adj _ _).mp h |>.elim

lemma IsVertexCover.mono {C D : Finset V} (hC : IsVertexCover G C) (hsub : C ⊆ D) :
    IsVertexCover G D := by
  intro u v hadj
  rcases hC hadj with hu | hv
  · exact Or.inl (hsub hu)
  · exact Or.inr (hsub hv)

/-- Number of edges in a subgraph (matching number counts *edges*). -/
def matchingCard (M : Subgraph G) : ℕ :=
  Fintype.card M.edgeSet

lemma matchingCard_bot : matchingCard (⊥ : Subgraph G) = 0 := by
  simp only [matchingCard]
  have hempty : (⊥ : Subgraph G).edgeSet = ∅ := by
    ext e
    refine Sym2.inductionOn e fun u v => ?_
    constructor
    · intro h
      exact (mem_edgeSet.mp h : (⊥ : Subgraph G).Adj u v).elim
    · intro h
      exact h.elim
  simp [hempty]

lemma matchingCard_subgraphOfAdj {u v : V} (h : G.Adj u v) :
    matchingCard (G.subgraphOfAdj h) = 1 := by
  simp only [matchingCard]
  have heq : (G.subgraphOfAdj h).edgeSet = ({s(u, v)} : Set (Sym2 V)) := by
    ext e
    refine Sym2.inductionOn e fun a b => ?_
    change (G.subgraphOfAdj h).Adj a b ↔ s(a, b) ∈ ({s(u, v)} : Set (Sym2 V))
    simp [subgraphOfAdj_adj, eq_comm]
  simp [heq]

lemma matchingCard_le_card_sym2 (M : Subgraph G) :
    matchingCard M ≤ Fintype.card (Sym2 V) :=
  Fintype.card_le_of_injective (Subtype.val : M.edgeSet → Sym2 V) Subtype.coe_injective

lemma bot_isMatching (G : SimpleGraph V) : (⊥ : Subgraph G).IsMatching := by
  intro v hv
  exact (Set.not_mem_empty v hv).elim

/-- Matching sizes as a set of `ℕ` (avoid unbounded `sSup` on all of `ℕ`). -/
def matchingSizes (G : SimpleGraph V) : Set ℕ :=
  { n : ℕ | ∃ (M : Subgraph G), M.IsMatching ∧ matchingCard M = n }

def coverSizes (G : SimpleGraph V) : Set ℕ :=
  { n : ℕ | ∃ (C : Finset V), IsVertexCover G C ∧ C.card = n }

lemma matchingSizes_nonempty (G : SimpleGraph V) : (matchingSizes G).Nonempty :=
  ⟨0, ⊥, bot_isMatching G, matchingCard_bot⟩

lemma coverSizes_nonempty (G : SimpleGraph V) : (coverSizes G).Nonempty :=
  ⟨univ.card, univ, univ_isVertexCover G, rfl⟩

lemma bddAbove_matchingSizes (G : SimpleGraph V) : BddAbove (matchingSizes G) :=
  ⟨Fintype.card (Sym2 V), fun _ ⟨M, _, hn⟩ => hn ▸ matchingCard_le_card_sym2 M⟩

/-- Matching number `ν(G)`: max number of edges in a matching. -/
def matchingNumber (G : SimpleGraph V) : ℕ := sSup (matchingSizes G)

/-- Vertex-cover number `τ(G)`: min cardinality of a vertex cover. -/
def vertexCoverNumber (G : SimpleGraph V) : ℕ := sInf (coverSizes G)

lemma le_matchingNumber {M : Subgraph G} (hM : M.IsMatching) :
    matchingCard M ≤ matchingNumber G :=
  le_csSup (bddAbove_matchingSizes G) ⟨M, hM, rfl⟩

lemma vertexCoverNumber_le {C : Finset V} (hC : IsVertexCover G C) :
    vertexCoverNumber G ≤ C.card :=
  csInf_le (OrderBot.bddBelow _) ⟨C, hC, rfl⟩

/-! ## Easy inequality `ν ≤ τ` (all finite graphs) -/

lemma exists_mem_cover_of_mem_edgeSet {M : Subgraph G} {C : Finset V}
    (hC : IsVertexCover G C) {e : Sym2 V} (he : e ∈ M.edgeSet) :
    ∃ v ∈ C, v ∈ e := by
  revert he
  refine Sym2.inductionOn e fun u v he => ?_
  have hadj : M.Adj u v := SimpleGraph.Subgraph.mem_edgeSet.mp he
  rcases hC hadj.adj_sub with hu | hv
  · exact ⟨u, hu, by simp⟩
  · exact ⟨v, hv, by simp⟩

lemma matching_edges_of_shared_vertex {M : Subgraph G} (hM : M.IsMatching)
    {e f : Sym2 V} {x : V} (he : e ∈ M.edgeSet) (hf : f ∈ M.edgeSet)
    (hxe : x ∈ e) (hxf : x ∈ f) : e = f := by
  have h1 : M.Adj x (Sym2.Mem.other hxe) := by
    rw [← SimpleGraph.Subgraph.mem_edgeSet, Sym2.other_spec hxe]
    exact he
  have h2 : M.Adj x (Sym2.Mem.other hxf) := by
    rw [← SimpleGraph.Subgraph.mem_edgeSet, Sym2.other_spec hxf]
    exact hf
  obtain ⟨w, _hw, huniq⟩ := hM (M.edge_vert h1)
  have hw1 : Sym2.Mem.other hxe = w := huniq _ h1
  have hw2 : Sym2.Mem.other hxf = w := huniq _ h2
  calc
    e = s(x, Sym2.Mem.other hxe) := (Sym2.other_spec hxe).symm
    _ = s(x, w) := by rw [hw1]
    _ = s(x, Sym2.Mem.other hxf) := by rw [hw2]
    _ = f := Sym2.other_spec hxf

/-- Every matching edge hits a cover in a distinct vertex. -/
theorem matchingCard_le_coverCard {M : Subgraph G} {C : Finset V}
    (hM : M.IsMatching) (hC : IsVertexCover G C) :
    matchingCard M ≤ C.card := by
  let pick : M.edgeSet → { x : V // x ∈ C } := fun e =>
    ⟨Classical.choose (exists_mem_cover_of_mem_edgeSet hC e.2),
      (Classical.choose_spec (exists_mem_cover_of_mem_edgeSet hC e.2)).1⟩
  have hinj : Injective pick := by
    intro e1 e2 hp
    have he1 := Classical.choose_spec (exists_mem_cover_of_mem_edgeSet hC e1.2)
    have he2 := Classical.choose_spec (exists_mem_cover_of_mem_edgeSet hC e2.2)
    have hx : (pick e1).1 = (pick e2).1 := congrArg Subtype.val hp
    apply Subtype.ext
    have hxe1 : (pick e1).1 ∈ (e1 : Sym2 V) := he1.2
    have hxe2 : (pick e2).1 ∈ (e2 : Sym2 V) := he2.2
    exact matching_edges_of_shared_vertex hM e1.2 e2.2 (hx ▸ hxe1) hxe2
  have hcard := Fintype.card_le_of_injective pick hinj
  simpa [matchingCard, Fintype.card_coe] using hcard

/-- v1-b stretch: easy inequality for *all* finite graphs. -/
theorem matchingNumber_le_vertexCoverNumber (G : SimpleGraph V) :
    matchingNumber G ≤ vertexCoverNumber G := by
  refine csSup_le (matchingSizes_nonempty G) ?_
  intro n ⟨M, hM, hn⟩
  subst hn
  refine le_csInf (coverSizes_nonempty G) ?_
  intro m ⟨C, hC, hm⟩
  subst hm
  exact matchingCard_le_coverCard hM hC

/-! ## Empty / edgeless graph -/

lemma bot_colorable : (⊥ : SimpleGraph V).Colorable 2 :=
  ⟨Coloring.mk (fun _ => 0) (by intro _ _ h; exact (bot_adj _ _).mp h |>.elim)⟩

theorem matchingNumber_bot : matchingNumber (⊥ : SimpleGraph V) = 0 := by
  apply le_antisymm
  · refine csSup_le (matchingSizes_nonempty _) ?_
    intro n ⟨M, _, hn⟩
    have hempty : M.edgeSet = ∅ := by
      ext e
      simp only [Set.mem_empty_iff_false, iff_false]
      intro he
      have : e ∈ (⊥ : SimpleGraph V).edgeSet := M.edgeSet_subset he
      simp [edgeSet_bot] at this
    have : matchingCard M = 0 := by simp [matchingCard, hempty]
    omega
  · exact Nat.zero_le _

theorem vertexCoverNumber_bot : vertexCoverNumber (⊥ : SimpleGraph V) = 0 := by
  apply le_antisymm
  · simpa using
      vertexCoverNumber_le (G := (⊥ : SimpleGraph V)) empty_isVertexCover_bot
  · exact Nat.zero_le _

theorem konig_bot :
    matchingNumber (⊥ : SimpleGraph V) = vertexCoverNumber (⊥ : SimpleGraph V) := by
  rw [matchingNumber_bot, vertexCoverNumber_bot]

/-! ## Complete bipartite graphs `K_{m,n}` -/

lemma completeBipartite_colorable (α β : Type*) :
    (completeBipartiteGraph α β).Colorable 2 :=
  (CompleteBipartiteGraph.bicoloring α β).colorable

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- Matching of `K_{α,β}` induced by an embedding `α ↪ β` (saturates the left). -/
def bipMatching (f : α ↪ β) : Subgraph (completeBipartiteGraph α β) where
  verts := Set.range (Sum.inl : α → α ⊕ β) ∪ Set.range (fun a : α => Sum.inr (f a))
  Adj := fun v w =>
    match v, w with
    | .inl a, .inr b => f a = b
    | .inr b, .inl a => f a = b
    | _, _ => False
  adj_sub := by
    intro v w h
    cases v with
    | inl a =>
      cases w with
      | inl _ => cases h
      | inr _ => simp [completeBipartiteGraph]
    | inr b =>
      cases w with
      | inl _ => simp [completeBipartiteGraph]
      | inr _ => cases h
  edge_vert := by
    intro v w h
    cases v with
    | inl a => exact Set.mem_union_left _ ⟨a, rfl⟩
    | inr b =>
      cases w with
      | inl a => exact Set.mem_union_right _ ⟨a, congrArg Sum.inr h⟩
      | inr _ => cases h
  symm := by
    intro v w h
    cases v with
    | inl a =>
      cases w with
      | inl _ => cases h
      | inr b => exact h
    | inr b =>
      cases w with
      | inl a => exact h
      | inr _ => cases h

lemma bipMatching_isMatching (f : α ↪ β) : (bipMatching f).IsMatching := by
  intro v hv
  cases v with
  | inl a =>
    refine ⟨Sum.inr (f a), ?_, ?_⟩
    · change f a = f a; rfl
    · intro w hw
      cases w with
      | inl _ => cases hw
      | inr b =>
        change f a = b at hw
        rw [hw]
  | inr b =>
    have hb : ∃ a : α, f a = b := by
      cases hv with
      | inl h =>
        rcases h with ⟨a, ha⟩
        cases ha
      | inr h =>
        rcases h with ⟨a, ha⟩
        exact ⟨a, Sum.inr.inj ha⟩
    obtain ⟨a, rfl⟩ := hb
    refine ⟨Sum.inl a, ?_, ?_⟩
    · change f a = f a; rfl
    · intro w hw
      cases w with
      | inl a' =>
        change f a' = f a at hw
        rw [f.injective hw]
      | inr _ => cases hw

lemma bipMatching_edgeSet (f : α ↪ β) :
    (bipMatching f).edgeSet =
      Set.range (fun a : α => s(Sum.inl a, Sum.inr (f a))) := by
  ext e
  refine Sym2.inductionOn e fun v w => ?_
  constructor
  · intro h
    have hadj : (bipMatching f).Adj v w := SimpleGraph.Subgraph.mem_edgeSet.mp h
    cases v with
    | inl a =>
      cases w with
      | inl _ => cases hadj
      | inr b =>
        change f a = b at hadj
        subst hadj
        exact ⟨a, rfl⟩
    | inr b =>
      cases w with
      | inl a =>
        change f a = b at hadj
        subst hadj
        exact ⟨a, by rw [Sym2.eq_swap]⟩
      | inr _ => cases hadj
  · rintro ⟨a, ha⟩
    apply SimpleGraph.Subgraph.mem_edgeSet.mpr
    have hpair := Sym2.eq_iff.mp ha
    rcases hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · cases h1; cases h2; exact rfl
    · cases h1; cases h2; exact rfl

lemma bipMatching_card (f : α ↪ β) : matchingCard (bipMatching f) = Fintype.card α := by
  let g : α → (bipMatching f).edgeSet := fun a =>
    ⟨s(Sum.inl a, Sum.inr (f a)), by
      rw [bipMatching_edgeSet]; exact ⟨a, rfl⟩⟩
  have hinj : Injective g := by
    intro a1 a2 hg
    have h := Subtype.ext_iff.mp hg
    rcases (Sym2.eq_iff.mp h) with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact Sum.inl_injective h1
    · exact (Sum.inl_ne_inr h1).elim
  have hsurj : Surjective g := by
    intro e
    have he : (e : Sym2 (α ⊕ β)) ∈ Set.range (fun a : α => s(Sum.inl a, Sum.inr (f a))) := by
      rw [← bipMatching_edgeSet]; exact e.property
    obtain ⟨a, ha⟩ := he
    exact ⟨a, Subtype.ext ha⟩
  exact (Fintype.card_congr (Equiv.ofBijective g ⟨hinj, hsurj⟩)).symm

/-- Matching of `K_{α,β}` induced by an embedding `β ↪ α` (saturates the right). -/
def bipMatchingRight (f : β ↪ α) : Subgraph (completeBipartiteGraph α β) where
  verts := Set.range (fun b : β => Sum.inl (f b)) ∪ Set.range (Sum.inr : β → α ⊕ β)
  Adj := fun v w =>
    match v, w with
    | .inl a, .inr b => f b = a
    | .inr b, .inl a => f b = a
    | _, _ => False
  adj_sub := by
    intro v w h
    cases v with
    | inl a =>
      cases w with
      | inl _ => cases h
      | inr _ => simp [completeBipartiteGraph]
    | inr b =>
      cases w with
      | inl _ => simp [completeBipartiteGraph]
      | inr _ => cases h
  edge_vert := by
    intro v w h
    cases v with
    | inl a =>
      cases w with
      | inl _ => cases h
      | inr b => exact Set.mem_union_left _ ⟨b, congrArg Sum.inl h⟩
    | inr b => exact Set.mem_union_right _ ⟨b, rfl⟩
  symm := by
    intro v w h
    cases v with
    | inl a =>
      cases w with
      | inl _ => cases h
      | inr b => exact h
    | inr b =>
      cases w with
      | inl a => exact h
      | inr _ => cases h

lemma bipMatchingRight_isMatching (f : β ↪ α) : (bipMatchingRight f).IsMatching := by
  intro v hv
  cases v with
  | inl a =>
    have ha : ∃ b : β, f b = a := by
      cases hv with
      | inl h =>
        rcases h with ⟨b, hb⟩
        exact ⟨b, Sum.inl.inj hb⟩
      | inr h =>
        rcases h with ⟨b, hb⟩
        cases hb
    obtain ⟨b, rfl⟩ := ha
    refine ⟨Sum.inr b, ?_, ?_⟩
    · change f b = f b; rfl
    · intro w hw
      cases w with
      | inl _ => cases hw
      | inr b' =>
        change f b' = f b at hw
        rw [f.injective hw]
  | inr b =>
    refine ⟨Sum.inl (f b), ?_, ?_⟩
    · change f b = f b; rfl
    · intro w hw
      cases w with
      | inl a =>
        change f b = a at hw
        rw [hw]
      | inr _ => cases hw

lemma bipMatchingRight_edgeSet (f : β ↪ α) :
    (bipMatchingRight f).edgeSet =
      Set.range (fun b : β => s(Sum.inl (f b), Sum.inr b)) := by
  ext e
  refine Sym2.inductionOn e fun v w => ?_
  constructor
  · intro h
    have hadj : (bipMatchingRight f).Adj v w := SimpleGraph.Subgraph.mem_edgeSet.mp h
    cases v with
    | inl a =>
      cases w with
      | inl _ => cases hadj
      | inr b =>
        change f b = a at hadj
        subst hadj
        exact ⟨b, rfl⟩
    | inr b =>
      cases w with
      | inl a =>
        change f b = a at hadj
        subst hadj
        exact ⟨b, by rw [Sym2.eq_swap]⟩
      | inr _ => cases hadj
  · rintro ⟨b, hb⟩
    apply SimpleGraph.Subgraph.mem_edgeSet.mpr
    have hpair := Sym2.eq_iff.mp hb
    rcases hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · cases h1; cases h2; exact rfl
    · cases h1; cases h2; exact rfl

lemma bipMatchingRight_card (f : β ↪ α) :
    matchingCard (bipMatchingRight f) = Fintype.card β := by
  let g : β → (bipMatchingRight f).edgeSet := fun b =>
    ⟨s(Sum.inl (f b), Sum.inr b), by
      rw [bipMatchingRight_edgeSet]; exact ⟨b, rfl⟩⟩
  have hinj : Injective g := by
    intro b1 b2 hg
    have h := Subtype.ext_iff.mp hg
    rcases (Sym2.eq_iff.mp h) with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact Sum.inr_injective h2
    · exact (Sum.inl_ne_inr h1).elim
  have hsurj : Surjective g := by
    intro e
    have he : (e : Sym2 (α ⊕ β)) ∈
        Set.range (fun b : β => s(Sum.inl (f b), Sum.inr b)) := by
      rw [← bipMatchingRight_edgeSet]; exact e.property
    obtain ⟨b, hb⟩ := he
    exact ⟨b, Subtype.ext hb⟩
  exact (Fintype.card_congr (Equiv.ofBijective g ⟨hinj, hsurj⟩)).symm

def leftCover (α β : Type*) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] :
    Finset (α ⊕ β) :=
  univ.image Sum.inl

def rightCover (α β : Type*) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] :
    Finset (α ⊕ β) :=
  univ.image Sum.inr

lemma leftCover_card : (leftCover α β).card = Fintype.card α :=
  card_image_of_injective univ Sum.inl_injective

lemma rightCover_card : (rightCover α β).card = Fintype.card β :=
  card_image_of_injective univ Sum.inr_injective

lemma leftCover_isVertexCover :
    IsVertexCover (completeBipartiteGraph α β) (leftCover α β) := by
  intro u v h
  cases u with
  | inl a =>
    left
    exact mem_image.mpr ⟨a, mem_univ _, rfl⟩
  | inr b =>
    cases v with
    | inl a =>
      right
      exact mem_image.mpr ⟨a, mem_univ _, rfl⟩
    | inr _ =>
      simp [completeBipartiteGraph] at h

lemma rightCover_isVertexCover :
    IsVertexCover (completeBipartiteGraph α β) (rightCover α β) := by
  intro u v h
  cases u with
  | inl a =>
    cases v with
    | inl _ => simp [completeBipartiteGraph] at h
    | inr b =>
      right
      exact mem_image.mpr ⟨b, mem_univ _, rfl⟩
  | inr b =>
    left
    exact mem_image.mpr ⟨b, mem_univ _, rfl⟩

/-- Level A: Kőnig on complete bipartite graphs. -/
theorem konig_completeBipartite :
    matchingNumber (completeBipartiteGraph α β) =
      vertexCoverNumber (completeBipartiteGraph α β) := by
  have hle := matchingNumber_le_vertexCoverNumber (completeBipartiteGraph α β)
  rcases le_total (Fintype.card α) (Fintype.card β) with hα | hβ
  · obtain ⟨f⟩ := Embedding.nonempty_of_card_le hα
    have hν : Fintype.card α ≤ matchingNumber (completeBipartiteGraph α β) := by
      simpa [bipMatching_card] using le_matchingNumber (bipMatching_isMatching f)
    have hτ : vertexCoverNumber (completeBipartiteGraph α β) ≤ Fintype.card α := by
      simpa [leftCover_card] using
        vertexCoverNumber_le (C := leftCover α β) leftCover_isVertexCover
    omega
  · obtain ⟨f⟩ := Embedding.nonempty_of_card_le hβ
    have hν : Fintype.card β ≤ matchingNumber (completeBipartiteGraph α β) := by
      simpa [bipMatchingRight_card] using
        le_matchingNumber (bipMatchingRight_isMatching f)
    have hτ : vertexCoverNumber (completeBipartiteGraph α β) ≤ Fintype.card β := by
      simpa [rightCover_card] using
        vertexCoverNumber_le (C := rightCover α β) rightCover_isVertexCover
    omega

theorem konig_completeBipartite_eq_min :
    matchingNumber (completeBipartiteGraph α β) =
      min (Fintype.card α) (Fintype.card β) := by
  have hEq := konig_completeBipartite (α := α) (β := β)
  have _hle := matchingNumber_le_vertexCoverNumber (completeBipartiteGraph α β)
  rcases le_total (Fintype.card α) (Fintype.card β) with hα | hβ
  · obtain ⟨f⟩ := Embedding.nonempty_of_card_le hα
    have hν : Fintype.card α ≤ matchingNumber (completeBipartiteGraph α β) := by
      simpa [bipMatching_card] using le_matchingNumber (bipMatching_isMatching f)
    have hτ : vertexCoverNumber (completeBipartiteGraph α β) ≤ Fintype.card α := by
      simpa [leftCover_card] using
        vertexCoverNumber_le (C := leftCover α β) leftCover_isVertexCover
    have : matchingNumber (completeBipartiteGraph α β) = Fintype.card α := by omega
    simp [this, min_eq_left hα]
  · obtain ⟨f⟩ := Embedding.nonempty_of_card_le hβ
    have hν : Fintype.card β ≤ matchingNumber (completeBipartiteGraph α β) := by
      simpa [bipMatchingRight_card] using
        le_matchingNumber (bipMatchingRight_isMatching f)
    have hτ : vertexCoverNumber (completeBipartiteGraph α β) ≤ Fintype.card β := by
      simpa [rightCover_card] using
        vertexCoverNumber_le (C := rightCover α β) rightCover_isVertexCover
    have : matchingNumber (completeBipartiteGraph α β) = Fintype.card β := by omega
    simp [this, min_eq_right hβ]

/-- Level A sanity: star `K_{1,n}`. -/
theorem konig_star (n : ℕ) :
    matchingNumber (completeBipartiteGraph (Fin 1) (Fin n)) =
      vertexCoverNumber (completeBipartiteGraph (Fin 1) (Fin n)) :=
  konig_completeBipartite

/-! ## `K_3` landmine: bipartite is load-bearing (`ν = 1`, `τ = 2`) -/

lemma not_cover_singleton_fin3 (i : Fin 3) :
    ¬ IsVertexCover (⊤ : SimpleGraph (Fin 3)) {i} := by
  intro h
  fin_cases i
  · have := h (by decide : (⊤ : SimpleGraph (Fin 3)).Adj 1 2)
    simp at this
  · have := h (by decide : (⊤ : SimpleGraph (Fin 3)).Adj 0 2)
    simp at this
  · have := h (by decide : (⊤ : SimpleGraph (Fin 3)).Adj 0 1)
    simp at this

lemma cover_two_fin3 : IsVertexCover (⊤ : SimpleGraph (Fin 3)) ({0, 1} : Finset (Fin 3)) := by
  intro u v h
  fin_cases u <;> fin_cases v <;> simp [top_adj] at h ⊢

lemma cover_card_ge_two_fin3 {C : Finset (Fin 3)}
    (hC : IsVertexCover (⊤ : SimpleGraph (Fin 3)) C) : 2 ≤ C.card := by
  by_contra h
  have hc : C.card ≤ 1 := by omega
  interval_cases hcard : C.card
  · have h0 : C = ∅ := card_eq_zero.mp hcard
    have hadj : (⊤ : SimpleGraph (Fin 3)).Adj 0 1 := by decide
    have := hC hadj
    simp [h0] at this
  · obtain ⟨x, hx⟩ := card_eq_one.mp hcard
    rw [hx] at hC
    exact not_cover_singleton_fin3 x hC

lemma exists_eq_mk (e : Sym2 V) : ∃ u v : V, e = s(u, v) :=
  Sym2.inductionOn e fun u v => ⟨u, v, rfl⟩

lemma matchingCard_le_one_of_card_lt_four {M : Subgraph G} (hM : M.IsMatching)
    (hV : Fintype.card V < 4) : matchingCard M ≤ 1 := by
  by_contra h
  have h2 : 2 ≤ Fintype.card M.edgeSet := by simpa [matchingCard] using (show 2 ≤ matchingCard M by omega)
  obtain ⟨e, f, hne⟩ := Fintype.one_lt_card_iff.mp (lt_of_lt_of_le (by decide : (1 : ℕ) < 2) h2)
  obtain ⟨u, v, heq⟩ := exists_eq_mk (e : Sym2 V)
  obtain ⟨w, x, hfq⟩ := exists_eq_mk (f : Sym2 V)
  have he : s(u, v) ∈ M.edgeSet := by
    convert e.2
    exact heq.symm
  have hf : s(w, x) ∈ M.edgeSet := by
    convert f.2
    exact hfq.symm
  have hadj1 : M.Adj u v := SimpleGraph.Subgraph.mem_edgeSet.mp he
  have hadj2 : M.Adj w x := SimpleGraph.Subgraph.mem_edgeSet.mp hf
  have hu_ne_v : u ≠ v := hadj1.ne
  have hw_ne_x : w ≠ x := hadj2.ne
  have hdis : ({u, v} : Set V) ∩ {w, x} = ∅ := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false,
      iff_false, not_and]
    intro hy
    intro hy2
    have hye : y ∈ (s(u, v) : Sym2 V) := by
      rw [Sym2.mem_iff]
      simpa using hy
    have hyf : y ∈ (s(w, x) : Sym2 V) := by
      rw [Sym2.mem_iff]
      simpa using hy2
    have : (s(u, v) : Sym2 V) = s(w, x) :=
      matching_edges_of_shared_vertex hM he hf hye hyf
    have : (e : Sym2 V) = f := by
      calc
        (e : Sym2 V) = s(u, v) := heq
        _ = s(w, x) := this
        _ = f := hfq.symm
    exact hne (Subtype.ext this)
  -- four distinct vertices
  have hcard4 : ({u, v, w, x} : Finset V).card = 4 := by
    have hpair1 : ({u, v} : Finset V).card = 2 := card_pair hu_ne_v
    have hpair2 : ({w, x} : Finset V).card = 2 := card_pair hw_ne_x
    have hdisF : Disjoint ({u, v} : Finset V) ({w, x} : Finset V) := by
      rw [disjoint_iff_inter_eq_empty]
      ext y
      simp only [mem_inter, mem_insert, mem_singleton, not_mem_empty, iff_false, not_and]
      intro hy1 hy2
      have : y ∈ ({u, v} : Set V) ∩ {w, x} := by
        simp [Set.mem_inter_iff]
        exact ⟨by simpa using hy1, by simpa using hy2⟩
      simp [hdis] at this
    have : ({u, v} : Finset V) ∪ {w, x} = {u, v, w, x} := by
      ext y
      simp only [mem_union, mem_insert, mem_singleton]
      tauto
    rw [← this, card_union_of_disjoint hdisF, hpair1, hpair2]
  have : ({u, v, w, x} : Finset V).card ≤ Fintype.card V := card_le_univ _
  omega

theorem complete_three_matchingNumber :
    matchingNumber (⊤ : SimpleGraph (Fin 3)) = 1 := by
  apply le_antisymm
  · refine csSup_le (matchingSizes_nonempty _) ?_
    intro n ⟨M, hM, hn⟩
    have : matchingCard M ≤ 1 := matchingCard_le_one_of_card_lt_four hM (by decide)
    omega
  · have hadj : (⊤ : SimpleGraph (Fin 3)).Adj 0 1 := by decide
    have := le_matchingNumber (SimpleGraph.Subgraph.IsMatching.subgraphOfAdj hadj)
    simpa [matchingCard_subgraphOfAdj] using this

theorem complete_three_vertexCoverNumber :
    vertexCoverNumber (⊤ : SimpleGraph (Fin 3)) = 2 := by
  apply le_antisymm
  · have : ({0, 1} : Finset (Fin 3)).card = 2 := by decide
    have hle := vertexCoverNumber_le (G := (⊤ : SimpleGraph (Fin 3))) cover_two_fin3
    omega
  · refine le_csInf (coverSizes_nonempty _) ?_
    intro m ⟨C, hC, hm⟩
    have := cover_card_ge_two_fin3 hC
    omega

/-- `K_3` is the STATEMENT landmine: do not drop `Colorable 2`. -/
theorem complete_three_ne :
    matchingNumber (⊤ : SimpleGraph (Fin 3)) ≠
      vertexCoverNumber (⊤ : SimpleGraph (Fin 3)) := by
  rw [complete_three_matchingNumber, complete_three_vertexCoverNumber]
  decide

end ProofLab.Konig
