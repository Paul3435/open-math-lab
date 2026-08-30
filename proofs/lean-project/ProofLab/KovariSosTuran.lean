/-
Kővári–Sós–Turán (1954): Zarankiewicz integer counting form.

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 has `completeBipartiteGraph` / `neighborFinset` / `degree` /
`Nat.choose` and ZERO Kővári–Sós–Turán / Zarankiewicz theorem ident.

Pin: `catalog/problems/kovari-sos-turan/STATEMENT.md` (OPE-740; Scout OPE-735
prime; Director OPE-739). Encoding: `SimpleGraph (α ⊕ β)` with
`IsBipartiteSum` (no internal edges) and `NoKst` (every `s`-set of the left
part `α` has at most `t-1` common neighbours on the right part `β`).
Zero `sorry`. Do not import `Archive.*`.

This is **not** Turán (`SimpleGraph/Turan.lean` already upstream; OPE-25
negative control — never cite Turán as this gap).
This is **not** Mantel (Turán `r = 2`).
This is **not** the Zarankiewicz problem (exact `z(m,n;s,t)` is open, out of v1).
This is **not** sunflower / Kruskal–Katona / Oddtown / EKR.
This is **not** combinatorial Nullstellensatz.
This is **not** pentagonal-number-theorem.
Parts `α` (s-side) and `β` (t-side) do not swap: the namesake sums
`binom(deg b, s)` over the **t-side**. `1 ≤ t` is load-bearing for `ℕ`
subtraction; `1 ≤ s` is load-bearing so `Nat.choose _ s` is the interesting
binomial. Real-exponent edge form / Erdős–Stone / non-bipartite `K_{s,t}`-free
are out of v1.

Level A: `s = t = 2` counting (no `K_{2,2}` / C₄ between the parts) +
empty / edgeless / complete-bipartite `K_{1,n}` landmines. Glue, **not**
labelled Kővári–Sós–Turán. Zero sorry.
Level B: namesake `kovari_sos_turan` by double counting pairs `(S, b)` with
`S ⊆ α`, `|S| = s`, `S` contained in the left-neighbourhood of `b`.
-/
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

set_option maxHeartbeats 400000

open Finset Function SimpleGraph

noncomputable section
open Classical

namespace ProofLab.KovariSosTuran

variable {α β : Type*}

/-! ## STATEMENT pin -/

/-- No internal edges on either part of `α ⊕ β`. Equivalently
`G ≤ completeBipartiteGraph α β`. Not `Colorable 2` (König already consumed
that as `ν = τ`). -/
def IsBipartiteSum (G : SimpleGraph (α ⊕ β)) : Prop :=
  (∀ a a' : α, ¬ G.Adj (.inl a) (.inl a')) ∧
  (∀ b b' : β, ¬ G.Adj (.inr b) (.inr b'))

/-- Every `s`-set of the **left** part `α` has at most `t - 1` common
neighbours on the **right** part `β`. Exactly “no `K_{s,t}` with the s-side
in `α` and the t-side in `β`.” -/
def NoKst [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (G : SimpleGraph (α ⊕ β)) [DecidableRel G.Adj] (s t : ℕ) : Prop :=
  ∀ S : Finset α, S.card = s →
    (Finset.univ.filter (fun b : β => ∀ a ∈ S, G.Adj (.inl a) (.inr b))).card
      ≤ t - 1

/-- Left-neighbourhood of a right vertex. Engine, not a second id. -/
def leftNhbds [Fintype α] [DecidableEq α]
    (G : SimpleGraph (α ⊕ β)) [DecidableRel G.Adj] (b : β) : Finset α :=
  univ.filter (fun a : α => G.Adj (.inl a) (.inr b))

/-- Common neighbourhood on `β` of a left set `S`. Engine. -/
def commonNhbds [Fintype β] [DecidableEq β]
    (G : SimpleGraph (α ⊕ β)) [DecidableRel G.Adj] (S : Finset α) : Finset β :=
  univ.filter (fun b : β => ∀ a ∈ S, G.Adj (.inl a) (.inr b))

/-! ## Bipartite pin glue (not labelled KST) -/

lemma isBipartiteSum_iff_le_complete (G : SimpleGraph (α ⊕ β)) :
    IsBipartiteSum G ↔ G ≤ completeBipartiteGraph α β := by
  constructor
  · intro h u v huv
    cases u with
    | inl a =>
      cases v with
      | inl a' => exact (h.1 a a' huv).elim
      | inr _ => simp [completeBipartiteGraph]
    | inr b =>
      cases v with
      | inl _ => simp [completeBipartiteGraph]
      | inr b' => exact (h.2 b b' huv).elim
  · intro hle
    constructor
    · intro a a' hab
      have := hle hab
      simp [completeBipartiteGraph] at this
    · intro b b' hbb
      have := hle hbb
      simp [completeBipartiteGraph] at this

lemma isBipartiteSum_bot : IsBipartiteSum (⊥ : SimpleGraph (α ⊕ β)) := by
  constructor <;> intro _ _ h <;> exact (bot_adj _ _).mp h |>.elim

lemma isBipartiteSum_complete : IsBipartiteSum (completeBipartiteGraph α β) :=
  (isBipartiteSum_iff_le_complete _).mpr le_rfl

/-! ## Neighbourhood / degree dictionary -/

variable [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
variable (G : SimpleGraph (α ⊕ β)) [DecidableRel G.Adj]

lemma mem_leftNhbds {a : α} {b : β} :
    a ∈ leftNhbds G b ↔ G.Adj (.inl a) (.inr b) := by
  simp [leftNhbds]

lemma subset_leftNhbds_iff {S : Finset α} {b : β} :
    S ⊆ leftNhbds G b ↔ ∀ a ∈ S, G.Adj (.inl a) (.inr b) := by
  simp [subset_iff, mem_leftNhbds]

lemma mem_commonNhbds {S : Finset α} {b : β} :
    b ∈ commonNhbds G S ↔ ∀ a ∈ S, G.Adj (.inl a) (.inr b) := by
  simp [commonNhbds]

lemma commonNhbds_eq_filter_subset {S : Finset α} :
    commonNhbds G S = univ.filter (fun b : β => S ⊆ leftNhbds G b) := by
  ext b
  simp [mem_commonNhbds, subset_leftNhbds_iff]

lemma neighborFinset_inr_eq_map (hbi : IsBipartiteSum G) (b : β) :
    G.neighborFinset (.inr b) = (leftNhbds G b).map Embedding.inl := by
  ext w
  simp only [mem_neighborFinset, mem_map, Embedding.inl_apply]
  constructor
  · intro hw
    cases w with
    | inl a =>
      exact ⟨a, (mem_leftNhbds G).mpr (hw.symm), rfl⟩
    | inr b' =>
      exact (hbi.2 b b' hw).elim
  · rintro ⟨a, ha, rfl⟩
    exact ((mem_leftNhbds G).mp ha).symm

lemma degree_inr_eq_card_leftNhbds (hbi : IsBipartiteSum G) (b : β) :
    G.degree (.inr b) = (leftNhbds G b).card := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_inr_eq_map G hbi]
  simp [card_map]

lemma powersetCard_leftNhbds_eq_filter (b : β) {s : ℕ} :
    (leftNhbds G b).powersetCard s =
      ((univ : Finset α).powersetCard s).filter (fun S => S ⊆ leftNhbds G b) := by
  ext S
  simp only [mem_powersetCard, mem_filter, subset_univ, true_and]
  constructor
  · intro h
    exact ⟨h.2, h.1⟩
  · intro h
    exact ⟨h.2, h.1⟩

/-! ## Level A: empty / edgeless / `K_{1,n}` / `s = t = 2` (not labelled KST) -/

lemma noKst_bot {s t : ℕ} (hs : 1 ≤ s) (_ht : 1 ≤ t) :
    NoKst (⊥ : SimpleGraph (α ⊕ β)) s t := by
  intro S hS
  have hpos : 0 < S.card := by
    rw [hS]
    exact hs
  obtain ⟨a, ha⟩ := card_pos.mp hpos
  have hempty :
      (univ.filter (fun b : β => ∀ x ∈ S, (⊥ : SimpleGraph (α ⊕ β)).Adj (.inl x) (.inr b))) =
        (∅ : Finset β) := by
    ext b
    simp only [mem_filter, mem_univ, true_and, not_mem_empty, iff_false]
    intro h
    exact (bot_adj _ _).mp (h a ha)
  rw [hempty, card_empty]
  exact Nat.zero_le _

lemma noKst_star_right (n : ℕ) :
    NoKst (completeBipartiteGraph (Fin n) Unit) 2 2 := by
  intro S _
  have hsub :
      (univ.filter (fun b : Unit =>
          ∀ a ∈ S, (completeBipartiteGraph (Fin n) Unit).Adj (.inl a) (.inr b))) ⊆
        (univ : Finset Unit) :=
    filter_subset _ _
  exact (card_le_card hsub).trans (by simp)

lemma noKst_star_left (n : ℕ) :
    NoKst (completeBipartiteGraph Unit (Fin n)) 2 2 := by
  intro S hS
  have hle : S.card ≤ Fintype.card Unit := card_le_univ S
  simp only [Fintype.card_unit] at hle
  omega

/-- Edgeless / empty graph: `∑_b binom(0, 2) = 0 ≤ binom(|α|, 2)`. Glue. -/
theorem sum_choose_two_bot :
    ∑ b : β, Nat.choose ((⊥ : SimpleGraph (α ⊕ β)).degree (.inr b)) 2 ≤
      Nat.choose (Fintype.card α) 2 := by
  have hdeg : ∀ b : β, (⊥ : SimpleGraph (α ⊕ β)).degree (.inr b) = 0 := by
    intro b
    rw [degree_inr_eq_card_leftNhbds _ isBipartiteSum_bot]
    simp [leftNhbds, bot_adj]
  simp [hdeg]

/-- Complete bipartite `K_{n,1}` (star, centre on the t-side): equality
`binom(n, 2) ≤ binom(n, 2)`. Glue, not labelled KST. -/
theorem sum_choose_two_star_right (n : ℕ) :
    ∑ b : Unit, Nat.choose
        ((completeBipartiteGraph (Fin n) Unit).degree (.inr b)) 2 ≤
      Nat.choose (Fintype.card (Fin n)) 2 := by
  have hdeg : ∀ b : Unit,
      (completeBipartiteGraph (Fin n) Unit).degree (.inr b) = n := by
    intro b
    rw [degree_inr_eq_card_leftNhbds _ isBipartiteSum_complete]
    simp [leftNhbds, completeBipartiteGraph, Fintype.card_fin]
  simp [hdeg, Fintype.card_fin]

/-- Complete bipartite `K_{1,n}` (star, centre on the s-side):
`∑ binom(1, 2) = 0 ≤ binom(1, 2) = 0`. Glue, not labelled KST. -/
theorem sum_choose_two_star_left (n : ℕ) :
    ∑ b : Fin n, Nat.choose
        ((completeBipartiteGraph Unit (Fin n)).degree (.inr b)) 2 ≤
      Nat.choose (Fintype.card Unit) 2 := by
  have hdeg : ∀ b : Fin n,
      (completeBipartiteGraph Unit (Fin n)).degree (.inr b) = 1 := by
    intro b
    rw [degree_inr_eq_card_leftNhbds _ isBipartiteSum_complete]
    simp [leftNhbds, completeBipartiteGraph, Fintype.card_unit]
  simp [hdeg]

/-! ## Double-counting engine (not labelled KST) -/

lemma sum_choose_eq_sum_commonNhbds (hbi : IsBipartiteSum G) {s : ℕ} :
    ∑ b : β, Nat.choose (G.degree (.inr b)) s =
      ∑ S ∈ (univ : Finset α).powersetCard s, (commonNhbds G S).card := by
  let r : Finset α → β → Prop := fun S b => S ⊆ leftNhbds G b
  have hleft :
      ∑ b : β, Nat.choose (G.degree (.inr b)) s =
        ∑ b ∈ (univ : Finset β),
          (((univ : Finset α).powersetCard s).bipartiteBelow r b).card := by
    refine sum_congr rfl fun b _ => ?_
    rw [degree_inr_eq_card_leftNhbds G hbi, ← card_powersetCard,
      powersetCard_leftNhbds_eq_filter]
    rfl
  have hright :
      ∑ S ∈ (univ : Finset α).powersetCard s, (commonNhbds G S).card =
        ∑ S ∈ (univ : Finset α).powersetCard s,
          ((univ : Finset β).bipartiteAbove r S).card := by
    refine sum_congr rfl fun S _ => ?_
    rw [commonNhbds_eq_filter_subset]
    rfl
  rw [hleft, hright]
  exact (sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow r).symm

lemma card_commonNhbds_eq_noKst_filter (S : Finset α) :
    (commonNhbds G S).card =
      (univ.filter (fun b : β => ∀ a ∈ S, G.Adj (.inl a) (.inr b))).card := by
  apply congrArg Finset.card
  ext b
  simp [commonNhbds]

lemma sum_commonNhbds_le {s t : ℕ} (hno : NoKst G s t) :
    ∑ S ∈ (univ : Finset α).powersetCard s, (commonNhbds G S).card ≤
      (t - 1) * Nat.choose (Fintype.card α) s := by
  have hle :
      ∑ S ∈ (univ : Finset α).powersetCard s, (commonNhbds G S).card ≤
        ∑ S ∈ (univ : Finset α).powersetCard s, (t - 1) := by
    refine sum_le_sum fun S hS => ?_
    have hcard : S.card = s := (mem_powersetCard.mp hS).2
    rw [card_commonNhbds_eq_noKst_filter]
    exact hno S hcard
  have hconst :
      ∑ S ∈ (univ : Finset α).powersetCard s, (t - 1) =
        (t - 1) * ((univ : Finset α).powersetCard s).card := by
    simp [sum_const, nsmul_eq_mul, mul_comm]
  have hch :
      ((univ : Finset α).powersetCard s).card = Nat.choose (Fintype.card α) s := by
    simp [card_powersetCard, card_univ]
  exact hle.trans (by rw [hconst, hch])

/-- Level A counting form (`s = t = 2`): no `K_{2,2}` / C₄ between the parts.
Glue, **not** labelled Kővári–Sós–Turán. -/
theorem sum_choose_two_le (hbi : IsBipartiteSum G) (hno : NoKst G 2 2) :
    ∑ b : β, Nat.choose (G.degree (.inr b)) 2 ≤
      Nat.choose (Fintype.card α) 2 := by
  have h := (sum_choose_eq_sum_commonNhbds G hbi (s := 2)).trans_le
    (sum_commonNhbds_le (s := 2) (t := 2) G hno)
  simpa using h

/-! ## Level B: namesake integer counting form -/

/-- Kővári–Sós–Turán 1954, integer counting form. Not Turán, not Mantel, not
exact Zarankiewicz. Double count pairs `(S, b)` with `|S| = s` and `S`
contained in the left-neighbourhood of `b`. -/
theorem kovari_sos_turan {s t : ℕ} (hs : 1 ≤ s) (ht : 1 ≤ t)
    (hbi : IsBipartiteSum G) (hno : NoKst G s t) :
    ∑ b : β, Nat.choose (G.degree (.inr b)) s ≤
      (t - 1) * Nat.choose (Fintype.card α) s := by
  have _hs := hs
  have _ht := ht
  exact (sum_choose_eq_sum_commonNhbds G hbi).trans_le
    (sum_commonNhbds_le G hno)

end ProofLab.KovariSosTuran
