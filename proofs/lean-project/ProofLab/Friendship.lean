/-
Friendship theorem (Erdős–Rényi–Sós 1966), finite graphs only.

status: known-classical, formalize-only, **no novelty claim**.
        Mathlib v4.10.0 has `commonNeighbors` + `IsSRGWith` but the
        theorem lives only in Archive (not `Mathlib/**`).

Level A (this PR): Dutch windmill construction satisfies `IsFriendship`.
Level B (this PR): universal friend ⇒ windmill-of-triangles (`IsWindmillAround`).
Level C (residual): no-universal-friend ⇒ regular ⇒ `IsSRGWith n k 1 1` ⇒
         contradiction. Mathlib Archive has `Theorems100.friendship_theorem`.

Pin: `catalog/problems/friendship-windmill/STATEMENT.md` (OPE-535).
Encoding: Mathlib `SimpleGraph`; finite is load-bearing. Zero `sorry`.
-/

import Mathlib.Combinatorics.SimpleGraph.Finite

open Finset SimpleGraph

namespace ProofLab.Friendship

variable {V : Type*}

/-- Hypothesis of the friendship theorem (STATEMENT.md). -/
def IsFriendship (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] : Prop :=
  ∀ ⦃v w : V⦄, v ≠ w → Fintype.card (G.commonNeighbors v w) = 1

/-- Dutch windmill around hub `u`: `u` meets every other vertex, and the
remaining edges are a matching (triangles through `u`, pairwise disjoint
off the hub). -/
def IsWindmillAround (G : SimpleGraph V) (u : V) : Prop :=
  (∀ w : V, w ≠ u → G.Adj u w) ∧
    ∀ v : V, v ≠ u → ∃! w : V, w ≠ u ∧ G.Adj v w

variable [Fintype V] [DecidableEq V]

/-! ## Degree dictionary -/

lemma neighborFinset_subset_erase (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) :
    G.neighborFinset u ⊆ univ.erase u := by
  intro x hx
  exact mem_erase.mpr ⟨(G.ne_of_adj ((mem_neighborFinset G u x).mp hx)).symm, mem_univ x⟩

lemma degree_eq_card_sub_one_iff (G : SimpleGraph V) [DecidableRel G.Adj] {u : V} :
    G.degree u = Fintype.card V - 1 ↔ ∀ w : V, w ≠ u → G.Adj u w := by
  constructor
  · intro hd w hw
    have heq : G.neighborFinset u = univ.erase u :=
      Finset.eq_of_subset_of_card_le (neighborFinset_subset_erase G u) (by
        have : (univ.erase u).card = Fintype.card V - 1 := card_erase_of_mem (mem_univ u)
        rw [this, ← hd]
        exact le_rfl)
    exact (mem_neighborFinset G u w).mp (heq.symm ▸ mem_erase.mpr ⟨hw, mem_univ w⟩)
  · intro h
    have heq : G.neighborFinset u = univ.erase u := by
      ext w
      constructor
      · intro hw
        exact mem_erase.mpr
          ⟨(G.ne_of_adj ((mem_neighborFinset G u w).mp hw)).symm, mem_univ w⟩
      · intro hw
        exact (mem_neighborFinset G u w).mpr (h w (mem_erase.mp hw).1)
    change (G.neighborFinset u).card = _
    rw [heq, card_erase_of_mem (mem_univ u), card_univ]

/-- Card of a singleton set, without rewriting the `Fintype` instance. -/
lemma card_eq_one_of_eq_singleton {α : Type*} [DecidableEq α] {s : Set α} {x : α}
    [Fintype s] (h : s = {x}) : Fintype.card s = 1 :=
  Fintype.card_eq_one_iff.mpr
    ⟨⟨x, show x ∈ s from h.symm ▸ Set.mem_singleton x⟩, fun ⟨y, hy⟩ =>
      Subtype.ext (by
        have : y ∈ ({x} : Set α) := h ▸ hy
        exact this)⟩

/-! ## Level A construction: Dutch windmill on `2k+1` vertices -/

abbrev WindmillV (k : ℕ) := Option (Fin k × Bool)

instance instFintypeWindmillV (k : ℕ) : Fintype (WindmillV k) where
  elems :=
    insert (none : WindmillV k)
      ((Finset.univ : Finset (Fin k)).biUnion fun i =>
        ({some (i, false), some (i, true)} : Finset (WindmillV k)))
  complete := by
    intro x
    cases x with
    | none => simp
    | some p =>
      rcases p with ⟨i, b⟩
      cases b <;> simp [mem_biUnion]

instance instDecidableEqWindmillV (k : ℕ) : DecidableEq (WindmillV k) :=
  inferInstanceAs (DecidableEq (Option (Fin k × Bool)))

def dutchWindmill (k : ℕ) : SimpleGraph (WindmillV k) where
  Adj
    | none, some _ => True
    | some _, none => True
    | some (i, b), some (j, c) => i = j ∧ b ≠ c
    | none, none => False
  symm := by
    intro x y h
    cases x with
    | none =>
      cases y with
      | none => cases h
      | some _ => trivial
    | some x =>
      cases y with
      | none => trivial
      | some y =>
        rcases x with ⟨i, b⟩
        rcases y with ⟨j, c⟩
        exact ⟨h.1.symm, h.2.symm⟩
  loopless := by
    intro x h
    cases x with
    | none => exact h
    | some p =>
      rcases p with ⟨_, b⟩
      exact h.2 rfl

instance decidableAdjDutchWindmill (k : ℕ) : DecidableRel (dutchWindmill k).Adj :=
  fun x y =>
    match x, y with
    | none, none => .isFalse fun h => h
    | none, some _ => .isTrue trivial
    | some _, none => .isTrue trivial
    | some (i, b), some (j, c) =>
        if h : i = j ∧ b ≠ c then .isTrue h else .isFalse h

lemma ne_bool_not (b : Bool) : b ≠ !b := by cases b <;> simp

lemma eq_not_of_ne_bool {b c : Bool} (h : b ≠ c) : c = !b := by
  cases b <;> cases c <;> simp at h ⊢

lemma adj_hub_leaf (k : ℕ) (p : Fin k × Bool) :
    (dutchWindmill k).Adj none (some p) := trivial

lemma adj_leaf_hub (k : ℕ) (p : Fin k × Bool) :
    (dutchWindmill k).Adj (some p) none := trivial

lemma adj_leaves (k : ℕ) (i j : Fin k) (b c : Bool) :
    (dutchWindmill k).Adj (some (i, b)) (some (j, c)) ↔ i = j ∧ b ≠ c := Iff.rfl

lemma neighborSet_leaf (k : ℕ) (i : Fin k) (b : Bool) (x : WindmillV k) :
    x ∈ (dutchWindmill k).neighborSet (some (i, b)) ↔
      x = none ∨ x = some (i, !b) := by
  cases x with
  | none => simp [mem_neighborSet, dutchWindmill]
  | some p =>
    rcases p with ⟨j, c⟩
    constructor
    · intro h
      obtain ⟨rfl, hbc⟩ := (adj_leaves k i j b c).mp h
      refine Or.inr ?_
      simp [eq_not_of_ne_bool hbc]
    · intro h
      rcases h with h | h
      · cases h
      · injection h with hpair
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
        exact ⟨rfl, ne_bool_not b⟩

lemma commonNeighbors_hub_leaf (k : ℕ) (i : Fin k) (b : Bool) :
    (dutchWindmill k).commonNeighbors none (some (i, b)) = {some (i, !b)} := by
  ext x
  simp only [mem_commonNeighbors, Set.mem_singleton_iff]
  constructor
  · intro hx
    have hxLeaf : x = none ∨ x = some (i, !b) := (neighborSet_leaf k i b x).mp hx.2
    cases hxLeaf with
    | inl hnone =>
      subst hnone
      exact False.elim ((dutchWindmill k).loopless none hx.1)
    | inr hsome =>
      exact hsome
  · rintro rfl
    exact ⟨adj_hub_leaf k (i, !b), (neighborSet_leaf k i b _).mpr (Or.inr rfl)⟩

lemma commonNeighbors_partners (k : ℕ) (i : Fin k) {b c : Bool} (hbc : b ≠ c) :
    (dutchWindmill k).commonNeighbors (some (i, b)) (some (i, c)) = {none} := by
  have hc : c = !b := eq_not_of_ne_bool hbc
  subst c
  ext x
  simp only [mem_commonNeighbors, Set.mem_singleton_iff]
  constructor
  · intro hx
    have h1 := (neighborSet_leaf k i b x).mp hx.1
    have h2 := (neighborSet_leaf k i (!b) x).mp hx.2
    cases h1 with
    | inl hnone => exact hnone
    | inr hsome =>
      cases h2 with
      | inl hnone =>
        exact Option.noConfusion (hsome.symm.trans hnone)
      | inr hsame =>
        have this := Option.some.inj (hsome.symm.trans hsame)
        have hb := (Prod.mk.inj this).2
        cases b <;> cases hb
  · rintro rfl
    exact ⟨adj_leaf_hub k (i, b), adj_leaf_hub k (i, !b)⟩

lemma commonNeighbors_diff_blocks (k : ℕ) {i j : Fin k} (hij : i ≠ j) (b c : Bool) :
    (dutchWindmill k).commonNeighbors (some (i, b)) (some (j, c)) = {none} := by
  ext x
  simp only [mem_commonNeighbors, Set.mem_singleton_iff]
  constructor
  · intro hx
    have h1 := (neighborSet_leaf k i b x).mp hx.1
    have h2 := (neighborSet_leaf k j c x).mp hx.2
    cases h1 with
    | inl hnone => exact hnone
    | inr hsome =>
      cases h2 with
      | inl hnone =>
        exact Option.noConfusion (hsome.symm.trans hnone)
      | inr hsame =>
        have hij' : i = j := (Prod.mk.inj (Option.some.inj (hsome.symm.trans hsame))).1
        exact False.elim (hij hij')
  · rintro rfl
    exact ⟨adj_leaf_hub k (i, b), adj_leaf_hub k (j, c)⟩

theorem dutchWindmill_isFriendship (k : ℕ) : IsFriendship (dutchWindmill k) := by
  intro v w hvw
  cases v with
  | none =>
    cases w with
    | none => exact (hvw rfl).elim
    | some p =>
      rcases p with ⟨i, b⟩
      exact card_eq_one_of_eq_singleton (commonNeighbors_hub_leaf k i b)
  | some p =>
    cases w with
    | none =>
      rcases p with ⟨i, b⟩
      have hset : (dutchWindmill k).commonNeighbors (some (i, b)) none =
          {some (i, !b)} := by
        rw [commonNeighbors_symm]
        exact commonNeighbors_hub_leaf k i b
      exact card_eq_one_of_eq_singleton hset
    | some q =>
      rcases p with ⟨i, b⟩
      rcases q with ⟨j, c⟩
      by_cases hij : i = j
      · subst i
        have hbc : b ≠ c := by
          intro hbc; subst hbc; exact hvw rfl
        exact card_eq_one_of_eq_singleton (commonNeighbors_partners k _ hbc)
      · exact card_eq_one_of_eq_singleton (commonNeighbors_diff_blocks k hij b c)

theorem dutchWindmill_isWindmillAround (k : ℕ) :
    IsWindmillAround (dutchWindmill k) none := by
  constructor
  · intro w hw
    cases w with
    | none => exact (hw rfl).elim
    | some _ => trivial
  · intro v hv
    cases v with
    | none => exact (hv rfl).elim
    | some p =>
      rcases p with ⟨i, b⟩
      refine ⟨some (i, !b), ⟨Option.some_ne_none _, ⟨rfl, ne_bool_not b⟩⟩, ?_⟩
      intro w hw
      cases w with
      | none => exact (hw.1 rfl).elim
      | some q =>
        rcases q with ⟨j, c⟩
        obtain ⟨rfl, hbc⟩ := hw.2
        exact congrArg some (Prod.ext rfl (eq_not_of_ne_bool hbc))

theorem dutchWindmill_hub_degree (k : ℕ) :
    (dutchWindmill k).degree none = Fintype.card (WindmillV k) - 1 :=
  (degree_eq_card_sub_one_iff (dutchWindmill k)).2 (dutchWindmill_isWindmillAround k).1

/-! ## Level A: abstract windmill ⇒ friendship -/

lemma neighborSet_leaf_of_windmill (G : SimpleGraph V) {u v p : V}
    (h : IsWindmillAround G u) (hv : v ≠ u)
    (hp : p ≠ u ∧ G.Adj v p)
    (huniq : ∀ w, w ≠ u ∧ G.Adj v w → w = p) :
    G.neighborSet v = {u, p} := by
  ext x
  simp only [mem_neighborSet, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hxv
    by_cases hxu : x = u
    · exact Or.inl hxu
    · exact Or.inr (huniq x ⟨hxu, hxv⟩)
  · rintro (rfl | rfl)
    · exact G.symm (h.1 v hv)
    · exact hp.2

theorem isFriendship_of_isWindmillAround (G : SimpleGraph V) [DecidableRel G.Adj] {u : V}
    (hwm : IsWindmillAround G u) : IsFriendship G := by
  intro v w hvw
  have leaf : ∀ {x : V}, x ≠ u →
      ∃ p, p ≠ u ∧ G.Adj x p ∧ G.neighborSet x = {u, p} := by
    intro x hx
    obtain ⟨p, hp, huq⟩ := hwm.2 x hx
    exact ⟨p, hp.1, hp.2, neighborSet_leaf_of_windmill G hwm hx hp huq⟩
  if hvu : v = u then
    have hw : w ≠ u := fun h => hvw (hvu.trans h.symm)
    obtain ⟨p, hpU, hpAdj, nset⟩ := leaf hw
    have hset : G.commonNeighbors v w = {p} := by
      rw [hvu]
      ext x
      simp only [mem_commonNeighbors, Set.mem_singleton_iff]
      constructor
      · intro hx
        have memN : x = u ∨ x = p := by
          have : x ∈ ({u, p} : Set V) := nset ▸ hx.2
          simpa using this
        rcases memN with hxU | hxP
        · exact False.elim (G.loopless u (hxU ▸ hx.1))
        · exact hxP
      · rintro hxp
        rw [hxp]
        exact ⟨hwm.1 p hpU, hpAdj⟩
    exact card_eq_one_of_eq_singleton hset
  else if hwu : w = u then
    obtain ⟨p, hpU, hpAdj, nset⟩ := leaf hvu
    have hset : G.commonNeighbors v w = {p} := by
      rw [hwu]
      ext x
      simp only [mem_commonNeighbors, Set.mem_singleton_iff]
      constructor
      · intro hx
        have memN : x = u ∨ x = p := by
          have : x ∈ ({u, p} : Set V) := nset ▸ hx.1
          simpa using this
        rcases memN with hxU | hxP
        · exact False.elim (G.loopless u (hxU ▸ hx.2))
        · exact hxP
      · rintro hxp
        rw [hxp]
        exact ⟨hpAdj, hwm.1 p hpU⟩
    exact card_eq_one_of_eq_singleton hset
  else
    obtain ⟨pv, pvU, pvAdj, nv⟩ := leaf hvu
    obtain ⟨pw, pwU, pwAdj, nw⟩ := leaf hwu
    have hset : G.commonNeighbors v w = {u} := by
      ext x
      simp only [mem_commonNeighbors, Set.mem_singleton_iff]
      constructor
      · intro hx
        have hxv : x = u ∨ x = pv := by
          have : x ∈ ({u, pv} : Set V) := nv ▸ hx.1
          simpa using this
        have hxw : x = u ∨ x = pw := by
          have : x ∈ ({u, pw} : Set V) := nw ▸ hx.2
          simpa using this
        rcases hxv with hxU | hxPv
        · exact hxU
        · rcases hxw with hxU | hxPw
          · exact False.elim (pvU (hxPv.symm.trans hxU))
          · have hpeq : pv = pw := hxPv.symm.trans hxPw
            have : v = w :=
              (hwm.2 pv pvU).unique ⟨hvu, G.symm pvAdj⟩ ⟨hwu, G.symm (hpeq ▸ pwAdj)⟩
            exact False.elim (hvw this)
      · rintro rfl
        exact ⟨G.symm (hwm.1 v hvu), G.symm (hwm.1 w hwu)⟩
    exact card_eq_one_of_eq_singleton hset

/-! ## Level B: universal friend ⇒ windmill of triangles -/

lemma commonNeighbors_eq_neighborSet_sdiff_hub (G : SimpleGraph V) {u v : V}
    (hu : ∀ w : V, w ≠ u → G.Adj u w) :
    G.commonNeighbors u v = G.neighborSet v \ {u} := by
  ext x
  simp only [mem_commonNeighbors, Set.mem_diff, Set.mem_singleton_iff, mem_neighborSet]
  constructor
  · intro ⟨hux, hvx⟩
    exact ⟨hvx, (G.ne_of_adj hux).symm⟩
  · intro ⟨hvx, hxu⟩
    exact ⟨hu x hxu, hvx⟩

theorem isWindmillAround_of_universal_friend (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : IsFriendship G) {u : V}
    (hu : G.degree u = Fintype.card V - 1) : IsWindmillAround G u := by
  have huAdj : ∀ w, w ≠ u → G.Adj u w := (degree_eq_card_sub_one_iff G).1 hu
  refine ⟨huAdj, ?_⟩
  intro v hv
  have hcard : Fintype.card (G.commonNeighbors u v) = 1 := hG hv.symm
  have heq : G.commonNeighbors u v = G.neighborSet v \ {u} :=
    commonNeighbors_eq_neighborSet_sdiff_hub G huAdj
  obtain ⟨⟨p, hp⟩, huniq⟩ := Fintype.card_eq_one_iff.mp hcard
  have hp' : p ∈ G.neighborSet v \ {u} := by
    have : p ∈ G.commonNeighbors u v := hp
    rwa [heq] at this
  refine ⟨p, ⟨hp'.2, hp'.1⟩, ?_⟩
  intro w hw
  have hwmem : w ∈ G.commonNeighbors u v := by
    rw [heq]; exact ⟨hw.2, hw.1⟩
  exact Subtype.ext_iff.mp (huniq ⟨w, hwmem⟩)

end ProofLab.Friendship
