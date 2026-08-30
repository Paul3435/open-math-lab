/-
Mycielski 1955: triangle-free finite simple graphs of arbitrarily high χ.

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 has `CliqueFree` / `Colorable` / `chromaticNumber` /
`Walk.three_le_chromaticNumber_of_odd_loop` and ZERO `Mycielski`.

Pin: `catalog/problems/mycielski-triangle-free/STATEMENT.md` (OPE-695).
Triangle-free pin: `CliqueFree 3` (not `CliqueFree 2` — that is edgeless).
Encoding: Mycielski `μ(G)` on `V ⊕ V ⊕ Unit` (Lean `⊕` is right-associative:
first copy `inl`, shadow `inr ∘ inl`, extra vertex `u = inr (inr ())`),
then `SimpleGraph.map` along `Fintype.equivFin` to a labelled `Fin n`.
Zero `sorry`. Do not import `Archive.*`.

This is **not** Brooks (`χ` vs `Δ`). This is **not** greedy `χ ≤ Δ+1`.
This is **not** Grötzsch / Hajós / Kneser / Vizing / 4CT/5CT.
Odd-loop `χ ≥ 3` is glue for Level A, **not** labelled Mycielski.

Level A: the 5-cycle is triangle-free and not 2-colourable (odd closed
walk; reuse `Walk.three_le_chromaticNumber_of_odd_loop`). Gives `k ≤ 2`.
Level B: namesake `mycielski_unbounded` by iterating `μ` from `K₂`.
-/
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.ConcreteColorings
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic

open Finset Function SimpleGraph

noncomputable section
open Classical

namespace ProofLab.Mycielski

variable {V : Type*}

/-! ## Level A: the 5-cycle (not labelled Mycielski) -/

/-- Cycle `C₅` on `Fin 5`. Wrap-around is `Fin` addition (`4 + 1 = 0`). -/
def C5 : SimpleGraph (Fin 5) where
  Adj i j := i + 1 = j ∨ j + 1 = i
  symm := fun _ _ h => Or.symm h
  loopless := by
    intro i h
    have h10 : (1 : Fin 5) ≠ 0 := by decide
    have : i + 1 = i := by
      rcases h with h | h <;> exact h
    exact h10 (add_left_cancel (this.trans (add_zero i).symm))

instance : DecidableRel C5.Adj :=
  fun i j => inferInstanceAs (Decidable (i + 1 = j ∨ j + 1 = i))

lemma c5_adj_succ (i : Fin 5) : C5.Adj i (i + 1) := Or.inl rfl

/-- Closed walk of length 5 around `C₅`. Glue for the odd-loop lemma. -/
def c5_odd_loop : C5.Walk 0 0 :=
  Walk.cons (c5_adj_succ 0)
    (Walk.cons (c5_adj_succ 1)
      (Walk.cons (c5_adj_succ 2)
        (Walk.cons (c5_adj_succ 3)
          (Walk.cons (c5_adj_succ 4) Walk.nil))))

lemma c5_odd_loop_length : c5_odd_loop.length = 5 := rfl

lemma c5_odd_loop_odd : Odd c5_odd_loop.length := by
  rw [c5_odd_loop_length]
  decide

/-- Odd closed walk ⇒ `χ ≥ 3`. Not Mycielski — Mathlib glue. -/
lemma three_le_chromaticNumber_C5 : 3 ≤ C5.chromaticNumber :=
  Walk.three_le_chromaticNumber_of_odd_loop c5_odd_loop c5_odd_loop_odd

/-- Level A: `C₅` is not 2-colourable. -/
theorem c5_not_colorable_two : ¬ C5.Colorable 2 := by
  intro h
  have hle : C5.chromaticNumber ≤ 2 := h.chromaticNumber_le
  have : (3 : ℕ∞) ≤ 2 := le_trans three_le_chromaticNumber_C5 hle
  norm_cast at this

/-- Level A: `C₅` is triangle-free (`CliqueFree 3`, not 2). -/
theorem c5_cliqueFree : C5.CliqueFree 3 := by
  intro t ht
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := is3Clique_iff.mp ht
  -- Exhaust the 5-cycle: neighbours of a vertex are not adjacent.
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp [C5] at hab hac hbc

/-- Level A existence for `k ≤ 2`: `C₅` is a triangle-free non-`k`-colourable graph. -/
theorem mycielski_unbounded_of_le_two (k : ℕ) (hk : k ≤ 2) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
      G.CliqueFree 3 ∧ ¬ G.Colorable k := by
  refine ⟨5, C5, inferInstance, c5_cliqueFree, ?_⟩
  intro hc
  exact c5_not_colorable_two (hc.mono hk)

/-! ## Level B engine: Mycielski construction `μ(G)` on `V ⊕ V ⊕ Unit` -/

/-- Vertex set of `μ(G)`. Lean `⊕` is right-associative, so
`V ⊕ V ⊕ Unit = V ⊕ (V ⊕ Unit)`:
* `Sum.inl v` — first copy of `v`
* `Sum.inr (Sum.inl v)` — shadow of `v`
* `Sum.inr (Sum.inr ())` — extra vertex `u`

The two copies are **not** identified. -/
abbrev MycielskiVertex (V : Type*) := V ⊕ V ⊕ Unit

/-- Adjacency of `μ(G)`:
* keep `G` on the first copy;
* join each shadow `v'` to the neighbours of `v` in the first copy (not to `v`);
* join `u` to every shadow;
* shadows are independent; `u` is not joined to the first copy. -/
def mycielskiAdj (G : SimpleGraph V) : MycielskiVertex V → MycielskiVertex V → Prop
  | .inl v, .inl w => G.Adj v w
  | .inl v, .inr (.inl w) => G.Adj v w
  | .inr (.inl v), .inl w => G.Adj v w
  | .inr (.inl _), .inr (.inl _) => False
  | .inr (.inr _), .inr (.inl _) => True
  | .inr (.inl _), .inr (.inr _) => True
  | .inl _, .inr (.inr _) => False
  | .inr (.inr _), .inl _ => False
  | .inr (.inr _), .inr (.inr _) => False

lemma mycielskiAdj_symm (G : SimpleGraph V) : Symmetric (mycielskiAdj G) := by
  intro x y h
  cases x with
  | inl v =>
    cases y with
    | inl w => exact G.symm h
    | inr y' =>
      cases y' with
      | inl w => exact G.symm h
      | inr _ => exact (False.elim h)
  | inr x' =>
    cases x' with
    | inl v =>
      cases y with
      | inl w => exact G.symm h
      | inr y' =>
        cases y' with
        | inl _ => exact (False.elim h)
        | inr _ => trivial
    | inr _ =>
      cases y with
      | inl _ => exact (False.elim h)
      | inr y' =>
        cases y' with
        | inl _ => trivial
        | inr _ => exact (False.elim h)

lemma mycielskiAdj_irrefl (G : SimpleGraph V) : Irreflexive (mycielskiAdj G) := by
  intro x
  cases x with
  | inl v => exact G.loopless v
  | inr x' =>
    cases x' with
    | inl _ => exact id
    | inr _ => exact id

/-- Mycielski graph `μ(G)` on `V ⊕ V ⊕ Unit`. -/
def mycielski (G : SimpleGraph V) : SimpleGraph (MycielskiVertex V) where
  Adj := mycielskiAdj G
  symm := mycielskiAdj_symm G
  loopless := mycielskiAdj_irrefl G

lemma mycielski_adj_orig {G : SimpleGraph V} {v w : V} :
    (mycielski G).Adj (.inl v) (.inl w) ↔ G.Adj v w :=
  Iff.rfl

lemma mycielski_adj_orig_shadow {G : SimpleGraph V} {v w : V} :
    (mycielski G).Adj (.inl v) (.inr (.inl w)) ↔ G.Adj v w :=
  Iff.rfl

lemma mycielski_adj_shadow_orig {G : SimpleGraph V} {v w : V} :
    (mycielski G).Adj (.inr (.inl v)) (.inl w) ↔ G.Adj v w :=
  Iff.rfl

lemma mycielski_not_adj_shadows {G : SimpleGraph V} {v w : V} :
    ¬ (mycielski G).Adj (.inr (.inl v)) (.inr (.inl w)) :=
  id

lemma mycielski_adj_u_shadow {G : SimpleGraph V} (v : V) :
    (mycielski G).Adj (.inr (.inr ())) (.inr (.inl v)) :=
  trivial

lemma mycielski_not_adj_u_orig {G : SimpleGraph V} {v : V} :
    ¬ (mycielski G).Adj (.inr (.inr ())) (.inl v) :=
  id

/-! ### Triangle-freeness of `μ(G)` -/

lemma mycielski_cliqueFree {G : SimpleGraph V} (hG : G.CliqueFree 3) :
    (mycielski G).CliqueFree 3 := by
  intro s hs
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := is3Clique_iff.mp hs
  have noG : ∀ x y z : V, G.Adj x y → G.Adj x z → G.Adj y z → False := by
    intro x y z hxy hxz hyz
    exact hG _ (is3Clique_triple_iff.2 ⟨hxy, hxz, hyz⟩)
  -- Impossible constructor triples are definitionally `False` adjacency.
  -- The remaining triples project to a triangle in `G`.
  match a, b, c with
  | .inl va, .inl vb, .inl vc => exact noG va vb vc hab hac hbc
  | .inl va, .inl vb, .inr (.inl vc) => exact noG va vb vc hab hac hbc
  | .inl _va, .inl _vb, .inr (.inr _) => exact hac
  | .inl va, .inr (.inl vb), .inl vc => exact noG va vb vc hab hac hbc
  | .inl _va, .inr (.inl _vb), .inr (.inl _vc) => exact hbc
  | .inl _va, .inr (.inl _vb), .inr (.inr _) => exact hac
  | .inl _va, .inr (.inr _), .inl _vc => exact hab
  | .inl _va, .inr (.inr _), .inr (.inl _vc) => exact hab
  | .inl _va, .inr (.inr _), .inr (.inr _) => exact hab
  | .inr (.inl va), .inl vb, .inl vc => exact noG va vb vc hab hac hbc
  | .inr (.inl _va), .inl _vb, .inr (.inl _vc) => exact hac
  | .inr (.inl _va), .inl _vb, .inr (.inr _) => exact hbc
  | .inr (.inl _va), .inr (.inl _vb), .inl _vc => exact hab
  | .inr (.inl _va), .inr (.inl _vb), .inr (.inl _vc) => exact hab
  | .inr (.inl _va), .inr (.inl _vb), .inr (.inr _) => exact hab
  | .inr (.inl _va), .inr (.inr _), .inl _vc => exact hbc
  | .inr (.inl _va), .inr (.inr _), .inr (.inl _vc) => exact hac
  | .inr (.inl _va), .inr (.inr _), .inr (.inr _) => exact hbc
  | .inr (.inr _), .inl _vb, .inl _vc => exact hab
  | .inr (.inr _), .inl _vb, .inr (.inl _vc) => exact hab
  | .inr (.inr _), .inl _vb, .inr (.inr _) => exact hab
  | .inr (.inr _), .inr (.inl _vb), .inl _vc => exact hac
  | .inr (.inr _), .inr (.inl _vb), .inr (.inl _vc) => exact hbc
  | .inr (.inr _), .inr (.inl _vb), .inr (.inr _) => exact hac
  | .inr (.inr _), .inr (.inr _), .inl _vc => exact hab
  | .inr (.inr _), .inr (.inr _), .inr (.inl _vc) => exact hab
  | .inr (.inr _), .inr (.inr _), .inr (.inr _) => exact hab

/-! ### Chromatic bump: ¬ `Colorable k` ⇒ μ not `Colorable (k+1)` -/

/-- Recolour a first-copy vertex: if it used `u`'s colour, take the shadow's colour. -/
def recolor {G : SimpleGraph V} {k : ℕ} (c : (mycielski G).Coloring (Fin (k + 1)))
    (v : V) : Fin (k + 1) :=
  if c (.inl v) = c (.inr (.inr ())) then c (.inr (.inl v)) else c (.inl v)

lemma recolor_ne_u {G : SimpleGraph V} {k : ℕ}
    (c : (mycielski G).Coloring (Fin (k + 1))) (v : V) :
    recolor c v ≠ c (.inr (.inr ())) := by
  dsimp [recolor]
  split_ifs with h
  · exact (c.valid (mycielski_adj_u_shadow v)).symm
  · exact h

lemma recolor_valid {G : SimpleGraph V} {k : ℕ}
    (c : (mycielski G).Coloring (Fin (k + 1))) {v w : V} (hvw : G.Adj v w) :
    recolor c v ≠ recolor c w := by
  dsimp [recolor]
  have h_orig : c (.inl v) ≠ c (.inl w) := c.valid (mycielski_adj_orig.mpr hvw)
  have h_v_sw : c (.inl v) ≠ c (.inr (.inl w)) :=
    c.valid (mycielski_adj_orig_shadow.mpr hvw)
  have h_w_sv : c (.inl w) ≠ c (.inr (.inl v)) :=
    c.valid (mycielski_adj_orig_shadow.mpr (Adj.symm hvw))
  split_ifs with hv hw
  · exact (h_orig (hv.trans hw.symm)).elim
  · exact h_w_sv.symm
  · exact h_v_sw
  · exact h_orig

/-- Compress colours in `Fin (k+1)` that avoid `cu` down to `ℕ < k`. -/
def compress (k : ℕ) (cu col : Fin (k + 1)) : ℕ :=
  if col.val < cu.val then col.val else col.val - 1

lemma compress_lt {k : ℕ} {cu col : Fin (k + 1)} (hne : col ≠ cu) :
    compress k cu col < k := by
  unfold compress
  have hval : col.val ≠ cu.val := fun h => hne (Fin.ext h)
  have hcol : col.val ≤ k := Nat.le_of_lt_succ col.isLt
  split_ifs with hlt
  · omega
  · have : cu.val ≤ col.val := Nat.le_of_not_lt hlt
    have : cu.val < col.val := lt_of_le_of_ne this hval.symm
    omega

lemma compress_inj {k : ℕ} {cu a b : Fin (k + 1)} (ha : a ≠ cu) (hb : b ≠ cu)
    (h : compress k cu a = compress k cu b) : a = b := by
  unfold compress at h
  have haval : a.val ≠ cu.val := fun h' => ha (Fin.ext h')
  have hbval : b.val ≠ cu.val := fun h' => hb (Fin.ext h')
  split_ifs at h with h1 h2 h2
  · exact Fin.ext h
  · have : a.val < cu.val := h1
    have : ¬ b.val < cu.val := h2
    omega
  · have : ¬ a.val < cu.val := h1
    have : b.val < cu.val := h2
    omega
  · have : a.val - 1 = b.val - 1 := h
    have ha' : ¬ a.val < cu.val := h1
    have hb' : ¬ b.val < cu.val := h2
    have : cu.val ≤ a.val := Nat.le_of_not_lt ha'
    have : cu.val ≤ b.val := Nat.le_of_not_lt hb'
    have ha1 : 1 ≤ a.val := by omega
    have hb1 : 1 ≤ b.val := by omega
    exact Fin.ext (by omega)

lemma not_colorable_zero_of_nonempty [Nonempty V] (G : SimpleGraph V) :
    ¬ G.Colorable 0 := by
  intro h
  exact (not_isEmpty_of_nonempty V) (isEmpty_of_colorable_zero G h)

/-- Named fact: if `G` is not `k`-colourable then `μ(G)` is not `(k+1)`-colourable. -/
theorem mycielski_not_colorable_succ {G : SimpleGraph V} {k : ℕ}
    (hG : ¬ G.Colorable k) : ¬ (mycielski G).Colorable (k + 1) := by
  intro hc
  obtain ⟨c⟩ := hc
  cases k with
  | zero =>
    -- A 1-colouring of `μ(G)`: `u` uses the only colour, so no shadows, so `V` empty.
    by_cases hV : IsEmpty V
    · exact hG (colorable_of_isEmpty G 0)
    · haveI : Nonempty V := not_isEmpty_iff.mp hV
      obtain ⟨v⟩ := ‹Nonempty V›
      have : Subsingleton (Fin 1) := inferInstance
      exact c.valid (mycielski_adj_u_shadow v) (Subsingleton.elim _ _)
  | succ m =>
    let cu := c (.inr (.inr ()))
    let color : V → ℕ := fun v => compress (m + 1) cu (recolor c v)
    have hbound : ∀ v, color v < m + 1 := fun v =>
      compress_lt (recolor_ne_u c v)
    have hvalid : ∀ {v w : V}, G.Adj v w → color v ≠ color w := by
      intro v w hvw hcol
      have : recolor c v = recolor c w :=
        compress_inj (recolor_ne_u c v) (recolor_ne_u c w) hcol
      exact recolor_valid c hvw this
    have : G.Colorable (m + 1) :=
      (colorable_iff_exists_bdd_nat_coloring (m + 1)).mpr
        ⟨Coloring.mk color hvalid, hbound⟩
    exact hG this

/-! ### Transport `μ(G)` onto a labelled `Fin n` -/

lemma card_mycielskiVertex [Fintype V] :
    Fintype.card (MycielskiVertex V) = 2 * Fintype.card V + 1 := by
  simp [MycielskiVertex, Fintype.card_sum, Fintype.card_unit]
  ring

def packMycielski [Fintype V] :
    MycielskiVertex V ≃ Fin (2 * Fintype.card V + 1) :=
  (Fintype.equivFin _).trans (finCongr card_mycielskiVertex)

/-- Labelled `Fin` copy of `μ(G)`. Isomorphic to `V ⊕ V ⊕ Unit`; copies stay distinct. -/
def mycielskiOnFin [Fintype V] (G : SimpleGraph V) :
    SimpleGraph (Fin (2 * Fintype.card V + 1)) :=
  (mycielski G).map (packMycielski (V := V)).toEmbedding

instance [Fintype V] (G : SimpleGraph V) : DecidableRel (mycielskiOnFin G).Adj :=
  Classical.decRel _

lemma mycielskiOnFin_cliqueFree [Fintype V] {G : SimpleGraph V} (hG : G.CliqueFree 3) :
    (mycielskiOnFin G).CliqueFree 3 := by
  haveI : Nonempty (MycielskiVertex V) := ⟨.inr (.inr ())⟩
  exact (cliqueFree_map_iff (f := (packMycielski (V := V)).toEmbedding)).mpr
    (mycielski_cliqueFree hG)

lemma mycielskiOnFin_not_colorable_succ [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (hG : ¬ G.Colorable k) : ¬ (mycielskiOnFin G).Colorable (k + 1) := by
  intro hc
  have hembed : mycielski G ↪g mycielskiOnFin G :=
    SimpleGraph.Embedding.map (packMycielski (V := V)).toEmbedding (mycielski G)
  exact mycielski_not_colorable_succ hG (Colorable.of_embedding hembed hc)

lemma mycielski_step [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (hcf : G.CliqueFree 3) (hnc : ¬ G.Colorable k) :
    ∃ (n : ℕ) (G' : SimpleGraph (Fin n)) (_ : DecidableRel G'.Adj),
      G'.CliqueFree 3 ∧ ¬ G'.Colorable (k + 1) :=
  ⟨2 * Fintype.card V + 1, mycielskiOnFin G, inferInstance,
    mycielskiOnFin_cliqueFree hcf, mycielskiOnFin_not_colorable_succ hnc⟩

/-! ### Base: `K₂` is triangle-free and not 0- or 1-colourable -/

lemma k2_cliqueFree : (⊤ : SimpleGraph (Fin 2)).CliqueFree 3 :=
  cliqueFree_of_card_lt (by decide : Fintype.card (Fin 2) < 3)

lemma k2_not_colorable_zero : ¬ (⊤ : SimpleGraph (Fin 2)).Colorable 0 :=
  not_colorable_zero_of_nonempty _

lemma k2_not_colorable_one : ¬ (⊤ : SimpleGraph (Fin 2)).Colorable 1 := by
  intro h
  obtain ⟨c⟩ := h
  have hadj : (⊤ : SimpleGraph (Fin 2)).Adj 0 1 := by decide
  exact c.valid hadj (Subsingleton.elim _ _)

/-! ## Level B namesake: unbounded χ among triangle-free finite graphs -/

/-- Mycielski 1955: for every `k` there is a finite triangle-free simple graph
that is not `k`-colourable. Construction: iterate `μ` from `K₂` (and `k = 0`
uses `K₂` itself). **No novelty claim.** -/
theorem mycielski_unbounded (k : ℕ) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
      G.CliqueFree 3 ∧ ¬ G.Colorable k := by
  induction k with
  | zero =>
    exact ⟨2, ⊤, inferInstance, k2_cliqueFree, k2_not_colorable_zero⟩
  | succ k ih =>
    obtain ⟨n, G, _, hcf, hnc⟩ := ih
    exact mycielski_step (V := Fin n) hcf hnc

end ProofLab.Mycielski
