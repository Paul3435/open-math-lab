/-
Menger (1927), vertex form, finite simple graphs: min |A–B vertex
separator| = max number of pairwise vertex-disjoint A–B paths.

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 has `Walk` / `Walk.support` / `IsPath` / `Reachable`
and ZERO `Menger` / graph `IsSeparator` / `vertexCut` / `IsABPath`
(category-theory `IsDetector.isSeparator` is unrelated).

Pin: `catalog/problems/menger-vertex/STATEMENT.md` (OPE-678).
Encoding: Mathlib `Walk` / `IsPath` / `Walk.support`. ProofLab
`IsABPath` / `IsABSeparator`. Global A–B form (Diestel 3.3.1 flavour):
fully vertex-disjoint, including ends. Zero `sorry`. Do not import
`Archive.*`.

This is **not** König `ν=τ`, **not** edge-Menger, **not** max-flow,
**not** infinite Erdős–Menger, **not** Tutte, **not** Whitney,
**not** Dilworth / greedy / Brooks / Eulerian / Dirac / Havel–Hakimi.

Level A: `A ∩ B` trivial paths; singleton `A`,`B` joined by an edge;
no A–B path ⇒ `p = s = 0`; easy `p ≤ s`; `|E|=0` / `⊥` base.
Zero sorry.
Level B residual (not sorry-ed): namesake `menger_vertex` by Diestel
induction on `card G.edgeFinset` (critical-edge / separator-split +
glue). Walk-induction is the named budget sink. Cap two levels.
No edge-Menger / no flows / no infinite.
-/
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

open Finset Function SimpleGraph

noncomputable section
open Classical

namespace ProofLab.Menger

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

/-! ## Pinned definitions (Diestel global A–B form) -/

/-- Diestel A–B path: first vertex in `A`, last in `B`, no *internal*
vertex in `A ∪ B`. Trivial `Walk.nil` at `x ∈ A ∩ B` is allowed. -/
structure IsABPath (G : SimpleGraph V) (A B : Set V) {u v : V}
    (p : G.Walk u v) : Prop where
  isPath : p.IsPath
  start_mem : u ∈ A
  end_mem : v ∈ B
  internals : ∀ x ∈ p.support, x ≠ u → x ≠ v → x ∉ A ∪ B

/-- `S` separates `A` from `B` when every A–B path meets `S`.
In particular `A ∩ B ⊆ S` for every separator. -/
def IsABSeparator (G : SimpleGraph V) (A B : Set V) (S : Finset V) : Prop :=
  ∀ ⦃u v : V⦄ (p : G.Walk u v), IsABPath G A B p → ∃ x ∈ S, x ∈ p.support

/-- A packing of `n` pairwise vertex-disjoint A–B paths (including ends). -/
def HasPack (G : SimpleGraph V) (A B : Set V) (n : ℕ) : Prop :=
  ∃ (src tgt : Fin n → V) (w : ∀ i, G.Walk (src i) (tgt i)),
    (∀ i, IsABPath G A B (w i)) ∧
      ∀ i j, i ≠ j → ∀ x, x ∈ (w i).support → x ∉ (w j).support

def packingSizes (G : SimpleGraph V) (A B : Set V) : Set ℕ :=
  { n | HasPack G A B n }

def separatorSizes (G : SimpleGraph V) (A B : Set V) : Set ℕ :=
  { n | ∃ S : Finset V, IsABSeparator G A B S ∧ S.card = n }

/-- Max number of pairwise vertex-disjoint A–B paths. -/
def p (G : SimpleGraph V) (A B : Set V) : ℕ := sSup (packingSizes G A B)

/-- Min cardinality of an A–B vertex separator. -/
def s (G : SimpleGraph V) (A B : Set V) : ℕ := sInf (separatorSizes G A B)

/-! ## Basic constructors -/

lemma isABPath_nil {A B : Set V} {x : V} (hxA : x ∈ A) (hxB : x ∈ B) :
    IsABPath G A B (Walk.nil : G.Walk x x) where
  isPath := Walk.IsPath.nil
  start_mem := hxA
  end_mem := hxB
  internals := by
    intro y hy hyx _
    simp [Walk.support_nil] at hy
    exact (hyx hy).elim

lemma isABPath_adj {A B : Set V} {a b : V} (ha : a ∈ A) (hb : b ∈ B)
    (h : G.Adj a b) : IsABPath G A B h.toWalk where
  isPath := by
    rw [Adj.toWalk, Walk.cons_isPath_iff]
    exact ⟨Walk.IsPath.nil, by simp [h.ne]⟩
  start_mem := ha
  end_mem := hb
  internals := by
    intro x hx hxa hxb
    simp [Adj.toWalk, Walk.support_cons, Walk.support_nil] at hx
    rcases hx with rfl | rfl
    · exact (hxa rfl).elim
    · exact (hxb rfl).elim

lemma hasPack_zero (G : SimpleGraph V) (A B : Set V) : HasPack G A B 0 := by
  refine ⟨isEmptyElim, ⟨isEmptyElim, ⟨isEmptyElim, ⟨?_, ?_⟩⟩⟩⟩
  · intro i; exact isEmptyElim i
  · intro i; exact isEmptyElim i

lemma packingSizes_nonempty (G : SimpleGraph V) (A B : Set V) :
    (packingSizes G A B).Nonempty :=
  ⟨0, hasPack_zero G A B⟩

lemma univ_isABSeparator (G : SimpleGraph V) (A B : Set V) :
    IsABSeparator G A B univ := by
  intro _ _ p _
  exact ⟨_, mem_univ _, Walk.start_mem_support p⟩

lemma separatorSizes_nonempty (G : SimpleGraph V) (A B : Set V) :
    (separatorSizes G A B).Nonempty :=
  ⟨univ.card, univ, univ_isABSeparator G A B, rfl⟩

lemma A_isABSeparator (G : SimpleGraph V) (A B : Set V) :
    IsABSeparator G A B A.toFinset := by
  intro u _ p hp
  exact ⟨u, Set.mem_toFinset.mpr hp.start_mem, Walk.start_mem_support p⟩

lemma B_isABSeparator (G : SimpleGraph V) (A B : Set V) :
    IsABSeparator G A B B.toFinset := by
  intro _ v p hp
  exact ⟨v, Set.mem_toFinset.mpr hp.end_mem, Walk.end_mem_support p⟩

/-! ## Easy inequality `p ≤ s` -/

lemma hasPack_le_card {n : ℕ} (h : HasPack G A B n) : n ≤ Fintype.card V := by
  obtain ⟨src, _, w, _, hdisj⟩ := h
  have hinj : Injective src := by
    intro i j hij
    by_contra hne
    have hj : src i ∈ (w j).support := by
      rw [hij]; exact Walk.start_mem_support (w j)
    exact hdisj i j hne (src i) (Walk.start_mem_support (w i)) hj
  simpa using Fintype.card_le_of_injective src hinj

lemma bddAbove_packingSizes (G : SimpleGraph V) (A B : Set V) :
    BddAbove (packingSizes G A B) :=
  ⟨Fintype.card V, fun _ hn => hasPack_le_card hn⟩

lemma pack_le_sep {n : ℕ} {S : Finset V} (hP : HasPack G A B n)
    (hS : IsABSeparator G A B S) : n ≤ S.card := by
  obtain ⟨_, _, w, hab, hdisj⟩ := hP
  let y : Fin n → V := fun i => Classical.choose (hS (w i) (hab i))
  have hy : ∀ i, y i ∈ S ∧ y i ∈ (w i).support := fun i =>
    Classical.choose_spec (hS (w i) (hab i))
  have hinj : Injective y := by
    intro i j hij
    by_contra hne
    have hj : y i ∈ (w j).support := by
      rw [hij]; exact (hy j).2
    exact hdisj i j hne (y i) (hy i).2 hj
  have himg : univ.image y ⊆ S := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := mem_image.mp hx
    exact (hy i).1
  have hcard : (univ.image y).card = n := by
    rw [card_image_of_injective _ hinj, card_univ, Fintype.card_fin]
  rw [← hcard]
  exact card_le_card himg

lemma le_packingNumber {n : ℕ} (h : HasPack G A B n) : n ≤ p G A B :=
  le_csSup (bddAbove_packingSizes G A B) h

lemma separatorNumber_le {S : Finset V} (h : IsABSeparator G A B S) :
    s G A B ≤ S.card :=
  csInf_le (OrderBot.bddBelow _) ⟨S, h, rfl⟩

/-- Easy direction: a separator meets every path, and disjoint paths
meet it in distinct vertices. -/
theorem packingNumber_le_separatorNumber (G : SimpleGraph V) (A B : Set V) :
    p G A B ≤ s G A B := by
  apply csSup_le (packingSizes_nonempty G A B)
  intro n hn
  apply le_csInf (separatorSizes_nonempty G A B)
  intro m hm
  obtain ⟨S, hS, rfl⟩ := hm
  exact pack_le_sep hn hS

/-! ## Level A: `A ∩ B` trivial paths (load-bearing) -/

lemma inter_subset_separator {A B : Set V} {S : Finset V}
    (hS : IsABSeparator G A B S) : (A ∩ B).toFinset ⊆ S := by
  intro x hx
  have hxAB : x ∈ A ∩ B := Set.mem_toFinset.mp hx
  obtain ⟨y, hyS, hy⟩ := hS Walk.nil (isABPath_nil hxAB.1 hxAB.2)
  simp [Walk.support_nil] at hy
  rwa [← hy]

lemma hasPack_inter (G : SimpleGraph V) (A B : Set V) :
    HasPack G A B (A ∩ B).toFinset.card := by
  let I := (A ∩ B).toFinset
  let e : Fin I.card ≃ I := I.equivFin.symm
  refine ⟨fun i => (e i).1, fun i => (e i).1, fun i => Walk.nil, ?_, ?_⟩
  · intro i
    have hAB : (e i).1 ∈ A ∩ B := Set.mem_toFinset.mp (e i).2
    exact isABPath_nil hAB.1 hAB.2
  · intro i j hij x hxi hxj
    have hi : x = (e i).1 := List.mem_singleton.mp (by simpa using hxi)
    have hj : x = (e j).1 := List.mem_singleton.mp (by simpa using hxj)
    exact hij (e.injective (Subtype.ext (hi.symm.trans hj)))

theorem packingNumber_ge_inter (G : SimpleGraph V) (A B : Set V) :
    (A ∩ B).toFinset.card ≤ p G A B :=
  le_packingNumber (hasPack_inter G A B)

theorem separatorNumber_ge_inter (G : SimpleGraph V) (A B : Set V) :
    (A ∩ B).toFinset.card ≤ s G A B := by
  apply le_csInf (separatorSizes_nonempty G A B)
  intro m hm
  obtain ⟨S, hS, rfl⟩ := hm
  exact card_le_card (inter_subset_separator hS)

/-- Nonempty intersection gives at least one trivial A–B path and sits
inside every separator. -/
theorem inter_nonempty_bounds {A B : Set V} (h : (A ∩ B).Nonempty) :
    1 ≤ p G A B ∧ 1 ≤ s G A B := by
  obtain ⟨x, hx⟩ := h
  have hpos : 1 ≤ (A ∩ B).toFinset.card := by
    have : (A ∩ B).toFinset.Nonempty := ⟨x, Set.mem_toFinset.mpr hx⟩
    exact Nat.succ_le_of_lt (card_pos.mpr this)
  exact ⟨hpos.trans (packingNumber_ge_inter G A B),
    hpos.trans (separatorNumber_ge_inter G A B)⟩

/-! ## Level A: no A–B path ⇒ `p = s = 0` -/

lemma not_hasPack_of_no_path {A B : Set V}
    (h : ∀ ⦃u v : V⦄ (p : G.Walk u v), ¬ IsABPath G A B p) {n : ℕ}
    (hn : 0 < n) : ¬ HasPack G A B n := by
  intro hP
  obtain ⟨_, _, w, hab, _⟩ := hP
  exact h (w ⟨0, hn⟩) (hab _)

lemma empty_isABSeparator_of_no_path {A B : Set V}
    (h : ∀ ⦃u v : V⦄ (p : G.Walk u v), ¬ IsABPath G A B p) :
    IsABSeparator G A B ∅ := by
  intro _ _ p hp
  exact (h p hp).elim

lemma inter_eq_empty_of_no_path {A B : Set V}
    (h : ∀ ⦃u v : V⦄ (p : G.Walk u v), ¬ IsABPath G A B p) :
    A ∩ B = ∅ := by
  ext x
  constructor
  · intro hx
    exact (h Walk.nil (isABPath_nil hx.1 hx.2)).elim
  · intro hx
    exact hx.elim

/-- Empty packing and empty separator. `A ∩ B = ∅` follows from the
no-path hypothesis (load-bearing in the pin). -/
theorem menger_vertex_no_path {A B : Set V}
    (h : ∀ ⦃u v : V⦄ (p : G.Walk u v), ¬ IsABPath G A B p)
    (hAB : A ∩ B = ∅) : s G A B = 0 ∧ p G A B = 0 := by
  let _ := hAB
  have hs : s G A B ≤ 0 :=
    separatorNumber_le (empty_isABSeparator_of_no_path h)
  have hp0 : p G A B = 0 := by
    have hset : packingSizes G A B = {0} := by
      ext n
      simp only [packingSizes, Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · intro hn
        by_contra hne
        exact not_hasPack_of_no_path h (Nat.pos_of_ne_zero hne) hn
      · intro hn
        rw [hn]
        exact hasPack_zero G A B
    simp [p, hset]
  exact ⟨Nat.eq_zero_of_le_zero hs, hp0⟩

/-! ## Level A: singleton `A`,`B` joined by an edge -/

lemma hasPack_adj {A B : Set V} {a b : V} (ha : a ∈ A) (hb : b ∈ B)
    (h : G.Adj a b) : HasPack G A B 1 := by
  refine ⟨fun _ => a, fun _ => b, fun _ => h.toWalk,
    fun _ => isABPath_adj ha hb h, ?_⟩
  intro i j hij
  exact (hij (Subsingleton.elim i j)).elim

lemma singleton_src_isABSeparator {A B : Set V} {a : V} (hA : A = {a}) :
    IsABSeparator G A B {a} := by
  intro u _ p hp
  have : u = a := by
    have hu := hp.start_mem
    simp [hA] at hu
    exact hu
  exact ⟨a, mem_singleton_self a, this ▸ Walk.start_mem_support p⟩

/-- Global form: paths share the unique ends, so `p = s = 1`. -/
theorem menger_vertex_singletons_adj {A B : Set V} {a b : V}
    (hA : A = {a}) (hB : B = {b}) (h : G.Adj a b) :
    s G A B = 1 ∧ p G A B = 1 := by
  have ha : a ∈ A := by simp [hA]
  have hb : b ∈ B := by simp [hB]
  have hpack : HasPack G A B 1 := hasPack_adj ha hb h
  have hsep : IsABSeparator G A B {a} := singleton_src_isABSeparator hA
  have hp1 : 1 ≤ p G A B := le_packingNumber hpack
  have hs1 : s G A B ≤ 1 := (separatorNumber_le hsep).trans_eq (card_singleton a)
  have hps : p G A B ≤ s G A B := packingNumber_le_separatorNumber G A B
  exact ⟨le_antisymm hs1 (hp1.trans hps), le_antisymm (hps.trans hs1) hp1⟩

/-! ## Level A / Diestel base: no edges ⇒ `p = s = |A ∩ B|` -/

lemma inter_isABSeparator_bot (A B : Set V) :
    IsABSeparator (⊥ : SimpleGraph V) A B (A ∩ B).toFinset := by
  intro u v p hp
  cases p with
  | cons h _ => exact ((bot_adj _ _).mp h).elim
  | nil =>
      exact ⟨u, Set.mem_toFinset.mpr ⟨hp.start_mem, hp.end_mem⟩,
        Walk.start_mem_support _⟩

/-- Diestel `|E| = 0` base of the named Level B induction. -/
theorem menger_bot (A B : Set V) :
    s (⊥ : SimpleGraph V) A B = (A ∩ B).toFinset.card ∧
      p (⊥ : SimpleGraph V) A B = (A ∩ B).toFinset.card := by
  let I := (A ∩ B).toFinset
  have hpack : HasPack (⊥ : SimpleGraph V) A B I.card := hasPack_inter _ A B
  have hsep : IsABSeparator (⊥ : SimpleGraph V) A B I :=
    inter_isABSeparator_bot A B
  have hple : p (⊥ : SimpleGraph V) A B ≤ s (⊥ : SimpleGraph V) A B :=
    packingNumber_le_separatorNumber _ A B
  have hpge : I.card ≤ p (⊥ : SimpleGraph V) A B := le_packingNumber hpack
  have hsle : s (⊥ : SimpleGraph V) A B ≤ I.card := separatorNumber_le hsep
  exact ⟨le_antisymm hsle (hpge.trans hple), le_antisymm (hple.trans hsle) hpge⟩

/-!
## Level B residual (not sorry-ed)

Named engine this heartbeat: Diestel induction on `card G.edgeFinset`.
Base `|E| = 0` is `menger_bot`. Inductive step: if some edge is
non-critical (`s(G-e,A,B) = s(G,A,B)`), delete and apply IH; if every
edge is critical, a minimum separator `S ∉ {A, B}` splits `G` along
`S` and the two sides glue to `s` disjoint A–B paths (walk-concatenation
budget sink). Optional König reduction on a split graph is the other
named engine — not attacked, not a König leftover.

`theorem menger_vertex (A B : Set V) : s G A B = p G A B` is **not**
stated with `sorry`. Cap two levels. No edge-Menger / no flows /
no infinite Erdős–Menger. Default **no claim**.
-/

end ProofLab.Menger
