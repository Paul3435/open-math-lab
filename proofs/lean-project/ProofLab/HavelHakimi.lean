/-
Havel–Hakimi (Havel 1955 / Hakimi 1962): a nonincreasing sequence of
nonnegative integers is graphic iff the Havel–Hakimi reduction is graphic.

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 has `SimpleGraph.degree` / `neighborFinset` / handshaking
(`sum_degrees_eq_twice_card_edges`) but ZERO `IsGraphic` / `Havel` / `Hakimi`
/ `degreeSequence` under Mathlib+Archive.

Pin: `catalog/problems/havel-hakimi/STATEMENT.md` (OPE-671).
Encoding: labelled `SimpleGraph (Fin n)` with `DecidableRel G.Adj`.
Existence only — not isomorphism classes. Zero `sorry`.
Do not import `Archive.*`.

This is **not** Erdős–Gállai, **not** Gale–Ryser, **not** Tutte,
**not** greedy / Brooks / König / Dirac / Eulerian / Dilworth.

`reduce` is defined only on `ReduceOK` sequences. Failed reduction
(`d 0 ≥ n`, or a decrement would go negative) is `¬ IsGraphic d` on the
left and is not passed to `IsGraphic` on the right — matching the pin.

Level A: empty / all-zeros (`⊥`) / complete (`⊤`) / `K₂ = (1,1)` /
non-graphic `(1)` and `(2,2,0,0)` + `d i < n` glue. Zero sorry.
Level B (honest partial this heartbeat): constructive reverse
`isGraphic_of_reduce` + failed reduction `not_graphic_of_not_reduceOK`
+ permutation invariance `isGraphic_sortNoninc`. **Namesake residual:**
forward `IsGraphic d → IsGraphic (reduce d h)` needs Havel switching
(realise so vertex `0` is adjacent to the next `d 0` vertices) then
delete; not sorry-ed. Cap two levels. No Erdős–Gállai / Gale–Ryser / Tutte.
-/
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.Sort
import Mathlib.Tactic

open Function SimpleGraph
open scoped Classical

noncomputable section

namespace ProofLab.HavelHakimi

/-! ## Pinned definitions -/

/-- Nonincreasing pin (STATEMENT.md). -/
def IsNoninc {n : ℕ} (d : Fin n → ℕ) : Prop :=
  ∀ ⦃i j : Fin n⦄, i ≤ j → d j ≤ d i

/-- Labelled realisation: some simple graph on `Fin n` has degrees `d`. -/
def IsGraphic {n : ℕ} (d : Fin n → ℕ) : Prop :=
  ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
    ∀ i, G.degree i = d i

/-- Unsorted Havel–Hakimi step: drop index `0`, subtract `1` from the next
`d 0` entries. `Nat.sub` floors at 0; `ReduceOK` rules out a genuine
negative. -/
def reduceUnsorted {n : ℕ} (d : Fin (n + 1) → ℕ) : Fin n → ℕ :=
  fun i => if i.val < d 0 then d i.succ - 1 else d i.succ

/-- Reduction succeeds: empty sequence, or `d 0 ≤ n` (i.e. `d 0 < n+1`)
and every decremented entry is positive. -/
def ReduceOK {n : ℕ} (d : Fin n → ℕ) : Prop :=
  match n with
  | 0 => True
  | n + 1 => d 0 ≤ n ∧ ∀ i : Fin n, i.val < d 0 → 0 < d i.succ

/-! ## Re-sort (load-bearing) -/

def tagged {n : ℕ} (d : Fin n → ℕ) : List (ℕ × Fin n) :=
  List.ofFn fun i => (d i, i)

def geFst {n : ℕ} : ℕ × Fin n → ℕ × Fin n → Prop :=
  fun a b => b.1 ≤ a.1

instance geFst.decidable {n : ℕ} : DecidableRel (@geFst n) :=
  fun a b => inferInstanceAs (Decidable (b.1 ≤ a.1))

instance geFst.isTotal {n : ℕ} : IsTotal (ℕ × Fin n) geFst :=
  ⟨fun a b => le_total b.1 a.1⟩

instance geFst.isTrans {n : ℕ} : IsTrans (ℕ × Fin n) geFst :=
  ⟨fun _ _ _ hab hbc => le_trans hbc hab⟩

instance geFst.isRefl {n : ℕ} : IsRefl (ℕ × Fin n) geFst :=
  ⟨fun _ => le_rfl⟩

def sortedTagged {n : ℕ} (d : Fin n → ℕ) : List (ℕ × Fin n) :=
  (tagged d).insertionSort geFst

lemma length_sortedTagged {n : ℕ} (d : Fin n → ℕ) :
    (sortedTagged d).length = n := by
  simpa [sortedTagged, tagged, List.length_ofFn]
    using (List.perm_insertionSort (@geFst n) (tagged d)).length_eq

lemma get_lt_sortedTagged {n : ℕ} (d : Fin n → ℕ) (i : Fin n) :
    i.val < (sortedTagged d).length := by
  rw [length_sortedTagged]; exact i.isLt

/-- Nonincreasing rearrangement of `d`. -/
def sortNoninc {n : ℕ} (d : Fin n → ℕ) : Fin n → ℕ :=
  fun i => ((sortedTagged d).get ⟨i.val, get_lt_sortedTagged d i⟩).1

def sortIndex {n : ℕ} (d : Fin n → ℕ) : Fin n → Fin n :=
  fun i => ((sortedTagged d).get ⟨i.val, get_lt_sortedTagged d i⟩).2

lemma mem_sortedTagged {n : ℕ} {d : Fin n → ℕ} {p : ℕ × Fin n} :
    p ∈ sortedTagged d ↔ p ∈ tagged d :=
  (List.perm_insertionSort geFst (tagged d)).mem_iff

lemma tagged_eq {n : ℕ} {d : Fin n → ℕ} {p : ℕ × Fin n} (hp : p ∈ tagged d) :
    p.1 = d p.2 := by
  rw [tagged, List.mem_ofFn] at hp
  obtain ⟨i, rfl⟩ := hp
  rfl

lemma get_mem_sortedTagged {n : ℕ} (d : Fin n → ℕ) (i : Fin n) :
    (sortedTagged d).get ⟨i.val, get_lt_sortedTagged d i⟩ ∈ sortedTagged d :=
  List.get_mem _ i.val _

lemma sortNoninc_eq_comp {n : ℕ} (d : Fin n → ℕ) (i : Fin n) :
    sortNoninc d i = d (sortIndex d i) :=
  tagged_eq (mem_sortedTagged.mp (get_mem_sortedTagged d i))

/-! ## Level A specials -/

lemma isGraphic_empty (d : Fin 0 → ℕ) : IsGraphic d :=
  ⟨⊥, inferInstance, fun i => isEmptyElim i⟩

lemma isGraphic_zeros (n : ℕ) : IsGraphic (fun _ : Fin n => 0) :=
  ⟨⊥, inferInstance, fun i => bot_degree i⟩

lemma isGraphic_complete (n : ℕ) : IsGraphic (fun _ : Fin n => n - 1) :=
  ⟨⊤, inferInstance, fun i => by rw [complete_graph_degree, Fintype.card_fin]⟩

lemma isGraphic_k2 : IsGraphic (fun _ : Fin 2 => 1) :=
  ⟨⊤, inferInstance, fun i => by rw [complete_graph_degree, Fintype.card_fin]⟩

lemma graphic_even_sum {n : ℕ} {d : Fin n → ℕ} (h : IsGraphic d) :
    Even (∑ i : Fin n, d i) := by
  obtain ⟨G, inst, hdeg⟩ := h
  letI := inst
  have hs := G.sum_degrees_eq_twice_card_edges
  simp_rw [hdeg] at hs
  have : Even (2 * G.edgeFinset.card) := even_two_mul _
  rwa [← hs] at this

lemma graphic_degree_lt {n : ℕ} {d : Fin n → ℕ} (h : IsGraphic d) (i : Fin n) :
    d i < n := by
  obtain ⟨G, inst, hdeg⟩ := h
  letI := inst
  have := G.degree_lt_card_verts i
  rw [hdeg, Fintype.card_fin] at this
  exact this

lemma not_graphic_of_degree_ge {n : ℕ} {d : Fin n → ℕ} {i : Fin n}
    (h : n ≤ d i) : ¬ IsGraphic d :=
  fun hg => (Nat.not_le_of_gt (graphic_degree_lt hg i)) h

lemma not_graphic_one : ¬ IsGraphic (fun _ : Fin 1 => 1) :=
  not_graphic_of_degree_ge (i := (0 : Fin 1)) (by decide)

def seq2200 : Fin 4 → ℕ := fun i => if i.val < 2 then 2 else 0

lemma seq2200_even : Even (∑ i : Fin 4, seq2200 i) := by
  unfold seq2200
  decide

lemma not_graphic_2200 : ¬ IsGraphic seq2200 := by
  intro ⟨G, inst, hdeg⟩
  letI := inst
  have h0 : G.degree 0 = 2 := by simpa [seq2200] using hdeg 0
  have n2 : ¬ G.Adj 0 (2 : Fin 4) := by
    intro h
    have : 0 < G.degree (2 : Fin 4) := (degree_pos_iff_exists_adj _ _).2 ⟨0, h.symm⟩
    have : G.degree (2 : Fin 4) = 0 := by simpa [seq2200] using hdeg (2 : Fin 4)
    omega
  have n3 : ¬ G.Adj 0 (3 : Fin 4) := by
    intro h
    have : 0 < G.degree (3 : Fin 4) := (degree_pos_iff_exists_adj _ _).2 ⟨0, h.symm⟩
    have : G.degree (3 : Fin 4) = 0 := by simpa [seq2200] using hdeg (3 : Fin 4)
    omega
  have sub : G.neighborFinset 0 ⊆ ({1} : Finset (Fin 4)) := by
    intro x hx
    have hadj : G.Adj 0 x := (mem_neighborFinset _ _ _).1 hx
    fin_cases x
    · exact (G.loopless _ hadj).elim
    · exact Finset.mem_singleton_self _
    · exact (n2 hadj).elim
    · exact (n3 hadj).elim
  have : G.degree 0 ≤ 1 := (Finset.card_le_card sub).trans (by simp)
  omega

lemma isNoninc_zeros (n : ℕ) : IsNoninc (fun _ : Fin n => 0) :=
  fun _ _ _ => le_rfl

lemma isNoninc_complete (n : ℕ) : IsNoninc (fun _ : Fin n => n - 1) :=
  fun _ _ _ => le_rfl

lemma isNoninc_k2 : IsNoninc (fun _ : Fin 2 => 1) :=
  fun _ _ _ => le_rfl

lemma isNoninc_one : IsNoninc (fun _ : Fin 1 => 1) :=
  fun _ _ _ => le_rfl

lemma isNoninc_2200 : IsNoninc seq2200 := by
  intro i j hij
  unfold seq2200
  have : i.val ≤ j.val := hij
  split_ifs <;> omega

lemma isNoninc_empty (d : Fin 0 → ℕ) : IsNoninc d :=
  fun i _ _ => isEmptyElim i

/-! ## Permutation invariance of `IsGraphic` -/

lemma nodup_map_snd_tagged {n : ℕ} (d : Fin n → ℕ) :
    ((tagged d).map Prod.snd).Nodup := by
  rw [tagged, List.map_ofFn]
  exact List.nodup_ofFn.mpr injective_id

lemma nodup_map_snd_sorted {n : ℕ} (d : Fin n → ℕ) :
    ((sortedTagged d).map Prod.snd).Nodup :=
  ((List.perm_insertionSort geFst (tagged d)).map Prod.snd).nodup_iff.mpr
    (nodup_map_snd_tagged d)

lemma mem_map_snd_sorted {n : ℕ} (d : Fin n → ℕ) (j : Fin n) :
    j ∈ (sortedTagged d).map Prod.snd := by
  have : j ∈ (tagged d).map Prod.snd := by
    simp [tagged, List.map_ofFn, List.mem_ofFn]
  exact ((List.perm_insertionSort geFst (tagged d)).map Prod.snd).mem_iff.mpr this

lemma length_map_snd {n : ℕ} (d : Fin n → ℕ) :
    ((sortedTagged d).map Prod.snd).length = n := by
  simp [List.length_map, length_sortedTagged]

/-- The index permutation realised by the nonincreasing sort. -/
def sortEquiv {n : ℕ} (d : Fin n → ℕ) : Equiv.Perm (Fin n) :=
  (finCongr (length_map_snd d).symm).trans
    (List.Nodup.getEquivOfForallMemList
      ((sortedTagged d).map Prod.snd)
      (nodup_map_snd_sorted d)
      (mem_map_snd_sorted d))

lemma sortIndex_eq_sortEquiv {n : ℕ} (d : Fin n → ℕ) (i : Fin n) :
    sortIndex d i = sortEquiv d i := by
  simp [sortEquiv, sortIndex, Equiv.trans_apply,
    List.Nodup.getEquivOfForallMemList]

lemma sortNoninc_eq_comp_equiv {n : ℕ} (d : Fin n → ℕ) :
    sortNoninc d = d ∘ sortEquiv d := by
  funext i
  rw [sortNoninc_eq_comp, Function.comp_apply, sortIndex_eq_sortEquiv]

lemma isNoninc_sortNoninc {n : ℕ} (d : Fin n → ℕ) : IsNoninc (sortNoninc d) := by
  intro i j hij
  have hs : (sortedTagged d).Sorted geFst :=
    List.sorted_insertionSort geFst (tagged d)
  have hij' :
      (⟨i.val, get_lt_sortedTagged d i⟩ : Fin (sortedTagged d).length) ≤
        ⟨j.val, get_lt_sortedTagged d j⟩ :=
    Fin.mk_le_mk.mpr hij
  exact List.Sorted.rel_get_of_le hs hij'

lemma degree_comap_perm {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (π : Equiv.Perm V) (v : V) :
    (G.comap (π : V → V)).degree v = G.degree (π v) := by
  change ((G.comap π).neighborFinset v).card = (G.neighborFinset (π v)).card
  have hset :
      (G.comap π).neighborFinset v =
        (G.neighborFinset (π v)).map π.symm.toEmbedding := by
    ext w
    simp only [Finset.mem_map, mem_neighborFinset, comap_adj, Equiv.coe_toEmbedding]
    constructor
    · intro hw
      exact ⟨π w, hw, Equiv.symm_apply_apply π w⟩
    · rintro ⟨x, hx, hπ⟩
      have hx' : x = π w := by rw [← hπ, Equiv.apply_symm_apply]
      subst hx'
      exact hx
  rw [hset, Finset.card_map]

lemma isGraphic_comp_perm {n : ℕ} {d : Fin n → ℕ} (π : Equiv.Perm (Fin n)) :
    IsGraphic (d ∘ π) ↔ IsGraphic d := by
  constructor
  · rintro ⟨G, inst, hdeg⟩
    letI := inst
    refine ⟨G.comap π.symm, inferInstance, fun i => ?_⟩
    rw [degree_comap_perm, hdeg]
    simp [Function.comp]
  · rintro ⟨G, inst, hdeg⟩
    letI := inst
    refine ⟨G.comap π, inferInstance, fun i => ?_⟩
    rw [degree_comap_perm, hdeg]
    rfl

lemma isGraphic_sortNoninc {n : ℕ} (d : Fin n → ℕ) :
    IsGraphic (sortNoninc d) ↔ IsGraphic d := by
  rw [sortNoninc_eq_comp_equiv, isGraphic_comp_perm]

/-- The Havel–Hakimi reduction of a successful sequence. -/
def reduce {n : ℕ} (d : Fin n → ℕ) (_h : ReduceOK d) : Fin n.pred → ℕ :=
  match n, d with
  | 0, d => d
  | _n + 1, d => sortNoninc (reduceUnsorted d)

/-! ## Failed reduction ⇒ ¬ IsGraphic -/

lemma card_nonzero_le {n t : ℕ} :
    ((Finset.univ : Finset (Fin (n + 1))).filter
      (fun x : Fin (n + 1) => x ≠ 0 ∧ x.val ≤ t)).card ≤ t := by
  -- injectively send each such vertex to its `val` in `Icc 1 t`
  refine (Finset.card_le_card_of_injOn (fun x : Fin (n + 1) => x.val)
      (s := (Finset.univ.filter (fun x : Fin (n + 1) => x ≠ 0 ∧ x.val ≤ t)))
      (t := Finset.Icc (1 : ℕ) t) ?_ ?_).trans ?_
  · intro x hx
    have hx' := Finset.mem_filter.mp hx
    exact Finset.mem_Icc.2
      ⟨Nat.succ_le_of_lt (Fin.pos_iff_ne_zero.mpr hx'.2.1), hx'.2.2⟩
  · intro x _ y _ h
    exact Fin.ext h
  · simp [Nat.card_Icc]

lemma reduceOK_of_isGraphic {n : ℕ} {d : Fin n → ℕ} (hni : IsNoninc d)
    (hg : IsGraphic d) : ReduceOK d := by
  cases n with
  | zero => trivial
  | succ n =>
    refine ⟨Nat.lt_succ_iff.mp (graphic_degree_lt hg 0), ?_⟩
    intro i hi
    by_contra h0
    have hi0 : d i.succ = 0 := Nat.eq_zero_of_not_pos h0
    obtain ⟨G, inst, hdeg⟩ := hg
    letI := inst
    have nbd : G.neighborFinset 0 ⊆
        Finset.univ.filter (fun x : Fin (n + 1) => x ≠ 0 ∧ x.val ≤ i.val) := by
      intro x hx
      have hadj : G.Adj 0 x := (mem_neighborFinset _ _ _).1 hx
      have hx0 : x ≠ 0 := (G.ne_of_adj hadj).symm
      have hxval : x.val ≤ i.val := by
        by_contra hgt
        have hge : i.succ ≤ x := by
          have : i.val + 1 ≤ x.val := Nat.succ_le_iff.mpr (lt_of_not_ge hgt)
          exact Fin.mk_le_mk.mpr (by simpa [Fin.succ] using this)
        have : d x ≤ 0 := (hni hge).trans (le_of_eq hi0)
        have : G.degree x = 0 := (hdeg x).trans (Nat.eq_zero_of_le_zero this)
        have : 0 < G.degree x := (degree_pos_iff_exists_adj _ _).2 ⟨0, hadj.symm⟩
        omega
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨hx0, hxval⟩⟩
    have : G.degree 0 ≤ i.val :=
      (Finset.card_le_card nbd).trans card_nonzero_le
    have : d 0 ≤ i.val := by simpa [hdeg 0] using this
    omega

lemma not_graphic_of_not_reduceOK {n : ℕ} {d : Fin n → ℕ} (hni : IsNoninc d)
    (h : ¬ ReduceOK d) : ¬ IsGraphic d :=
  fun hg => h (reduceOK_of_isGraphic hni hg)

/-! ## Reverse reduction: insert a vertex adjacent to the first `s` -/

lemma exists_pred {n : ℕ} {x : Fin (n + 1)} (hx : x ≠ 0) :
    ∃ k : Fin n, x = k.succ := by
  refine ⟨⟨x.val - 1, ?_⟩, Fin.ext ?_⟩
  · have : 0 < x.val := Fin.pos_iff_ne_zero.mpr hx
    have : x.val < n + 1 := x.isLt
    omega
  · have : 0 < x.val := Fin.pos_iff_ne_zero.mpr hx
    simp [Fin.succ]
    omega

def insertMax {n : ℕ} (H : SimpleGraph (Fin n)) (s : ℕ) :
    SimpleGraph (Fin (n + 1)) :=
  fromEdgeSet <|
    (Sym2.map Fin.succ '' H.edgeSet) ∪
      {e | ∃ k : Fin n, k.val < s ∧ e = s(0, k.succ)}

instance insertMax.decidableRel {n : ℕ} (H : SimpleGraph (Fin n))
    [DecidableRel H.Adj] (s : ℕ) : DecidableRel (insertMax H s).Adj := by
  infer_instance

lemma insertMax_adj {n : ℕ} {H : SimpleGraph (Fin n)} {s : ℕ}
    {x y : Fin (n + 1)} :
    (insertMax H s).Adj x y ↔
      (x = 0 ∧ ∃ k : Fin n, y = k.succ ∧ k.val < s) ∨
      (y = 0 ∧ ∃ k : Fin n, x = k.succ ∧ k.val < s) ∨
      (∃ a b : Fin n, x = a.succ ∧ y = b.succ ∧ H.Adj a b) := by
  simp only [insertMax, fromEdgeSet_adj, Set.mem_union, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hmem, hne⟩
    rcases hmem with ⟨e, he, hmap⟩ | ⟨k, hk, heq⟩
    · revert hmap
      revert he
      refine e.inductionOn fun a b he hmap => ?_
      have hab : H.Adj a b := (mem_edgeSet _).mp he
      simp only [Sym2.map_pair_eq, Sym2.eq_iff] at hmap
      rcases hmap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr (Or.inr ⟨a, b, rfl, rfl, hab⟩)
      · exact Or.inr (Or.inr ⟨b, a, rfl, rfl, hab.symm⟩)
    · simp only [Sym2.eq_iff] at heq
      rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, k, rfl, hk⟩
      · exact Or.inr (Or.inl ⟨rfl, k, rfl, hk⟩)
  · intro h
    rcases h with ⟨rfl, k, rfl, hk⟩ | ⟨rfl, k, rfl, hk⟩ | ⟨a, b, rfl, rfl, hab⟩
    · exact ⟨Or.inr ⟨k, hk, rfl⟩, (Fin.succ_ne_zero k).symm⟩
    · exact ⟨Or.inr ⟨k, hk, Sym2.eq_swap⟩, Fin.succ_ne_zero k⟩
    · exact ⟨Or.inl ⟨s(a, b), (mem_edgeSet _).mpr hab, by simp [Sym2.map_pair_eq]⟩,
        (Fin.succ_injective n).ne (H.ne_of_adj hab)⟩

lemma card_filter_val_lt {n s : ℕ} (hs : s ≤ n) :
    ((Finset.univ : Finset (Fin n)).filter (fun k => k.val < s)).card = s := by
  trans (Finset.univ : Finset (Fin s)).card
  · refine Finset.card_bij
      (fun k hk => (⟨k.val, (Finset.mem_filter.mp hk).2⟩ : Fin s))
      (fun _ _ => Finset.mem_univ _)
      (fun a _ b _ h => Fin.ext (congr_arg (Fin.val : Fin s → ℕ) h))
      (fun k _ =>
        ⟨⟨k.val, Nat.lt_of_lt_of_le k.isLt hs⟩,
          Finset.mem_filter.2 ⟨Finset.mem_univ _, k.isLt⟩, Fin.ext rfl⟩)
  · simp

lemma insertMax_degree_zero {n : ℕ} (H : SimpleGraph (Fin n))
    [DecidableRel H.Adj] {s : ℕ} (hs : s ≤ n) :
    (insertMax H s).degree 0 = s := by
  have hset :
      (insertMax H s).neighborFinset 0 =
        ((Finset.univ.filter (fun k : Fin n => k.val < s)).map (Fin.succEmb n)) := by
    ext x
    constructor
    · intro hx
      have hadj : (insertMax H s).Adj 0 x := (mem_neighborFinset _ _ _).1 hx
      rcases (insertMax_adj (H := H) (s := s)).mp hadj with h | h | h
      · obtain ⟨_, k, rfl, hk⟩ := h
        exact Finset.mem_map.2 ⟨k, Finset.mem_filter.2 ⟨Finset.mem_univ _, hk⟩, rfl⟩
      · obtain ⟨rfl, _⟩ := h
        exact (SimpleGraph.loopless _ _ hadj).elim
      · obtain ⟨a, _, ha, _, _⟩ := h
        exact (Fin.succ_ne_zero a ha.symm).elim
    · intro hx
      obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hx
      have hk' : k.val < s := (Finset.mem_filter.mp hk).2
      exact (mem_neighborFinset _ _ _).2
        ((insertMax_adj (H := H) (s := s)).mpr (Or.inl ⟨rfl, k, rfl, hk'⟩))
  rw [degree, hset, Finset.card_map, card_filter_val_lt hs]

lemma insertMax_degree_succ {n : ℕ} (H : SimpleGraph (Fin n))
    [DecidableRel H.Adj] {s : ℕ} (k : Fin n) :
    (insertMax H s).degree k.succ =
      H.degree k + if k.val < s then 1 else 0 := by
  have hset :
      (insertMax H s).neighborFinset k.succ =
        (H.neighborFinset k).map (Fin.succEmb n) ∪
          if k.val < s then {0} else (∅ : Finset (Fin (n + 1))) := by
    ext x
    constructor
    · intro hx
      have hadj : (insertMax H s).Adj k.succ x := (mem_neighborFinset _ _ _).1 hx
      rw [Finset.mem_union]
      rcases (insertMax_adj (H := H) (s := s)).mp hadj with h | h | h
      · obtain ⟨hk0, _⟩ := h
        exact (Fin.succ_ne_zero k hk0).elim
      · obtain ⟨rfl, k', hk', hkval⟩ := h
        have : k' = k := Fin.succ_injective n hk'.symm
        subst this
        refine Or.inr ?_
        simp [hkval]
      · obtain ⟨a, b, ha, hb, hab⟩ := h
        have : a = k := Fin.succ_injective n ha.symm
        subst this
        refine Or.inl (Finset.mem_map.2 ⟨b, (mem_neighborFinset _ _ _).2 hab, hb.symm⟩)
    · intro hx
      rw [Finset.mem_union] at hx
      rcases hx with hx | hx
      · obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hx
        exact (mem_neighborFinset _ _ _).2
          ((insertMax_adj (H := H) (s := s)).mpr
            (Or.inr (Or.inr ⟨k, b, rfl, rfl, (mem_neighborFinset _ _ _).1 hb⟩)))
      · by_cases hks : k.val < s
        · simp [hks] at hx
          subst x
          exact (mem_neighborFinset _ _ _).2
            ((insertMax_adj (H := H) (s := s)).mpr
              (Or.inr (Or.inl ⟨rfl, k, rfl, hks⟩)))
        · simp [hks] at hx
  have hdisj :
      Disjoint ((H.neighborFinset k).map (Fin.succEmb n))
        (if k.val < s then ({0} : Finset (Fin (n + 1))) else ∅) := by
    split_ifs
    · rw [Finset.disjoint_singleton_right]
      simp [Finset.mem_map]
      intro b _ hb
      exact Fin.succ_ne_zero b hb
    · simp
  rw [degree, hset, Finset.card_union_of_disjoint hdisj, Finset.card_map]
  split_ifs
  · rw [card_neighborFinset_eq_degree, Finset.card_singleton]
  · rw [card_neighborFinset_eq_degree, Finset.card_empty, add_zero]

lemma isGraphic_insert {n : ℕ} {d : Fin (n + 1) → ℕ}
    (hok : ReduceOK (n := n + 1) d)
    (hH : IsGraphic (reduceUnsorted d)) : IsGraphic d := by
  obtain ⟨H, inst, hdeg⟩ := hH
  letI := inst
  obtain ⟨hs, hpos⟩ := hok
  refine ⟨insertMax H (d 0), inferInstance, fun x => ?_⟩
  rcases eq_or_ne x 0 with rfl | hx
  · simpa using insertMax_degree_zero H hs
  · obtain ⟨k, rfl⟩ := exists_pred hx
    rw [insertMax_degree_succ, hdeg]
    unfold reduceUnsorted
    split_ifs with hks
    · have : 0 < d k.succ := hpos k hks
      omega
    · simp

/-- Constructive reverse-reduction (STATEMENT.md: same heartbeat as the iff). -/
lemma isGraphic_of_reduce {n : ℕ} {d : Fin n → ℕ} (hok : ReduceOK d)
    (hr : IsGraphic (reduce d hok)) : IsGraphic d := by
  match n, d, hok, hr with
  | 0, _d, _, hr => exact hr
  | n + 1, d, hok, hr =>
    have : IsGraphic (reduceUnsorted d) := (isGraphic_sortNoninc _).mp hr
    exact isGraphic_insert hok this

end ProofLab.HavelHakimi
