/-
Dirac's theorem (1952): δ ≥ n/2 ⇒ Hamiltonian cycle.

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 has `Walk.IsHamiltonian` / `IsHamiltonianCycle` /
`SimpleGraph.IsHamiltonian` but no degree sufficient-condition.

Pin: `catalog/problems/dirac-hamiltonian/STATEMENT.md` (OPE-559).
Encoding: Mathlib `SimpleGraph` + `Walk`. Zero `sorry`.
`n ≥ 3` is load-bearing (`K₂` is a counterexample). Claim is a cycle,
not a path. Integer form `2 * minDegree ≥ n`. Completeness `⊤` is a
lemma, not the theorem. Singleton `IsHamiltonian` convention unused.

Level A (this heartbeat): n = 3, complete graphs, connectedness from δ.
Level B residual: longest-path / cycle-closing (Bondy–Murty / Diestel).
-/
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

open Finset Function SimpleGraph

namespace ProofLab.Dirac

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

local notation "n" => Fintype.card V

/-! ## Degree dictionary -/

lemma neighborFinset_subset_erase (u : V) :
    G.neighborFinset u ⊆ univ.erase u := by
  intro x hx
  exact mem_erase.mpr
    ⟨(G.ne_of_adj ((mem_neighborFinset G u x).mp hx)).symm, mem_univ x⟩

lemma degree_eq_card_sub_one_iff {u : V} :
    G.degree u = n - 1 ↔ ∀ w : V, w ≠ u → G.Adj u w := by
  constructor
  · intro hd w hw
    have heq : G.neighborFinset u = univ.erase u :=
      eq_of_subset_of_card_le (neighborFinset_subset_erase u) (by
        have : (univ.erase u).card = n - 1 := card_erase_of_mem (mem_univ u)
        rw [this, ← hd]
        exact le_rfl)
    exact (mem_neighborFinset G u w).mp
      (heq.symm ▸ mem_erase.mpr ⟨hw, mem_univ w⟩)
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

lemma eq_top_of_forall_degree_pred (h : ∀ u : V, G.degree u = n - 1) :
    G = ⊤ := by
  ext u v
  constructor
  · intro hadj
    exact hadj.ne
  · intro hne
    exact (degree_eq_card_sub_one_iff (G := G)).mp (h u) v ((top_adj u v).mp hne).symm

lemma two_le_minDegree_of_dirac (hn : 3 ≤ n) (hδ : n ≤ 2 * G.minDegree) :
    2 ≤ G.minDegree := by
  have hpos : 0 < n := lt_of_lt_of_le (by decide : 0 < 3) hn
  haveI : Nonempty V := Fintype.card_pos_iff.mp hpos
  obtain ⟨v, hv⟩ := G.exists_minimal_degree_vertex
  have := G.degree_lt_card_verts v
  omega

lemma concat_isPath {u v w : V} {p : G.Walk u v} (hp : p.IsPath) {h : G.Adj v w}
    (hw : w ∉ p.support) : (p.concat h).IsPath :=
  Walk.IsPath.mk' (by
    rw [Walk.support_concat]
    exact List.Nodup.concat hw hp.support_nodup)

/-! ## Level A: complete graphs (`⊤`) are Hamiltonian for `n ≥ 3` -/

/-- Increasing path `a — a+1 — … — a+d` in the complete graph on `Fin m`.
Visited vertices have values in `[a, a+d]`. -/
lemma exists_fin_path_up (m a d : ℕ) (ha : a < m) (hd : a + d < m) :
    ∃ p : (⊤ : SimpleGraph (Fin m)).Walk ⟨a, ha⟩ ⟨a + d, hd⟩,
      p.IsPath ∧ p.length = d ∧ ∀ x ∈ p.support, a ≤ (x : ℕ) ∧ (x : ℕ) ≤ a + d := by
  induction d with
  | zero =>
    refine ⟨Walk.nil.copy rfl (Fin.ext (by simp)), ?_, by simp, ?_⟩
    · exact Walk.IsPath.nil
    · intro x hx
      simp only [Walk.support_copy, Walk.support_nil, List.mem_singleton] at hx
      subst x
      simp
  | succ d ih =>
    have hd' : a + d < m := by omega
    obtain ⟨p, hp, hlen, hge⟩ := ih hd'
    have hadj : (⊤ : SimpleGraph (Fin m)).Adj ⟨a + d, hd'⟩ ⟨a + (d + 1), hd⟩ := by
      rw [top_adj]
      exact Fin.ne_of_val_ne (Nat.ne_of_lt (Nat.lt_succ_self (a + d)))
    refine ⟨p.concat hadj, concat_isPath hp ?_, ?_, ?_⟩
    · intro hmem
      have hbd := hge _ hmem
      have : a + (d + 1) ≤ a + d := by simpa using hbd.2
      omega
    · simp [hlen]
    · intro x hx
      rw [Walk.support_concat, List.concat_eq_append, List.mem_append,
        List.mem_singleton] at hx
      rcases hx with hx | rfl
      · obtain ⟨hlo, hhi⟩ := hge x hx
        exact ⟨hlo, Nat.le_succ_of_le hhi⟩
      · exact ⟨Nat.le_add_right a (d + 1), le_rfl⟩

lemma isHamiltonianCycle_of_cycle_length {a : V} {p : G.Walk a a}
    (hp : p.IsCycle) (hlen : p.length = n) : p.IsHamiltonianCycle := by
  refine ⟨hp, ?_⟩
  have hnn : ¬ p.Nil := hp.not_nil
  have hpath : (p.tail hnn).IsPath := by
    cases p with
    | nil => exact (hnn Walk.nil_nil).elim
    | cons h q =>
      simpa [Walk.tail_cons] using ((Walk.cons_isCycle_iff q h).1 hp).1
  apply hpath.isHamiltonian_of_mem
  intro w
  have hlen_tail : (p.tail hnn).length = n - 1 := by
    have := Walk.length_tail_add_one hnn
    omega
  have hsupp : (p.tail hnn).support.length = n := by
    rw [Walk.length_support, hlen_tail]
    have : 1 ≤ n := by
      have : 3 ≤ p.length := hp.three_le_length
      omega
    omega
  have hcard : (p.tail hnn).support.toFinset.card = n := by
    rw [List.toFinset_card_of_nodup hpath.support_nodup, hsupp]
  have huni : (p.tail hnn).support.toFinset = univ :=
    Finset.eq_univ_of_card _ hcard
  exact List.mem_toFinset.mp (by rw [huni]; exact mem_univ w)

lemma isHamiltonian_complete_fin (m : ℕ) (hm : 3 ≤ m) :
    (⊤ : SimpleGraph (Fin m)).IsHamiltonian := by
  intro _hne
  have h0 : 0 < m := lt_of_lt_of_le (by decide : 0 < 3) hm
  have h1 : 1 < m := lt_of_lt_of_le (by decide : 1 < 3) hm
  have hlast : 1 + (m - 2) < m := by omega
  obtain ⟨q, hq, hlen, hge⟩ := exists_fin_path_up m 1 (m - 2) h1 hlast
  have hadjLast : (⊤ : SimpleGraph (Fin m)).Adj ⟨1 + (m - 2), hlast⟩ ⟨0, h0⟩ := by
    rw [top_adj]
    exact Fin.ne_of_val_ne (by
      change (1 + (m - 2) : ℕ) ≠ 0
      rw [Nat.add_comm]
      exact Nat.succ_ne_zero _)
  have hadj01 : (⊤ : SimpleGraph (Fin m)).Adj ⟨0, h0⟩ ⟨1, h1⟩ := by
    rw [top_adj]
    exact Fin.ne_of_val_ne Nat.zero_ne_one
  let r : (⊤ : SimpleGraph (Fin m)).Walk ⟨1, h1⟩ ⟨0, h0⟩ := q.concat hadjLast
  have hr : r.IsPath := concat_isPath hq (by
    intro hmem
    exact Nat.not_succ_le_self 0 (hge _ hmem).1)
  have hedge : s((⟨0, h0⟩ : Fin m), ⟨1, h1⟩) ∉ r.edges := by
    intro he
    rw [show r.edges = q.edges.concat s((⟨1 + (m - 2), hlast⟩ : Fin m), ⟨0, h0⟩)
      from Walk.edges_concat q hadjLast, List.concat_eq_append, List.mem_append,
      List.mem_singleton] at he
    rcases he with hqe | hsy
    · have h0q : (⟨0, h0⟩ : Fin m) ∈ q.support :=
        Walk.fst_mem_support_of_mem_edges q hqe
      exact Nat.not_succ_le_self 0 (hge _ h0q).1
    · have : (⟨1 + (m - 2), hlast⟩ : Fin m) = ⟨1, h1⟩ ∨
          (⟨0, h0⟩ : Fin m) = ⟨1, h1⟩ := by
        simpa [Sym2.eq_iff] using hsy
      rcases this with h | h
      · have hval := Fin.val_eq_of_eq h
        have : 1 + (m - 2) = 1 := hval
        have : m = 2 := by omega
        omega
      · exact absurd (Fin.val_eq_of_eq h) (Nat.zero_ne_one)
  have hcyc : (Walk.cons hadj01 r).IsCycle :=
    (Walk.cons_isCycle_iff r hadj01).2 ⟨hr, hedge⟩
  have hlen' : (Walk.cons hadj01 r).length = m := by
    simp [r, hlen]
    omega
  refine ⟨⟨0, h0⟩, Walk.cons hadj01 r,
    isHamiltonianCycle_of_cycle_length (V := Fin m) hcyc (by
      simpa [Fintype.card_fin] using hlen')⟩

lemma isHamiltonian_complete (hn : 3 ≤ n) :
    (⊤ : SimpleGraph V).IsHamiltonian := by
  intro hne
  let e : V ≃ Fin n := Fintype.equivFin V
  obtain ⟨a, p, hp⟩ := isHamiltonian_complete_fin n hn (by
    simpa [Fintype.card_fin] using hne)
  let f : (⊤ : SimpleGraph (Fin n)) →g (⊤ : SimpleGraph V) :=
    (Iso.completeGraph e.symm).toHom
  refine ⟨e.symm a, p.map f, hp.map f (Equiv.bijective e.symm)⟩

/-! ## Level A: n = 3 -/

lemma eq_top_of_dirac_card_eq_three (hn : n = 3) (hδ : n ≤ 2 * G.minDegree) :
    G = ⊤ := by
  have hpos : 0 < n := by omega
  haveI : Nonempty V := Fintype.card_pos_iff.mp hpos
  apply eq_top_of_forall_degree_pred
  intro u
  have hle := G.minDegree_le_degree u
  have hlt := G.degree_lt_card_verts u
  omega

/-- Dirac for `n = 3`: the bound forces `K₃`. -/
theorem dirac_hamiltonian_card_eq_three (hn : n = 3)
    (hδ : n ≤ 2 * G.minDegree) : G.IsHamiltonian := by
  rw [eq_top_of_dirac_card_eq_three hn hδ]
  exact isHamiltonian_complete (by omega)

/-! ## Level A: connectedness from δ -/

lemma card_component_bound (u : V) (_hn : 3 ≤ n) (hδ : n ≤ 2 * G.minDegree) :
    n ≤ 2 * ((univ.filter fun w => G.Reachable u w).card - 1) := by
  let C := univ.filter fun w => G.Reachable u w
  have hu : u ∈ C := mem_filter.mpr ⟨mem_univ u, Reachable.refl u⟩
  have hsub : G.neighborFinset u ⊆ C.erase u := by
    intro w hw
    have hadj : G.Adj u w := (mem_neighborFinset G u w).mp hw
    exact mem_erase.mpr ⟨hadj.ne.symm,
      mem_filter.mpr ⟨mem_univ w, Adj.reachable hadj⟩⟩
  have hdeg : G.degree u ≤ C.card - 1 := by
    have : (C.erase u).card = C.card - 1 := card_erase_of_mem hu
    rw [← this, ← card_neighborFinset_eq_degree]
    exact card_le_card hsub
  exact le_trans hδ (Nat.mul_le_mul_left _ (le_trans (G.minDegree_le_degree u) hdeg))

theorem connected_of_dirac (hn : 3 ≤ n) (hδ : n ≤ 2 * G.minDegree) :
    G.Connected := by
  have hpos : 0 < n := lt_of_lt_of_le (by decide : 0 < 3) hn
  haveI : Nonempty V := Fintype.card_pos_iff.mp hpos
  refine { preconnected := ?_ }
  intro u v
  by_contra hnr
  let C := univ.filter fun w => G.Reachable u w
  let D := univ.filter fun w => G.Reachable v w
  have hC := card_component_bound (u := u) hn hδ
  have hD := card_component_bound (u := v) hn hδ
  have hu : u ∈ C := mem_filter.mpr ⟨mem_univ u, Reachable.refl u⟩
  have hv : v ∈ D := mem_filter.mpr ⟨mem_univ v, Reachable.refl v⟩
  have hdisj : Disjoint C D := by
    rw [disjoint_left]
    intro x hxC hxD
    have hxu : G.Reachable u x := (mem_filter.mp hxC).2
    have hxv : G.Reachable v x := (mem_filter.mp hxD).2
    exact hnr (hxu.trans hxv.symm)
  have hsum : C.card + D.card ≤ n := by
    have : (C ∪ D).card = C.card + D.card := card_union_of_disjoint hdisj
    rw [← this]
    exact card_le_card (subset_univ _)
  have hC' : n ≤ 2 * (C.card - 1) := by simpa [C] using hC
  have hD' : n ≤ 2 * (D.card - 1) := by simpa [D] using hD
  have : 1 ≤ C.card := card_pos.mpr ⟨u, hu⟩
  have : 1 ≤ D.card := card_pos.mpr ⟨v, hv⟩
  omega

/-! ## Level A sanity: Dirac hypotheses on `K_n` -/

lemma minDegree_top (hV : Nonempty V) : (⊤ : SimpleGraph V).minDegree = n - 1 := by
  apply le_antisymm
  · obtain ⟨v, hv⟩ := (⊤ : SimpleGraph V).exists_minimal_degree_vertex
    have := (⊤ : SimpleGraph V).degree_lt_card_verts v
    rw [hv]
    omega
  · apply le_minDegree_of_forall_le_degree
    intro v
    simp [complete_graph_degree]

lemma two_mul_minDegree_top (hn : 3 ≤ n) :
    n ≤ 2 * (⊤ : SimpleGraph V).minDegree := by
  have hpos : 0 < n := lt_of_lt_of_le (by decide : 0 < 3) hn
  haveI : Nonempty V := Fintype.card_pos_iff.mp hpos
  rw [minDegree_top inferInstance]
  omega

/-- Optional tiny `n = 3` sanity: `K₃` meets the Dirac hypotheses and is Hamiltonian. -/
theorem complete_fin_three_isHamiltonian :
    (⊤ : SimpleGraph (Fin 3)).IsHamiltonian :=
  isHamiltonian_complete_fin 3 (by decide)

end ProofLab.Dirac

