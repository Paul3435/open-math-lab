/-
Dirac's theorem (1952): δ ≥ n/2 ⇒ Hamiltonian cycle.

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 has `Walk.IsHamiltonian` / `IsHamiltonianCycle` /
`SimpleGraph.IsHamiltonian` but no degree sufficient-condition.

Pin: `catalog/problems/dirac-hamiltonian/STATEMENT.md` (OPE-559 / OPE-568).
Encoding: Mathlib `SimpleGraph` + `Walk`. Zero `sorry`.
`n ≥ 3` is load-bearing (`K₂` is a counterexample). Claim is a cycle,
not a path. Integer form `2 * minDegree ≥ n`. Completeness `⊤` is a
lemma, not the theorem. Singleton `IsHamiltonian` convention unused.

Level A (OPE-559): n = 3, complete graphs, connectedness from δ.
Level B (OPE-568): longest-path / cycle-closing (Bondy–Murty / Diestel).
  The longest-path lemma is an internal tool, not the claim.
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

/-! ## Level B: longest-path dictionary (internal tool, not the claim) -/

lemma getVert_mem_support {u v : V} (p : G.Walk u v) {i : ℕ} (hi : i ≤ p.length) :
    p.getVert i ∈ p.support :=
  Walk.mem_support_iff_exists_getVert.2 ⟨i, rfl, hi⟩

lemma getVert_eq_support_get {u v : V} :
    ∀ (p : G.Walk u v) {i : ℕ} (hi : i < p.support.length),
      p.getVert i = p.support.get ⟨i, hi⟩
  | .nil, i, hi => by
      simp only [Walk.support_nil, List.length_singleton] at hi
      have : i = 0 := Nat.lt_one_iff.mp hi
      subst i; rfl
  | .cons _ q, 0, _ => rfl
  | .cons _ q, i + 1, hi => by
      have hi' : i < q.support.length := by
        simpa [Walk.support_cons, List.length_cons] using hi
      simpa [Walk.getVert, Walk.support_cons] using getVert_eq_support_get q hi'

lemma getVert_inj_of_isPath {u v : V} {p : G.Walk u v} (hp : p.IsPath)
    {i j : ℕ} (hi : i ≤ p.length) (hj : j ≤ p.length)
    (heq : p.getVert i = p.getVert j) : i = j := by
  have hi' : i < p.support.length := by rw [Walk.length_support]; omega
  have hj' : j < p.support.length := by rw [Walk.length_support]; omega
  have hget : p.support.get ⟨i, hi'⟩ = p.support.get ⟨j, hj'⟩ := by
    rw [← getVert_eq_support_get p hi', ← getVert_eq_support_get p hj', heq]
  exact Fin.val_eq_of_eq (List.nodup_iff_injective_get.mp hp.support_nodup hget)

/-- A path of globally maximal length. Internal tool. -/
lemma exists_longest_path (hV : Nonempty V) :
    ∃ (u v : V) (p : G.Walk u v), p.IsPath ∧
      ∀ {u' v' : V} (q : G.Walk u' v'), q.IsPath → q.length ≤ p.length := by
  let s : Set ℕ := {k | ∃ (u v : V) (p : G.Walk u v), p.IsPath ∧ p.length = k}
  have hsne : s.Nonempty := by
    obtain ⟨x⟩ := hV
    exact ⟨0, ⟨x, x, Walk.nil, Walk.IsPath.nil, rfl⟩⟩
  have hsfin : s.Finite :=
    (Set.finite_lt_nat n).subset fun k hk => by
      obtain ⟨_, _, p, hp, rfl⟩ := hk
      exact hp.length_lt
  obtain ⟨k, hks, hkmax⟩ := Set.Finite.exists_maximal_wrt (id : ℕ → ℕ) s hsfin hsne
  obtain ⟨u, v, p, hp, hpk⟩ := hks
  refine ⟨u, v, p, hp, fun q hq => ?_⟩
  have hqmem : q.length ∈ s := ⟨_, _, q, hq, rfl⟩
  cases le_total q.length k with
  | inl h => simpa [hpk] using h
  | inr h =>
    have := hkmax q.length hqmem h
    simp only [id_eq] at this
    omega

lemma adj_start_mem_support_of_maximal {u v w : V} {p : G.Walk u v}
    (hp : p.IsPath)
    (hmax : ∀ {u' v' : V} (q : G.Walk u' v'), q.IsPath → q.length ≤ p.length)
    (hw : G.Adj u w) : w ∈ p.support := by
  by_contra hnotin
  have hp' : (Walk.cons hw.symm p).IsPath := hp.cons hnotin
  have := hmax (Walk.cons hw.symm p) hp'
  simp at this

lemma adj_end_mem_support_of_maximal {u v w : V} {p : G.Walk u v}
    (hp : p.IsPath)
    (hmax : ∀ {u' v' : V} (q : G.Walk u' v'), q.IsPath → q.length ≤ p.length)
    (hw : G.Adj v w) : w ∈ p.support := by
  by_contra hnotin
  have hp' : (p.concat hw).IsPath := concat_isPath hp hnotin
  have := hmax (p.concat hw) hp'
  simp [Walk.length_concat] at this

lemma two_le_length_of_dirac_longest {u v : V} {p : G.Walk u v}
    (hn : 3 ≤ n) (hδ : n ≤ 2 * G.minDegree) (hp : p.IsPath)
    (hmax : ∀ {u' v' : V} (q : G.Walk u' v'), q.IsPath → q.length ≤ p.length) :
    2 ≤ p.length := by
  have hδ2 := two_le_minDegree_of_dirac hn hδ
  have hdeg : 2 ≤ G.degree u := le_trans hδ2 (G.minDegree_le_degree u)
  have hcard : 2 ≤ (G.neighborFinset u).card := hdeg
  have hsub : G.neighborFinset u ⊆ p.support.toFinset.erase u := by
    intro w hw
    have hadj : G.Adj u w := (mem_neighborFinset G u w).mp hw
    exact mem_erase.mpr ⟨hadj.ne.symm, List.mem_toFinset.mpr
      (adj_start_mem_support_of_maximal hp hmax hadj)⟩
  have hu : u ∈ p.support.toFinset := List.mem_toFinset.mpr (Walk.start_mem_support p)
  have : 2 ≤ p.support.toFinset.card - 1 := by
    have := card_le_card hsub
    simpa [card_erase_of_mem hu, card_neighborFinset_eq_degree] using
      (le_trans hcard this)
  have hnodup := hp.support_nodup
  have hsc : p.support.toFinset.card = p.support.length :=
    List.toFinset_card_of_nodup hnodup
  rw [hsc, Walk.length_support] at this
  omega

/-- Cycle-closing index on a longest path: some `i` with `v — xᵢ` and `u — xᵢ₊₁`. -/
lemma exists_cycle_closing {u v : V} {p : G.Walk u v} (hp : p.IsPath)
    (hmax : ∀ {u' v' : V} (q : G.Walk u' v'), q.IsPath → q.length ≤ p.length)
    (hδ : n ≤ 2 * G.minDegree) :
    ∃ i, i < p.length ∧ G.Adj v (p.getVert i) ∧ G.Adj u (p.getVert (i + 1)) := by
  let k := p.length
  let A := (Finset.range k).filter fun i => G.Adj u (p.getVert (i + 1))
  let B := (Finset.range k).filter fun i => G.Adj v (p.getVert i)
  have hA : A.card = G.degree u := by
    refine Finset.card_bij (fun i _ => p.getVert (i + 1)) ?_ ?_ ?_
    · intro i hi
      exact (mem_neighborFinset G u _).mpr (mem_filter.mp hi).2
    · intro i hi j hj heq
      have hik : i + 1 ≤ k := by
        have := (mem_filter.mp hi).1
        simp only [mem_range, k] at this
        omega
      have hjk : j + 1 ≤ k := by
        have := (mem_filter.mp hj).1
        simp only [mem_range, k] at this
        omega
      have := getVert_inj_of_isPath hp hik hjk heq
      omega
    · intro w hw
      have hadj : G.Adj u w := (mem_neighborFinset G u w).mp hw
      have hwsup := adj_start_mem_support_of_maximal hp hmax hadj
      obtain ⟨j, rfl, hjle⟩ := Walk.mem_support_iff_exists_getVert.mp hwsup
      have hjpos : j ≠ 0 := by
        intro h0
        subst h0
        simp only [Walk.getVert_zero] at hadj
        exact hadj.ne rfl
      refine ⟨j - 1, ?_, ?_⟩
      · simp only [A, mem_filter, mem_range, k]
        have : j - 1 < p.length := by omega
        refine ⟨this, ?_⟩
        have : j - 1 + 1 = j := by omega
        rwa [this]
      · have : j - 1 + 1 = j := by omega
        simp [this]
  have hB : B.card = G.degree v := by
    refine Finset.card_bij (fun i _ => p.getVert i) ?_ ?_ ?_
    · intro i hi
      exact (mem_neighborFinset G v _).mpr (mem_filter.mp hi).2
    · intro i hi j hj heq
      have hik : i ≤ k := by
        have := (mem_filter.mp hi).1
        simp only [mem_range, k] at this
        omega
      have hjk : j ≤ k := by
        have := (mem_filter.mp hj).1
        simp only [mem_range, k] at this
        omega
      exact getVert_inj_of_isPath hp hik hjk heq
    · intro w hw
      have hadj : G.Adj v w := (mem_neighborFinset G v w).mp hw
      have hwsup := adj_end_mem_support_of_maximal hp hmax hadj
      obtain ⟨j, rfl, hjle⟩ := Walk.mem_support_iff_exists_getVert.mp hwsup
      have hjlt : j < k := by
        refine lt_of_le_of_ne hjle ?_
        intro hjk
        have hvj : p.getVert j = v := by rw [hjk, Walk.getVert_length]
        rw [hvj] at hadj
        exact hadj.ne rfl
      refine ⟨j, ?_, rfl⟩
      simp only [B, mem_filter, mem_range, k]
      exact ⟨hjlt, hadj⟩
  by_contra hnone
  have hdisj : Disjoint A B := by
    rw [disjoint_left]
    intro i hiA hiB
    exact hnone ⟨i, mem_range.mp (mem_filter.mp hiA).1,
      (mem_filter.mp hiB).2, (mem_filter.mp hiA).2⟩
  have hle : (A ∪ B).card ≤ k := by
    have : A ∪ B ⊆ Finset.range k :=
      union_subset (filter_subset _ _) (filter_subset _ _)
    simpa [card_range] using card_le_card this
  have hsum : A.card + B.card ≤ k := by
    rwa [← card_union_of_disjoint hdisj]
  have hge : n ≤ A.card + B.card := by
    rw [hA, hB]
    have h2 : 2 * G.minDegree = G.minDegree + G.minDegree := Nat.two_mul _
    rw [h2] at hδ
    exact le_trans hδ (Nat.add_le_add (G.minDegree_le_degree u) (G.minDegree_le_degree v))
  have : k < n := hp.length_lt
  omega

lemma takeUntil_getVert_length {u v : V} {p : G.Walk u v} (hp : p.IsPath)
    {i : ℕ} (hi : i ≤ p.length) :
    (p.takeUntil (p.getVert i) (getVert_mem_support p hi)).length = i := by
  induction p generalizing i with
  | nil =>
    have : i = 0 := by simp at hi; exact hi
    subst i
    simp [Walk.takeUntil]
  | cons h q ih =>
    cases i with
    | zero =>
      simp [Walk.getVert_zero, Walk.takeUntil]
    | succ i =>
      have hpq : q.IsPath := Walk.IsPath.of_cons hp
      have hiq : i ≤ q.length := by simp at hi; omega
      have hne : (Walk.cons h q).getVert 0 ≠ (Walk.cons h q).getVert (i + 1) := by
        intro heq
        have := getVert_inj_of_isPath hp (Nat.zero_le _) hi heq
        omega
      simp [Walk.takeUntil, Walk.getVert]
      split_ifs with hu
      · exact (hne (by simpa [Walk.getVert_zero, Walk.getVert] using hu)).elim
      · simpa using ih hpq hiq

lemma takeUntil_getVert_eq {u v w : V} (p : G.Walk u v) (hw : w ∈ p.support) (j : ℕ)
    (hj : j ≤ (p.takeUntil w hw).length) :
    (p.takeUntil w hw).getVert j = p.getVert j := by
  have hspec := p.take_spec hw
  by_cases hlt : j < (p.takeUntil w hw).length
  · have hgv := Walk.getVert_append (p.takeUntil w hw) (p.dropUntil w hw) j
    rw [hspec] at hgv
    simp [hlt] at hgv
    exact hgv.symm
  · have hj' : j = (p.takeUntil w hw).length := le_antisymm hj (le_of_not_lt hlt)
    subst hj'
    have hgv := Walk.getVert_append (p.takeUntil w hw) (p.dropUntil w hw)
      (p.takeUntil w hw).length
    rw [hspec] at hgv
    simp [lt_irrefl, Nat.sub_self, Walk.getVert_zero, Walk.getVert_length] at hgv ⊢
    exact hgv.symm

lemma mem_support_takeUntil_getVert {u v : V} {p : G.Walk u v} (hp : p.IsPath)
    {i : ℕ} (hi : i ≤ p.length) {x : V} :
    x ∈ (p.takeUntil (p.getVert i) (getVert_mem_support p hi)).support ↔
      ∃ j ≤ i, p.getVert j = x := by
  set hw := getVert_mem_support p hi
  set P := p.takeUntil (p.getVert i) hw
  have hlenP : P.length = i := takeUntil_getVert_length hp hi
  constructor
  · intro hx
    obtain ⟨j, rfl, hj⟩ := Walk.mem_support_iff_exists_getVert.mp hx
    refine ⟨j, by omega, (takeUntil_getVert_eq p hw j hj).symm⟩
  · rintro ⟨j, hji, rfl⟩
    have hjle : j ≤ P.length := by omega
    rw [← takeUntil_getVert_eq p hw j hjle]
    exact getVert_mem_support P hjle

lemma mem_support_dropUntil_getVert {u v : V} {p : G.Walk u v} (hp : p.IsPath)
    {i : ℕ} (hi : i ≤ p.length) {x : V} :
    x ∈ (p.dropUntil (p.getVert i) (getVert_mem_support p hi)).support ↔
      ∃ j, i ≤ j ∧ j ≤ p.length ∧ p.getVert j = x := by
  set hw := getVert_mem_support p hi
  set P := p.takeUntil (p.getVert i) hw
  set Q := p.dropUntil (p.getVert i) hw
  have hspec : P.append Q = p := p.take_spec hw
  have hlenP : P.length = i := takeUntil_getVert_length hp hi
  have hlenPQ : P.length + Q.length = p.length := by
    simpa [Walk.length_append] using congr_arg Walk.length hspec
  constructor
  · intro hx
    obtain ⟨t, rfl, ht⟩ := Walk.mem_support_iff_exists_getVert.mp hx
    refine ⟨t + i, Nat.le_add_left _ _, ?_, ?_⟩
    · omega
    · have hgv := Walk.getVert_append P Q (t + P.length)
      have hnlt : ¬ t + P.length < P.length := by omega
      simp [hspec, hnlt, hlenP] at hgv
      exact hgv
  · rintro ⟨j, hij, hjlen, rfl⟩
    have hgv := Walk.getVert_append P Q j
    rw [hspec] at hgv
    have hnlt : ¬ j < P.length := by omega
    rw [if_neg hnlt] at hgv
    have hj' : j - P.length ≤ Q.length := by omega
    rw [hgv]
    exact getVert_mem_support Q hj'

/-- Path from `xᵢ₊₁` to `u` obtained by jumping `xᵢ — v` and reversing the prefix. -/
def closePath {u v : V} (p : G.Walk u v) (i : ℕ) (hi : i < p.length)
    (hvi : G.Adj v (p.getVert i)) :
    G.Walk (p.getVert (i + 1)) u :=
  (p.dropUntil (p.getVert (i + 1)) (getVert_mem_support p (Nat.succ_le_of_lt hi))).append
    (Walk.cons hvi
      (p.takeUntil (p.getVert i) (getVert_mem_support p (le_of_lt hi))).reverse)

lemma closePath_isPath {u v : V} {p : G.Walk u v} (hp : p.IsPath) {i : ℕ}
    (hi : i < p.length) (hvi : G.Adj v (p.getVert i)) :
    (closePath p i hi hvi).IsPath := by
  unfold closePath
  apply Walk.IsPath.mk'
  rw [Walk.support_append, Walk.support_cons, List.tail_cons]
  refine (List.nodup_append).2 ⟨?_, ?_, ?_⟩
  · exact (hp.dropUntil _).support_nodup
  · exact (hp.takeUntil _).reverse.support_nodup
  · intro x hxS hxP
    rw [Walk.support_reverse] at hxP
    have hxP' : x ∈ (p.takeUntil (p.getVert i) (getVert_mem_support p (le_of_lt hi))).support := by
      simpa using List.mem_reverse.mp hxP
    rw [mem_support_dropUntil_getVert hp (Nat.succ_le_of_lt hi)] at hxS
    rw [mem_support_takeUntil_getVert hp (le_of_lt hi)] at hxP'
    obtain ⟨j, hij, hjlen, hjx⟩ := hxS
    obtain ⟨j', hj'i, hj'x⟩ := hxP'
    have : j = j' := getVert_inj_of_isPath hp hjlen (le_trans hj'i (le_of_lt hi))
      (hjx.trans hj'x.symm)
    omega

lemma closePath_not_mem_edges {u v : V} {p : G.Walk u v} (hp : p.IsPath) {i : ℕ}
    (hi : i < p.length) (hvi : G.Adj v (p.getVert i))
    (hui : G.Adj u (p.getVert (i + 1))) (hlen : 2 ≤ p.length) :
    s(u, p.getVert (i + 1)) ∉ (closePath p i hi hvi).edges := by
  intro he
  unfold closePath at he
  rw [Walk.edges_append, List.mem_append, Walk.edges_cons, List.mem_cons] at he
  rcases he with h1 | h2 | h3
  · have huS : u ∈ (p.dropUntil (p.getVert (i + 1))
        (getVert_mem_support p (Nat.succ_le_of_lt hi))).support :=
      Walk.fst_mem_support_of_mem_edges _ h1
    obtain ⟨j, hij, hjlen, hj⟩ :=
      (mem_support_dropUntil_getVert hp (Nat.succ_le_of_lt hi)).mp huS
    have : j = 0 := getVert_inj_of_isPath hp hjlen (Nat.zero_le _)
      (by simpa [Walk.getVert_zero] using hj)
    omega
  · rw [Sym2.eq_iff] at h2
    rcases h2 with h | h
    · obtain ⟨_huv, hii⟩ := h
      have : i + 1 = i := getVert_inj_of_isPath hp (Nat.succ_le_of_lt hi) (le_of_lt hi) hii
      omega
    · obtain ⟨hui', hiv⟩ := h
      have hi0 : i = 0 := getVert_inj_of_isPath hp (le_of_lt hi) (Nat.zero_le _)
        (hui'.symm.trans (Walk.getVert_zero p).symm)
      have hilen : i + 1 = p.length := getVert_inj_of_isPath hp
        (Nat.succ_le_of_lt hi) (Nat.le_refl _) (hiv.trans (Walk.getVert_length p).symm)
      omega
  · have hxi1 : p.getVert (i + 1) ∈
        (p.takeUntil (p.getVert i) (getVert_mem_support p (le_of_lt hi))).reverse.support :=
      Walk.snd_mem_support_of_mem_edges _ h3
    have hxi1' : p.getVert (i + 1) ∈
        (p.takeUntil (p.getVert i) (getVert_mem_support p (le_of_lt hi))).support := by
      simpa [Walk.support_reverse] using hxi1
    obtain ⟨j, hji, hj⟩ :=
      (mem_support_takeUntil_getVert hp (le_of_lt hi)).mp hxi1'
    have : j = i + 1 := getVert_inj_of_isPath hp (le_trans hji (le_of_lt hi))
      (Nat.succ_le_of_lt hi) hj
    omega

lemma closePath_cons_isCycle {u v : V} {p : G.Walk u v} (hp : p.IsPath) {i : ℕ}
    (hi : i < p.length) (hvi : G.Adj v (p.getVert i))
    (hui : G.Adj u (p.getVert (i + 1))) (hlen : 2 ≤ p.length) :
    (Walk.cons hui (closePath p i hi hvi)).IsCycle :=
  (Walk.cons_isCycle_iff (closePath p i hi hvi) hui).2
    ⟨closePath_isPath hp hi hvi, closePath_not_mem_edges hp hi hvi hui hlen⟩

lemma closePath_length {u v : V} {p : G.Walk u v} (hp : p.IsPath) {i : ℕ}
    (hi : i < p.length) (hvi : G.Adj v (p.getVert i)) :
    (closePath p i hi hvi).length = p.length := by
  unfold closePath
  simp only [Walk.length_append, Walk.length_cons, Walk.length_reverse]
  have hlen_i := takeUntil_getVert_length hp (le_of_lt hi)
  have hlen_i1 := takeUntil_getVert_length hp (Nat.succ_le_of_lt hi)
  have hsum := congr_arg Walk.length
    (p.take_spec (getVert_mem_support p (Nat.succ_le_of_lt hi)))
  rw [Walk.length_append, hlen_i1] at hsum
  simp [Nat.succ_eq_add_one, hlen_i, add_comm, add_left_comm, add_assoc] at hsum ⊢
  exact hsum

lemma closePath_mem_support {u v : V} {p : G.Walk u v} (hp : p.IsPath) {i : ℕ}
    (hi : i < p.length) (hvi : G.Adj v (p.getVert i)) {x : V} :
    x ∈ (closePath p i hi hvi).support ↔ x ∈ p.support := by
  unfold closePath
  constructor
  · intro hx
    rw [Walk.mem_support_append_iff, Walk.support_cons, List.mem_cons,
      Walk.support_reverse] at hx
    rcases hx with h | rfl | h
    · exact Walk.support_dropUntil_subset _ _ h
    · exact Walk.end_mem_support p
    · exact Walk.support_takeUntil_subset _ _
        (List.mem_reverse.mp (by simpa using h))
  · intro hx
    obtain ⟨j, rfl, hjle⟩ := Walk.mem_support_iff_exists_getVert.mp hx
    rw [Walk.mem_support_append_iff, Walk.support_cons, List.mem_cons,
      Walk.support_reverse]
    by_cases hji : j ≤ i
    · exact Or.inr <| Or.inr <| List.mem_reverse.mpr
        ((mem_support_takeUntil_getVert hp (le_of_lt hi)).mpr ⟨j, hji, rfl⟩)
    · exact Or.inl
        ((mem_support_dropUntil_getVert hp (Nat.succ_le_of_lt hi)).mpr
          ⟨j, Nat.succ_le_of_lt (lt_of_not_ge hji), hjle, rfl⟩)

lemma cons_closePath_mem_support {u v : V} {p : G.Walk u v} (hp : p.IsPath) {i : ℕ}
    (hi : i < p.length) (hvi : G.Adj v (p.getVert i))
    (hui : G.Adj u (p.getVert (i + 1))) {x : V} :
    x ∈ (Walk.cons hui (closePath p i hi hvi)).support ↔ x ∈ p.support := by
  simp only [Walk.support_cons, List.mem_cons, closePath_mem_support hp hi hvi]
  constructor
  · intro h; rcases h with rfl | h
    · exact Walk.start_mem_support p
    · exact h
  · exact Or.inr

lemma mem_support_rotate {u v : V} (c : G.Walk v v) (h : u ∈ c.support) {x : V} :
    x ∈ (c.rotate h).support ↔ x ∈ c.support := by
  simp only [Walk.rotate, Walk.mem_support_append_iff]
  rw [or_comm, ← Walk.mem_support_append_iff, c.take_spec h]

lemma length_rotate {u v : V} (c : G.Walk v v) (h : u ∈ c.support) :
    (c.rotate h).length = c.length := by
  simp only [Walk.rotate, Walk.length_append]
  have := congr_arg Walk.length (c.take_spec h)
  rw [Walk.length_append, add_comm] at this
  exact this

lemma exists_adj_off_support (hconn : G.Connected) {u v w : V} {p : G.Walk u v}
    (hw : w ∉ p.support) :
    ∃ x y : V, x ∈ p.support ∧ y ∉ p.support ∧ G.Adj x y := by
  obtain ⟨q⟩ := hconn u w
  obtain ⟨d, _, hfst, hsnd⟩ :=
    q.exists_boundary_dart {x | x ∈ p.support} (Walk.start_mem_support p) hw
  exact ⟨d.fst, d.snd, hfst, hsnd, d.adj⟩

lemma longest_path_support_univ {u v : V} {p : G.Walk u v}
    (hn : 3 ≤ n) (hδ : n ≤ 2 * G.minDegree) (hp : p.IsPath)
    (hmax : ∀ {u' v' : V} (q : G.Walk u' v'), q.IsPath → q.length ≤ p.length)
    (hconn : G.Connected) : ∀ w : V, w ∈ p.support := by
  intro w
  by_contra hw
  obtain ⟨i, hi, hvi, hui⟩ := exists_cycle_closing hp hmax hδ
  have hlen2 := two_le_length_of_dirac_longest hn hδ hp hmax
  have hcyc := closePath_cons_isCycle hp hi hvi hui hlen2
  let C := Walk.cons hui (closePath p i hi hvi)
  obtain ⟨x, y, hx, hy, hadj⟩ := exists_adj_off_support hconn hw
  have hxC : x ∈ C.support := (cons_closePath_mem_support hp hi hvi hui).2 hx
  have hyC : y ∉ C.support := fun h => hy ((cons_closePath_mem_support hp hi hvi hui).1 h)
  let C' := C.rotate hxC
  have hC'cyc : C'.IsCycle := hcyc.rotate hxC
  cases hC' : C' with
  | nil =>
    rw [hC'] at hC'cyc
    exact Walk.IsCycle.not_of_nil hC'cyc
  | cons h q =>
    have hq : q.IsPath := ((Walk.cons_isCycle_iff q h).1 (hC' ▸ hC'cyc)).1
    have hyq : y ∉ q.reverse.support := by
      intro hym
      have hyq' : y ∈ q.support := by
        simpa [Walk.support_reverse] using hym
      have : y ∈ C'.support := by
        rw [hC', Walk.support_cons]
        exact List.mem_cons_of_mem _ hyq'
      exact hyC ((mem_support_rotate C hxC).mp this)
    have hp' : (Walk.cons hadj.symm q.reverse).IsPath := hq.reverse.cons hyq
    have hlenC : C.length = p.length + 1 := by
      simp only [C, Walk.length_cons, closePath_length hp hi hvi]
    have hlenC' : C'.length = C.length := length_rotate C hxC
    have hlenq : q.length + 1 = C'.length := by simp [hC']
    have := hmax (Walk.cons hadj.symm q.reverse) hp'
    simp only [Walk.length_cons, Walk.length_reverse] at this
    omega

/-- Dirac's theorem: `n ≥ 3` and `δ ≥ n/2` imply a Hamiltonian **cycle**. -/
theorem dirac_hamiltonian (hn : 3 ≤ n) (hδ : n ≤ 2 * G.minDegree) :
    G.IsHamiltonian := by
  have hpos : 0 < n := lt_of_lt_of_le (by decide : 0 < 3) hn
  haveI hneV : Nonempty V := Fintype.card_pos_iff.mp hpos
  intro _hne
  have hconn := connected_of_dirac hn hδ
  obtain ⟨u, v, p, hp, hmax⟩ := exists_longest_path hneV
  obtain ⟨i, hi, hvi, hui⟩ := exists_cycle_closing hp hmax hδ
  have hspan := longest_path_support_univ hn hδ hp hmax hconn
  have hlen2 := two_le_length_of_dirac_longest hn hδ hp hmax
  have hcyc := closePath_cons_isCycle hp hi hvi hui hlen2
  have hlen : (Walk.cons hui (closePath p i hi hvi)).length = n := by
    simp only [Walk.length_cons, closePath_length hp hi hvi]
    have hcard : p.support.toFinset.card = n := by
      have : p.support.toFinset = univ :=
        Finset.eq_univ_of_forall fun w => List.mem_toFinset.mpr (hspan w)
      simp [this]
    have := List.toFinset_card_of_nodup hp.support_nodup
    rw [Walk.length_support] at this
    omega
  refine ⟨u, Walk.cons hui (closePath p i hi hvi),
    isHamiltonianCycle_of_cycle_length hcyc hlen⟩

end ProofLab.Dirac

