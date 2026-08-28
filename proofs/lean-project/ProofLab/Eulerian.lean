/-
Euler / Hierholzer: existence of Eulerian trails.

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 has `Walk.IsEulerian` and the *necessary* parity
(`IsEulerian.card_odd_degree`). This module is the existence direction.

Pin: `catalog/problems/eulerian-hierholzer/STATEMENT.md` (OPE-579 / OPE-597).
Encoding: Mathlib `SimpleGraph` + `Walk.IsEulerian` / `Walk.IsCircuit`.
Zero `sorry`. Do not import `Archive.*`. Not Königsberg. Not Dirac.

Level A (OPE-579, do not re-prove): `K_1` (nil walk Eulerian) and cycles
`C_n` (`n ≥ 3`) Eulerian circuits; connectedness used. `K_2` is the
open-trail sanity check.

Level B (OPE-597): Hierholzer / longest-trail existence for connected `G`
with 0 odd-degree vertices (circuit) plus the complete-odd family.
Circuit clause needs a nonempty `edgeSet` because `Walk.IsCircuit`
excludes the `K_1` nil walk (STATEMENT caveat). Open-trail ∀G (card oddDeg = 2)
is residual — Walk splice / dummy reduction did not land this heartbeat.
-/
import Mathlib.Combinatorics.SimpleGraph.Trails
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

open Finset Function SimpleGraph

namespace ProofLab.Eulerian

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Odd-degree vertex set from STATEMENT.md. -/
def oddDeg (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] : Set V :=
  { v : V | Odd (G.degree v) }

lemma concat_isPath {u v w : V} {p : G.Walk u v} (hp : p.IsPath) {h : G.Adj v w}
    (hw : w ∉ p.support) : (p.concat h).IsPath :=
  Walk.IsPath.mk' (by
    rw [Walk.support_concat]
    exact List.Nodup.concat hw hp.support_nodup)

lemma concat_isTrail {u v w : V} {p : G.Walk u v} (hp : p.IsTrail) {h : G.Adj v w}
    (he : s(v, w) ∉ p.edges) : (p.concat h).IsTrail := by
  rw [Walk.isTrail_def, Walk.edges_concat]
  exact List.Nodup.concat he hp.edges_nodup

/-! ## Cycle graph `C_n` -/

def CycleGraph (n : ℕ) : SimpleGraph (Fin n) where
  Adj i j :=
    i.val + 1 = j.val ∨ j.val + 1 = i.val ∨
      (2 ≤ n ∧ i.val + 1 = n ∧ j.val = 0) ∨
      (2 ≤ n ∧ j.val + 1 = n ∧ i.val = 0)
  symm := by
    intro i j h
    rcases h with h | h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl h))
  loopless := by
    intro i h
    rcases h with h | h | h | h
    · omega
    · omega
    · omega
    · omega

instance {n : ℕ} : DecidableRel (CycleGraph n).Adj :=
  fun i j => inferInstanceAs (Decidable
    (i.val + 1 = j.val ∨ j.val + 1 = i.val ∨
      (2 ≤ n ∧ i.val + 1 = n ∧ j.val = 0) ∨
      (2 ≤ n ∧ j.val + 1 = n ∧ i.val = 0)))

lemma zero_lt_of_one_le {n : ℕ} (hn : 1 ≤ n) : 0 < n :=
  lt_of_lt_of_le (by decide : 0 < 1) hn

lemma cycleGraph_adj_succ {n : ℕ} {i : ℕ} (hi : i < n) (hsi : i + 1 < n) :
    (CycleGraph n).Adj ⟨i, hi⟩ ⟨i + 1, hsi⟩ :=
  Or.inl rfl

lemma cycleGraph_adj_last_zero {n : ℕ} (hn : 2 ≤ n) :
    (CycleGraph n).Adj ⟨n - 1, Nat.sub_lt (zero_lt_of_one_le (le_trans (by decide : 1 ≤ 2) hn))
        (by decide)⟩ ⟨0, zero_lt_of_one_le (le_trans (by decide : 1 ≤ 2) hn)⟩ :=
  Or.inr (Or.inr (Or.inl ⟨hn, Nat.sub_add_cancel (zero_lt_of_one_le (le_trans (by decide : 1 ≤ 2) hn)), rfl⟩))

lemma eulerian_nil_of_edgeless {u : V} (hE : G.edgeSet = ∅) :
    (Walk.nil : G.Walk u u).IsEulerian := by
  intro e he
  rw [hE] at he
  exact False.elim he

lemma cycleGraph_one_not_adj (i j : Fin 1) : ¬ (CycleGraph 1).Adj i j := by
  intro h
  rcases h with h | h | h | h
  · have : i.val = 0 := Nat.lt_one_iff.mp i.isLt
    have : j.val = 0 := Nat.lt_one_iff.mp j.isLt
    omega
  · have : i.val = 0 := Nat.lt_one_iff.mp i.isLt
    have : j.val = 0 := Nat.lt_one_iff.mp j.isLt
    omega
  · omega
  · omega

lemma cycleGraph_one_eq_bot : CycleGraph 1 = ⊥ := by
  ext i j
  constructor
  · intro h
    exact (cycleGraph_one_not_adj i j h).elim
  · intro h
    exact (bot_adj i j).mp h |>.elim

lemma cycleGraph_connected_one : (CycleGraph 1).Connected where
  preconnected := fun a b => by
    have ha : a = ⟨0, by decide⟩ := Fin.ext (Nat.lt_one_iff.mp a.isLt)
    have hb : b = ⟨0, by decide⟩ := Fin.ext (Nat.lt_one_iff.mp b.isLt)
    subst ha; subst hb
    exact ⟨Walk.nil⟩

lemma cycleGraph_one_degree (v : Fin 1) : (CycleGraph 1).degree v = 0 := by
  change ((CycleGraph 1).neighborFinset v).card = 0
  apply card_eq_zero.mpr
  ext x
  simp [mem_neighborFinset, cycleGraph_one_not_adj]

theorem eulerian_k1 :
    (CycleGraph 1).Connected ∧
      Fintype.card { v : Fin 1 | Odd ((CycleGraph 1).degree v) } = 0 ∧
      ∃ u : Fin 1, ∃ p : (CycleGraph 1).Walk u u, p.IsEulerian := by
  refine ⟨cycleGraph_connected_one, ?_, ⟨⟨0, by decide⟩, Walk.nil, ?_⟩⟩
  · apply Fintype.card_eq_zero_iff.mpr
    refine ⟨fun ⟨v, hv⟩ => ?_⟩
    have : Odd ((CycleGraph 1).degree v) := hv
    rw [cycleGraph_one_degree] at this
    exact Nat.odd_iff_not_even.mp this even_zero
  · have : (CycleGraph 1).edgeSet = ∅ := by
      rw [cycleGraph_one_eq_bot, edgeSet_bot]
    exact eulerian_nil_of_edgeless this

/-- Prefix path `0 — 1 — … — k` together with its consecutive edges. -/
lemma exists_cycle_prefix {n : ℕ} (hn : 1 ≤ n) :
    ∀ (k : ℕ) (hk : k < n),
      ∃ p : (CycleGraph n).Walk ⟨0, zero_lt_of_one_le hn⟩ ⟨k, hk⟩,
        p.IsPath ∧ p.length = k ∧
          (∀ x ∈ p.support, x.val ≤ k) ∧
          (∀ e ∈ p.edges, ∃ u v : Fin n, e = s(u, v) ∧ u.val + 1 = v.val ∧ v.val ≤ k) ∧
          (∀ (i : ℕ) (hi : i < k) (hsi : i + 1 < n),
            s((⟨i, Nat.lt_trans hi hk⟩ : Fin n), ⟨i + 1, hsi⟩) ∈ p.edges) := by
  intro k hk
  induction k with
  | zero =>
    refine ⟨Walk.nil.copy rfl (Fin.ext rfl), ?_, by simp, ?_, ?_, ?_⟩
    · exact (Walk.isPath_copy _ _ _).mpr Walk.IsPath.nil
    · intro x hx
      simp only [Walk.support_copy, Walk.support_nil, List.mem_singleton] at hx
      subst x
      simp
    · intro e he
      simp [Walk.edges_copy, Walk.edges_nil] at he
    · intro i hi hsi
      exact (Nat.not_lt_zero _ hi).elim
  | succ k ih =>
    have hk' : k < n := Nat.lt_of_succ_lt hk
    obtain ⟨p, hp, hlen, hge, hedges, hmem⟩ := ih hk'
    have hadj : (CycleGraph n).Adj ⟨k, hk'⟩ ⟨k + 1, hk⟩ := cycleGraph_adj_succ hk' hk
    refine ⟨p.concat hadj, concat_isPath (V := Fin n) (G := CycleGraph n) hp ?_, ?_, ?_, ?_, ?_⟩
    · intro hmem'
      have : k + 1 ≤ k := by simpa using hge _ hmem'
      omega
    · simp [hlen]
    · intro x hx
      rw [Walk.support_concat, List.concat_eq_append, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact Nat.le_succ_of_le (hge x hx)
      · exact le_rfl
    · intro e he
      rw [Walk.edges_concat, List.concat_eq_append, List.mem_append, List.mem_singleton] at he
      rcases he with he | rfl
      · obtain ⟨u, v, rfl, hcons, hv⟩ := hedges e he
        exact ⟨u, v, rfl, hcons, Nat.le_succ_of_le hv⟩
      · exact ⟨⟨k, hk'⟩, ⟨k + 1, hk⟩, rfl, rfl, le_rfl⟩
    · intro i hi hsi
      rw [Walk.edges_concat, List.concat_eq_append, List.mem_append, List.mem_singleton]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
      · exact Or.inl (hmem i hlt hsi)
      · exact Or.inr rfl

lemma cycleGraph_reachable_zero {n : ℕ} (hn : 1 ≤ n) (k : Fin n) :
    (CycleGraph n).Reachable ⟨0, zero_lt_of_one_le hn⟩ k := by
  obtain ⟨p, _, _, _, _, _⟩ := exists_cycle_prefix hn k.val k.isLt
  exact ⟨p.copy rfl (Fin.eq_mk_iff_val_eq.mpr rfl).symm⟩

/-- Connectedness is load-bearing (STATEMENT landmine 1). -/
lemma cycleGraph_connected {n : ℕ} (hn : 1 ≤ n) : (CycleGraph n).Connected := by
  haveI : Nonempty (Fin n) := ⟨⟨0, zero_lt_of_one_le hn⟩⟩
  exact ⟨fun a b =>
    (cycleGraph_reachable_zero hn a).symm.trans (cycleGraph_reachable_zero hn b)⟩

lemma exists_cycle_circuit {n : ℕ} (hn : 3 ≤ n) :
    ∃ p : (CycleGraph n).Walk ⟨0, zero_lt_of_one_le (le_trans (by decide : 1 ≤ 3) hn)⟩
        ⟨0, zero_lt_of_one_le (le_trans (by decide : 1 ≤ 3) hn)⟩,
      p.IsCircuit ∧ p.IsEulerian := by
  have hn1 : 1 ≤ n := le_trans (by decide : 1 ≤ 3) hn
  have hn2 : 2 ≤ n := le_trans (by decide : 2 ≤ 3) hn
  have hk : n - 1 < n := Nat.sub_lt (zero_lt_of_one_le hn1) (by decide)
  obtain ⟨p, hp, hlen, _hge, hedges, hmem⟩ := exists_cycle_prefix hn1 (n - 1) hk
  have hadj := cycleGraph_adj_last_zero hn2
  have he : s((⟨n - 1, hk⟩ : Fin n),
      (⟨0, zero_lt_of_one_le hn1⟩ : Fin n)) ∉ p.edges := by
    intro hmem'
    obtain ⟨u, v, heq, hcons, hv⟩ := hedges _ hmem'
    have hsym : s((⟨n - 1, hk⟩ : Fin n), (⟨0, zero_lt_of_one_le hn1⟩ : Fin n)) = s(u, v) := heq
    rw [Sym2.eq_iff] at hsym
    rcases hsym with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp at hcons
    · simp at hcons
      omega
  have htrail : (p.concat hadj).IsTrail :=
    concat_isTrail (V := Fin n) (G := CycleGraph n) hp.isTrail he
  have hlen' : (p.concat hadj).length = n := by
    simp [Walk.length_concat, hlen]
    omega
  have hne : p.concat hadj ≠ Walk.nil := by
    intro hnil
    have : (p.concat hadj).length = 0 := by simp [hnil]
    omega
  refine ⟨p.concat hadj, ⟨htrail, hne⟩, ?_⟩
  apply htrail.isEulerian_of_forall_mem
  intro e hee
  have : ∃ u v : Fin n, e = s(u, v) ∧ (CycleGraph n).Adj u v := by
    revert e
    refine Sym2.ind ?_
    intro u v huv
    exact ⟨u, v, rfl, by rwa [mem_edgeSet] at huv⟩
  obtain ⟨u, v, rfl, hadjuv⟩ := this
  have hin : s(u, v) ∈ (p.concat hadj).edges := by
    rw [Walk.edges_concat, List.concat_eq_append, List.mem_append, List.mem_singleton]
    rcases hadjuv with h | h | h | h
    · -- consecutive u → v with v.val = u.val + 1, so this is a prefix edge
      have hu : u.val < n - 1 := by omega
      have hsi : u.val + 1 < n := by omega
      left
      have := hmem u.val hu hsi
      -- this is s(⟨u.val⟩, ⟨u.val+1⟩); need s(u, v)
      have hu' : (⟨u.val, Nat.lt_trans hu hk⟩ : Fin n) = u := Fin.ext rfl
      have hv' : (⟨u.val + 1, hsi⟩ : Fin n) = v := Fin.ext h
      simpa [hu', hv'] using this
    · -- consecutive v → u
      have hv : v.val < n - 1 := by omega
      have hsi : v.val + 1 < n := by omega
      left
      have := hmem v.val hv hsi
      have hv' : (⟨v.val, Nat.lt_trans hv hk⟩ : Fin n) = v := Fin.ext rfl
      have hu' : (⟨v.val + 1, hsi⟩ : Fin n) = u := Fin.ext h
      simpa [hv', hu', Sym2.eq_swap] using this
    · -- wrap u = n-1, v = 0
      obtain ⟨_, hu1, hv0⟩ := h
      right
      have hu : u = ⟨n - 1, hk⟩ := Fin.ext <| by
        apply Nat.succ_injective
        rw [Nat.succ_eq_add_one, hu1, Nat.succ_eq_add_one, Nat.sub_add_cancel (zero_lt_of_one_le hn1)]
      have hv : v = ⟨0, zero_lt_of_one_le hn1⟩ := Fin.ext hv0
      simp [hu, hv]
    · -- wrap v = n-1, u = 0
      obtain ⟨_, hv1, hu0⟩ := h
      right
      have hv : v = ⟨n - 1, hk⟩ := Fin.ext <| by
        apply Nat.succ_injective
        rw [Nat.succ_eq_add_one, hv1, Nat.succ_eq_add_one, Nat.sub_add_cancel (zero_lt_of_one_le hn1)]
      have hu : u = ⟨0, zero_lt_of_one_le hn1⟩ := Fin.ext hu0
      simp [hu, hv, Sym2.eq_swap]
  exact hin

/-- `C_n` (`n ≥ 3`): connected Eulerian circuit. Odd-degree set is empty
because the circuit is Eulerian (Mathlib necessary direction). -/
theorem eulerian_cycle {n : ℕ} (hn : 3 ≤ n) :
    (CycleGraph n).Connected ∧
      Fintype.card { v : Fin n | Odd ((CycleGraph n).degree v) } = 0 ∧
      ∃ u : Fin n, ∃ p : (CycleGraph n).Walk u u, p.IsEulerian ∧ p.IsCircuit := by
  obtain ⟨p, hc, he⟩ := exists_cycle_circuit hn
  refine ⟨cycleGraph_connected (le_trans (by decide : 1 ≤ 3) hn), ?_,
    ⟨⟨0, zero_lt_of_one_le (le_trans (by decide : 1 ≤ 3) hn)⟩, p, he, hc⟩⟩
  apply Fintype.card_eq_zero_iff.mpr
  refine ⟨fun ⟨x, hx⟩ => ?_⟩
  have : Even ((CycleGraph n).degree x) := by
    rw [he.even_degree_iff]
    intro hne
    exact (hne rfl).elim
  exact Nat.odd_iff_not_even.mp hx this

/-! ### Level A: `K_2` open Eulerian trail -/

lemma cycleGraph_two_adj : (CycleGraph 2).Adj ⟨0, by decide⟩ ⟨1, by decide⟩ :=
  cycleGraph_adj_succ (by decide : 0 < 2) (by decide : 1 < 2)

theorem eulerian_k2 :
    (CycleGraph 2).Connected ∧
      ∃ u v : Fin 2, u ≠ v ∧
        ∃ p : (CycleGraph 2).Walk u v, p.IsEulerian := by
  refine ⟨cycleGraph_connected (by decide : 1 ≤ 2),
    ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide, ⟨cycleGraph_two_adj.toWalk, ?_⟩⟩⟩
  intro e he
  have : e = s((⟨0, by decide⟩ : Fin 2), ⟨1, by decide⟩) := by
    revert e
    refine Sym2.ind ?_
    intro a b hab
    have hadj : (CycleGraph 2).Adj a b := by
      rwa [mem_edgeSet] at hab
    fin_cases a <;> fin_cases b <;> simp [CycleGraph] at hadj ⊢
  subst this
  simp [Adj.toWalk, Walk.edges_cons, Walk.edges_nil]

/-! ## Level B: Hierholzer / longest trail (OPE-597) -/

lemma trail_length_le_card {u v : V} {p : G.Walk u v} (hp : p.IsTrail) :
    p.length ≤ G.edgeFinset.card := by
  have hsub : p.edges.toFinset ⊆ G.edgeFinset := by
    intro e he
    exact mem_edgeFinset.mpr (p.edges_subset_edgeSet (List.mem_toFinset.mp he))
  have hcard : p.edges.toFinset.card = p.edges.length :=
    List.toFinset_card_of_nodup hp.edges_nodup
  rw [← Walk.length_edges p]
  exact hcard ▸ card_le_card hsub

/-- A trail of globally maximal length. Internal tool. -/
lemma exists_longest_trail (hV : Nonempty V) :
    ∃ (u v : V) (p : G.Walk u v), p.IsTrail ∧
      ∀ {u' v' : V} (q : G.Walk u' v'), q.IsTrail → q.length ≤ p.length := by
  let s : Set ℕ := {k | ∃ (u v : V) (p : G.Walk u v), p.IsTrail ∧ p.length = k}
  have hsne : s.Nonempty := by
    obtain ⟨x⟩ := hV
    exact ⟨0, ⟨x, x, Walk.nil, Walk.IsTrail.nil, rfl⟩⟩
  have hsfin : s.Finite :=
    (Set.finite_lt_nat (G.edgeFinset.card + 1)).subset fun k hk => by
      obtain ⟨_, _, p, hp, rfl⟩ := hk
      exact Nat.lt_succ_of_le (trail_length_le_card hp)
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

lemma saturated_end {u v w : V} {p : G.Walk u v} (hp : p.IsTrail)
    (hmax : ∀ {u' v' : V} (q : G.Walk u' v'), q.IsTrail → q.length ≤ p.length)
    (hw : G.Adj v w) : s(v, w) ∈ p.edges := by
  by_contra hnotin
  have hp' : (p.concat hw).IsTrail := concat_isTrail hp hnotin
  have := hmax (p.concat hw) hp'
  simp [Walk.length_concat] at this

lemma saturated_start {u v w : V} {p : G.Walk u v} (hp : p.IsTrail)
    (hmax : ∀ {u' v' : V} (q : G.Walk u' v'), q.IsTrail → q.length ≤ p.length)
    (hw : G.Adj u w) : s(u, w) ∈ p.edges := by
  have hrev : p.reverse.IsTrail := Walk.IsTrail.reverse p hp
  have hmax' : ∀ {u' v' : V} (q : G.Walk u' v'), q.IsTrail → q.length ≤ p.reverse.length := by
    intro u' v' q hq
    simpa [Walk.length_reverse] using hmax q hq
  simpa [Walk.edges_reverse, List.mem_reverse, Sym2.eq_swap] using
    saturated_end (w := w) hrev hmax' hw

lemma mem_support_of_mem_edges {u v x : V} :
    ∀ {p : G.Walk u v} {e : Sym2 V}, e ∈ p.edges → x ∈ e → x ∈ p.support
  | Walk.nil, e, he, _ => by simp at he
  | Walk.cons h p, e, he, hx => by
    rw [Walk.edges_cons, List.mem_cons] at he
    rw [Walk.support_cons, List.mem_cons]
    rcases he with he | he
    · subst e
      simp only [Sym2.mem_iff] at hx
      rcases hx with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Walk.start_mem_support p)
    · exact Or.inr (mem_support_of_mem_edges he hx)

lemma countP_eq_degree_of_saturated {u v x : V} {p : G.Walk u v}
    (hp : p.IsTrail)
    (hsat : ∀ w, G.Adj x w → s(x, w) ∈ p.edges) :
    p.edges.countP (fun e => x ∈ e) = G.degree x := by
  let t := (p.edges.filter (fun e => x ∈ e)).toFinset
  have hnodup : (p.edges.filter (fun e => x ∈ e)).Nodup :=
    List.Nodup.filter _ hp.edges_nodup
  have htlen : t.card = p.edges.countP (fun e => x ∈ e) := by
    rw [List.countP_eq_length_filter]
    exact List.toFinset_card_of_nodup hnodup
  apply le_antisymm
  · have hsub : t ⊆ G.incidenceFinset x := by
      intro e he
      have hf := List.mem_filter.mp (List.mem_toFinset.mp he)
      simp only [mem_incidenceFinset, mem_incidenceSet]
      exact ⟨p.edges_subset_edgeSet hf.1, of_decide_eq_true hf.2⟩
    rw [← htlen, ← card_incidenceFinset_eq_degree]
    exact card_le_card hsub
  · have hf : ∀ w ∈ G.neighborFinset x, s(x, w) ∈ t := by
      intro w hw
      have hadj : G.Adj x w := (mem_neighborFinset G x w).mp hw
      have he : s(x, w) ∈ p.edges := hsat w hadj
      exact List.mem_toFinset.mpr <| List.mem_filter.mpr
        ⟨he, decide_eq_true ((Sym2.mem_iff).2 (Or.inl rfl))⟩
    have hinj : (G.neighborFinset x : Set V).InjOn (fun w => (s(x, w) : Sym2 V)) := by
      intro w hw w' hw' heq
      have hadj : G.Adj x w := (mem_neighborFinset G x w).mp hw
      rcases (Sym2.eq_iff).mp heq with ⟨_, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact (hadj.ne rfl).elim
    have hle := card_le_card_of_injOn (fun w => (s(x, w) : Sym2 V)) hf hinj
    rw [← htlen, ← card_neighborFinset_eq_degree]
    exact hle

lemma length_rotate {u v : V} (c : G.Walk v v) (h : u ∈ c.support) :
    (c.rotate h).length = c.length := by
  simp only [Walk.rotate, Walk.length_append]
  have := congr_arg Walk.length (c.take_spec h)
  rw [Walk.length_append] at this
  omega

lemma even_of_oddDeg_card_zero
    (hodd : Fintype.card { v : V | Odd (G.degree v) } = 0) (x : V) :
    Even (G.degree x) := by
  by_contra hx
  have hx' : Odd (G.degree x) := Nat.odd_iff_not_even.mpr hx
  exact (Fintype.card_eq_zero_iff.mp hodd).elim ⟨x, hx'⟩

lemma longest_closed_of_even {u v : V} {p : G.Walk u v} (hp : p.IsTrail)
    (hmax : ∀ {u' v' : V} (q : G.Walk u' v'), q.IsTrail → q.length ≤ p.length)
    (heven : ∀ x : V, Even (G.degree x)) : u = v := by
  by_contra hne
  have hsat : ∀ w, G.Adj v w → s(v, w) ∈ p.edges := fun w hw =>
    saturated_end hp hmax hw
  have hcount : p.edges.countP (fun e => v ∈ e) = G.degree v :=
    countP_eq_degree_of_saturated hp hsat
  have hparity := hp.even_countP_edges_iff v
  have : Even (G.degree v) := heven v
  rw [hcount] at hparity
  have : u ≠ v → v ≠ u ∧ v ≠ v := hparity.mp this
  exact (this hne).2 rfl

lemma saturated_support_of_closed_longest {u x : V} {p : G.Walk u u}
    (hp : p.IsTrail)
    (hmax : ∀ {u' v' : V} (q : G.Walk u' v'), q.IsTrail → q.length ≤ p.length)
    (hx : x ∈ p.support) {w : V} (hw : G.Adj x w) : s(x, w) ∈ p.edges := by
  let r := p.rotate hx
  have hr : r.IsTrail := hp.rotate hx
  have hmax' : ∀ {u' v' : V} (q : G.Walk u' v'), q.IsTrail → q.length ≤ r.length := by
    intro u' v' q hq
    rw [length_rotate]
    exact hmax q hq
  have : s(x, w) ∈ r.edges := saturated_end hr hmax' hw
  exact (List.IsRotated.mem_iff (p.rotate_edges hx)).1 this

lemma isEulerian_of_closed_longest (hG : G.Connected) {u : V} {p : G.Walk u u}
    (hp : p.IsTrail)
    (hmax : ∀ {u' v' : V} (q : G.Walk u' v'), q.IsTrail → q.length ≤ p.length) :
    p.IsEulerian := by
  rw [Walk.isEulerian_iff]
  refine ⟨hp, ?_⟩
  intro e
  revert e
  refine Sym2.ind ?_
  intro a b hab
  by_contra hnotin
  let S : Set V := {x | x ∈ p.support}
  have huS : u ∈ S := Walk.start_mem_support p
  have hsat : ∀ x ∈ S, ∀ w, G.Adj x w → s(x, w) ∈ p.edges := fun x hx w hw =>
    saturated_support_of_closed_longest hp hmax hx hw
  have hadj : G.Adj a b := hab
  have haS : a ∉ S := fun ha => hnotin (hsat a ha b hadj)
  obtain ⟨q⟩ := hG u a
  obtain ⟨d, _hd, hdfst, hdsnd⟩ := Walk.exists_boundary_dart q S huS haS
  have hin : d.edge ∈ p.edges := by
    simpa [Dart.edge] using hsat d.toProd.1 hdfst d.toProd.2 d.adj
  have hsnd : d.toProd.2 ∈ S :=
    mem_support_of_mem_edges hin (by
      rw [Dart.edge, Sym2.mem_iff]
      exact Or.inr rfl)
  exact hdsnd hsnd

/-- STATEMENT circuit clause. `IsCircuit` excludes the edgeless `K_1` nil walk. -/
theorem eulerian_hierholzer_circuit (hG : G.Connected)
    (hodd : Fintype.card { v : V | Odd (G.degree v) } = 0)
    (hE : G.edgeSet.Nonempty) :
    ∃ u : V, ∃ p : G.Walk u u, p.IsEulerian ∧ p.IsCircuit := by
  haveI := hG.nonempty
  have heven : ∀ x : V, Even (G.degree x) := even_of_oddDeg_card_zero hodd
  obtain ⟨u, v, p, hp, hmax⟩ := exists_longest_trail (G := G) hG.nonempty
  have huv : u = v := longest_closed_of_even hp hmax heven
  subst huv
  have hne : p ≠ Walk.nil := by
    intro hnil
    obtain ⟨e, he⟩ := hE
    revert e
    refine Sym2.ind ?_
    intro a b hab
    have hadj : G.Adj a b := hab
    have ht : hadj.toWalk.IsTrail := by
      simp [Adj.toWalk, Walk.isTrail_def]
    have := hmax hadj.toWalk ht
    simp [hnil, Adj.toWalk] at this
  refine ⟨u, p, isEulerian_of_closed_longest hG hp hmax, ⟨hp, hne⟩⟩

/-- Second infinite family: complete graphs of odd order (`n ≥ 3`).
Corollary of `eulerian_hierholzer_circuit`; not a re-proof of `eulerian_cycle`. -/
theorem eulerian_complete_odd {n : ℕ} (hodd : Odd n) (hn : 3 ≤ n) :
    (⊤ : SimpleGraph (Fin n)).Connected ∧
      Fintype.card { v : Fin n | Odd ((⊤ : SimpleGraph (Fin n)).degree v) } = 0 ∧
      ∃ u : Fin n, ∃ p : (⊤ : SimpleGraph (Fin n)).Walk u u,
        p.IsEulerian ∧ p.IsCircuit := by
  haveI : Nonempty (Fin n) := ⟨⟨0, lt_of_lt_of_le (by decide : 0 < 3) hn⟩⟩
  have hconn : (⊤ : SimpleGraph (Fin n)).Connected := top_connected
  have hdeg : ∀ v : Fin n, (⊤ : SimpleGraph (Fin n)).degree v = n - 1 := by
    intro v
    change ((⊤ : SimpleGraph (Fin n)).neighborFinset v).card = n - 1
    have hset : (⊤ : SimpleGraph (Fin n)).neighborFinset v = univ.erase v := by
      ext w
      constructor
      · intro hw
        exact mem_erase.mpr ⟨((mem_neighborFinset _ _ _).mp hw).ne.symm, mem_univ w⟩
      · intro hw
        exact (mem_neighborFinset _ _ _).mpr
          ((top_adj _ _).mpr (mem_erase.mp hw).1.symm)
    rw [hset, card_erase_of_mem (mem_univ v), card_univ, Fintype.card_fin]
  have hodd0 : Fintype.card { v : Fin n | Odd ((⊤ : SimpleGraph (Fin n)).degree v) } = 0 := by
    apply Fintype.card_eq_zero_iff.mpr
    refine ⟨fun x => ?_⟩
    have hv : Odd ((⊤ : SimpleGraph (Fin n)).degree x.1) := x.2
    rw [hdeg] at hv
    have : Even (n - 1) := by
      cases n with
      | zero =>
        cases (Nat.not_succ_le_zero 2 hn)
      | succ k =>
        change Even k
        have : (k + 1) % 2 = 1 := Nat.odd_iff.mp hodd
        exact Nat.even_iff.mpr (by omega)
    exact Nat.odd_iff_not_even.mp hv this
  have hE : (⊤ : SimpleGraph (Fin n)).edgeSet.Nonempty := by
    refine ⟨s((⟨0, lt_of_lt_of_le (by decide : 0 < 3) hn⟩ : Fin n),
        ⟨1, lt_of_lt_of_le (by decide : 1 < 3) hn⟩), ?_⟩
    simp [mem_edgeSet, top_adj]
  obtain ⟨u, p, hEul, hC⟩ := eulerian_hierholzer_circuit hconn hodd0 hE
  exact ⟨hconn, hodd0, u, p, hEul, hC⟩

end ProofLab.Eulerian
