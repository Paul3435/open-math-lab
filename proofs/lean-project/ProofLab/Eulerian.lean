/-
Euler / Hierholzer: existence of Eulerian trails.

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 has `Walk.IsEulerian` and the *necessary* parity
(`IsEulerian.card_odd_degree`). This module is the existence direction.

Pin: `catalog/problems/eulerian-hierholzer/STATEMENT.md` (OPE-579 / OPE-597 / OPE-633).
Encoding: Mathlib `SimpleGraph` + `Walk.IsEulerian` / `Walk.IsCircuit`.
Zero `sorry`. Do not import `Archive.*`. Not Königsberg. Not Dirac.

Level A (OPE-579, do not re-prove): `K_1` (nil walk Eulerian) and cycles
`C_n` (`n ≥ 3`) Eulerian circuits; connectedness used. `K_2` is the
open-trail sanity check.

Level B (OPE-597, do not re-prove): Hierholzer / longest-trail existence
for connected `G` with 0 odd-degree vertices (circuit) plus the
complete-odd family. Circuit clause needs a nonempty `edgeSet` because
`Walk.IsCircuit` excludes the `K_1` nil walk (STATEMENT caveat).

Level C (OPE-633): open Eulerian trail when `card oddDeg = 2`. Encoding:
longest trail **starting at an odd-degree vertex**; Hierholzer splice of
an unused even-degree detour. **No dummy-edge.**
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

/-! ## Level C: open Eulerian trail, `card oddDeg = 2` (OPE-633)

Encoding pin: longest trail starting at an odd-degree vertex.
Hierholzer splice of a closed unused detour. No dummy-edge. -/

/-- Longest trail with a **fixed** start. Internal tool. -/
lemma exists_longest_trail_from (u : V) :
    ∃ (v : V) (p : G.Walk u v), p.IsTrail ∧
      ∀ {v' : V} (q : G.Walk u v'), q.IsTrail → q.length ≤ p.length := by
  let s : Set ℕ := {k | ∃ (v : V) (p : G.Walk u v), p.IsTrail ∧ p.length = k}
  have hsne : s.Nonempty := ⟨0, ⟨u, Walk.nil, Walk.IsTrail.nil, rfl⟩⟩
  have hsfin : s.Finite :=
    (Set.finite_lt_nat (G.edgeFinset.card + 1)).subset fun k hk => by
      obtain ⟨_, p, hp, rfl⟩ := hk
      exact Nat.lt_succ_of_le (trail_length_le_card hp)
  obtain ⟨k, hks, hkmax⟩ := Set.Finite.exists_maximal_wrt (id : ℕ → ℕ) s hsfin hsne
  obtain ⟨v, p, hp, hpk⟩ := hks
  refine ⟨v, p, hp, fun q hq => ?_⟩
  have hqmem : q.length ∈ s := ⟨_, q, hq, rfl⟩
  cases le_total q.length k with
  | inl h => simpa [hpk] using h
  | inr h =>
    have := hkmax q.length hqmem h
    simp only [id_eq] at this
    omega

lemma saturated_end_from {u v w : V} {p : G.Walk u v} (hp : p.IsTrail)
    (hmax : ∀ {v' : V} (q : G.Walk u v'), q.IsTrail → q.length ≤ p.length)
    (hw : G.Adj v w) : s(v, w) ∈ p.edges := by
  by_contra hnotin
  have hp' : (p.concat hw).IsTrail := concat_isTrail hp hnotin
  have := hmax (p.concat hw) hp'
  simp [Walk.length_concat] at this

lemma longest_from_odd_open {u v : V} {p : G.Walk u v} (hp : p.IsTrail)
    (hmax : ∀ {v' : V} (q : G.Walk u v'), q.IsTrail → q.length ≤ p.length)
    (hu : Odd (G.degree u)) : u ≠ v := by
  intro huv
  subst huv
  have hsat : ∀ w, G.Adj u w → s(u, w) ∈ p.edges := fun w hw =>
    saturated_end_from hp hmax hw
  have hcount : p.edges.countP (fun e => u ∈ e) = G.degree u :=
    countP_eq_degree_of_saturated hp hsat
  have : Even (p.edges.countP (fun e => u ∈ e)) := by
    have hparity := hp.even_countP_edges_iff u
    simpa using hparity.mpr (fun h => (h rfl).elim)
  rw [hcount] at this
  exact Nat.odd_iff_not_even.mp hu this

lemma longest_closed_of_even_from {u v : V} {p : G.Walk u v} (hp : p.IsTrail)
    (hmax : ∀ {v' : V} (q : G.Walk u v'), q.IsTrail → q.length ≤ p.length)
    (heven : ∀ x : V, Even (G.degree x)) : u = v := by
  by_contra hne
  have hsat : ∀ w, G.Adj v w → s(v, w) ∈ p.edges := fun w hw =>
    saturated_end_from hp hmax hw
  have hcount : p.edges.countP (fun e => v ∈ e) = G.degree v :=
    countP_eq_degree_of_saturated hp hsat
  have hparity := hp.even_countP_edges_iff v
  have : Even (G.degree v) := heven v
  rw [hcount] at hparity
  have : u ≠ v → v ≠ u ∧ v ≠ v := hparity.mp this
  exact (this hne).2 rfl

lemma oddDeg_toFinset_eq :
    ({ y : V | Odd (G.degree y) } : Set V).toFinset =
      univ.filter (fun y : V => Odd (G.degree y)) := by
  ext y
  simp

lemma oddDeg_filter_card (hcard : Fintype.card { y : V | Odd (G.degree y) } = 2) :
    (univ.filter (fun y : V => Odd (G.degree y))).card = 2 := by
  rw [← oddDeg_toFinset_eq, Set.toFinset_card]
  exact hcard

instance decidableRel_deleteEdges (s : Set (Sym2 V)) [DecidablePred (· ∈ s)] :
    DecidableRel (G.deleteEdges s).Adj :=
  fun a b =>
    decidable_of_iff (G.Adj a b ∧ s(a, b) ∉ s)
      (deleteEdges_adj (s := s)).symm

lemma odd_eq_of_card_two {u v x : V}
    (hcard : Fintype.card { y : V | Odd (G.degree y) } = 2)
    (hne : u ≠ v) (hu : Odd (G.degree u)) (hv : Odd (G.degree v))
    (hx : Odd (G.degree x)) : x = u ∨ x = v := by
  have hcard' := oddDeg_filter_card hcard
  rw [card_eq_two] at hcard'
  obtain ⟨a, b, hab, hs⟩ := hcard'
  have hmem : ∀ y : V, Odd (G.degree y) ↔ y = a ∨ y = b := by
    intro y
    constructor
    · intro hy
      have : y ∈ univ.filter (fun z => Odd (G.degree z)) :=
        mem_filter.mpr ⟨mem_univ y, hy⟩
      rw [hs, mem_insert, mem_singleton] at this
      exact this
    · intro hy
      have : y ∈ univ.filter (fun z => Odd (G.degree z)) := by
        rw [hs, mem_insert, mem_singleton]
        exact hy
      exact (mem_filter.mp this).2
  have hua := (hmem u).mp hu
  have hva := (hmem v).mp hv
  have hxa := (hmem x).mp hx
  rcases hua with rfl | rfl
  · rcases hva with rfl | rfl
    · exact (hne rfl).elim
    · rcases hxa with rfl | rfl <;> simp
  · rcases hva with rfl | rfl
    · rcases hxa with h | h
      · exact Or.inr h
      · exact Or.inl h
    · exact (hne rfl).elim

lemma countP_eq_card_used_neighbors {u v x : V} {p : G.Walk u v} (hp : p.IsTrail) :
    p.edges.countP (fun e => x ∈ e) =
      ((G.neighborFinset x).filter (fun w => s(x, w) ∈ p.edges)).card := by
  let used := (G.neighborFinset x).filter (fun w => s(x, w) ∈ p.edges)
  let t := (p.edges.filter (fun e => x ∈ e)).toFinset
  have hnodup : (p.edges.filter (fun e => x ∈ e)).Nodup :=
    List.Nodup.filter _ hp.edges_nodup
  have htlen : t.card = p.edges.countP (fun e => x ∈ e) := by
    rw [List.countP_eq_length_filter]
    exact List.toFinset_card_of_nodup hnodup
  rw [← htlen]
  have hinj : ((used : Set V).InjOn (fun w => (s(x, w) : Sym2 V))) := by
    intro w hw w' hw' heq
    have hadj : G.Adj x w :=
      (mem_neighborFinset G x w).mp (mem_filter.mp (by exact hw)).1
    rcases (Sym2.eq_iff).mp heq with ⟨_, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact (hadj.ne rfl).elim
  have himg : used.image (fun w => s(x, w)) = t := by
    ext e
    constructor
    · intro he
      obtain ⟨w, hw, rfl⟩ := mem_image.mp he
      obtain ⟨_, hwE⟩ := mem_filter.mp hw
      exact List.mem_toFinset.mpr <| List.mem_filter.mpr
        ⟨hwE, decide_eq_true ((Sym2.mem_iff).2 (Or.inl rfl))⟩
    · intro he
      have hf := List.mem_filter.mp (List.mem_toFinset.mp he)
      have hmemT :
          ∀ e : Sym2 V, e ∈ p.edges → x ∈ e →
            e ∈ used.image (fun w => s(x, w)) := by
        refine Sym2.ind ?_
        intro a b hab hxin
        have hadj : G.Adj a b := by
          have : s(a, b) ∈ G.edgeSet := p.edges_subset_edgeSet hab
          rwa [mem_edgeSet] at this
        simp only [Sym2.mem_iff] at hxin
        rw [mem_image]
        rcases hxin with rfl | rfl
        · refine ⟨b, ?_, rfl⟩
          exact mem_filter.mpr ⟨(mem_neighborFinset G x b).mpr hadj, hab⟩
        · refine ⟨a, ?_, ?_⟩
          · exact mem_filter.mpr
              ⟨(mem_neighborFinset G x a).mpr hadj.symm,
                by simpa [Sym2.eq_swap] using hab⟩
          · simp [Sym2.eq_swap]
      have hxin : x ∈ e := of_decide_eq_true hf.2
      exact hmemT e hf.1 hxin
  rw [← himg, card_image_of_injOn hinj]

lemma even_degree_delete_trail_edges {u v : V} {p : G.Walk u v}
    (hp : p.IsTrail) (hne : u ≠ v)
    (hu : Odd (G.degree u)) (hv : Odd (G.degree v))
    (hcard : Fintype.card { y : V | Odd (G.degree y) } = 2) (x : V) :
    Even ((G.deleteEdges {e | e ∈ p.edges}).degree x) := by
  set s : Set (Sym2 V) := {e | e ∈ p.edges}
  have hnf :
      (G.deleteEdges s).neighborFinset x =
        (G.neighborFinset x).filter (fun w => s(x, w) ∉ s) := by
    ext w
    simp [mem_neighborFinset, deleteEdges_adj, s]
  change Even ((G.deleteEdges s).neighborFinset x).card
  rw [hnf]
  have hsum := filter_card_add_filter_neg_card_eq_card
    (s := G.neighborFinset x) (fun w => s(x, w) ∈ p.edges)
  have hused :
      p.edges.countP (fun e => x ∈ e) =
        ((G.neighborFinset x).filter (fun w => s(x, w) ∈ p.edges)).card :=
    countP_eq_card_used_neighbors hp
  have hrem :
      ((G.neighborFinset x).filter (fun w => s(x, w) ∉ s)).card =
        ((G.neighborFinset x).filter (fun w => s(x, w) ∉ p.edges)).card := by
    simp [s]
  rw [hrem]
  set usedc := ((G.neighborFinset x).filter (fun w => s(x, w) ∈ p.edges)).card
  set remc := ((G.neighborFinset x).filter (fun w => s(x, w) ∉ p.edges)).card
  have hdeg : usedc + remc = G.degree x := by
    rw [← card_neighborFinset_eq_degree]
    exact hsum
  have hparity := hp.even_countP_edges_iff x
  have hiff : Even (p.edges.countP (fun e => x ∈ e)) ↔ x ≠ u ∧ x ≠ v := by
    rw [hparity]
    simp [hne]
  by_cases hxuv : x = u ∨ x = v
  · have hoddX : Odd (G.degree x) := by
      rcases hxuv with rfl | rfl <;> assumption
    have hoddU : ¬ Even (p.edges.countP (fun e => x ∈ e)) := by
      rw [hiff]
      intro ⟨hxu, hxv⟩
      rcases hxuv with rfl | rfl
      · exact hxu rfl
      · exact hxv rfl
    have hoddUsed : Odd usedc := by
      rw [← hused]
      exact Nat.odd_iff_not_even.mpr hoddU
    rw [Nat.even_iff]
    have h1 : G.degree x % 2 = 1 := Nat.odd_iff.mp hoddX
    have h2 : usedc % 2 = 1 := Nat.odd_iff.mp hoddUsed
    have h3 : (usedc + remc) % 2 = 1 := by rw [hdeg]; exact h1
    rw [Nat.add_mod, h2] at h3
    omega
  · push_neg at hxuv
    have hevenUsed : Even (p.edges.countP (fun e => x ∈ e)) := hiff.mpr hxuv
    have hevenDeg : Even (G.degree x) := by
      by_contra hnot
      have hxodd : Odd (G.degree x) := Nat.odd_iff_not_even.mpr hnot
      rcases odd_eq_of_card_two hcard hne hu hv hxodd with rfl | rfl
      · exact hxuv.1 rfl
      · exact hxuv.2 rfl
    rw [Nat.even_iff]
    have h1 : G.degree x % 2 = 0 := Nat.even_iff.mp hevenDeg
    have h2 : usedc % 2 = 0 := by
      have : Even usedc := by rwa [← hused]
      exact Nat.even_iff.mp this
    have h3 : (usedc + remc) % 2 = 0 := by rw [hdeg]; exact h1
    rw [Nat.add_mod, h2] at h3
    omega

lemma append_isTrail {u v w : V} {p : G.Walk u v} {q : G.Walk v w}
    (hp : p.IsTrail) (hq : q.IsTrail)
    (hdisj : List.Disjoint p.edges q.edges) : (p.append q).IsTrail := by
  rw [Walk.isTrail_def, Walk.edges_append]
  exact hp.edges_nodup.append hq.edges_nodup hdisj

lemma mapLe_edges {G₀ G₁ : SimpleGraph V} (h : G₀ ≤ G₁) {u v : V}
    (p : G₀.Walk u v) : (p.mapLe h).edges = p.edges := by
  induction p with
  | nil => rfl
  | cons _adj p ih =>
    simp [Walk.mapLe, Walk.edges_cons, ih]

lemma mapLe_isTrail {G₀ G₁ : SimpleGraph V} (h : G₀ ≤ G₁) {u v : V}
    {p : G₀.Walk u v} (hp : p.IsTrail) : (p.mapLe h).IsTrail := by
  rw [Walk.isTrail_def, mapLe_edges]
  exact hp.edges_nodup

lemma splice_isTrail {u v x : V} {p : G.Walk u v} {q : G.Walk x x}
    (hp : p.IsTrail) (hq : q.IsTrail) (hx : x ∈ p.support)
    (hdisj : List.Disjoint p.edges q.edges) :
    (((p.takeUntil x hx).append q).append (p.dropUntil x hx)).IsTrail := by
  have hp' : ((p.takeUntil x hx).append (p.dropUntil x hx)).IsTrail := by
    rwa [p.take_spec hx]
  have htd : List.Disjoint (p.takeUntil x hx).edges (p.dropUntil x hx).edges := by
    have := hp'.edges_nodup
    rw [Walk.edges_append] at this
    exact List.disjoint_of_nodup_append this
  have ht : (p.takeUntil x hx).IsTrail := hp.takeUntil hx
  have hd : (p.dropUntil x hx).IsTrail := hp.dropUntil hx
  have hdisj_tq : List.Disjoint (p.takeUntil x hx).edges q.edges :=
    fun e het heq => hdisj (p.edges_takeUntil_subset hx het) heq
  have h1 : ((p.takeUntil x hx).append q).IsTrail :=
    append_isTrail ht hq hdisj_tq
  have hdisj_rest :
      List.Disjoint ((p.takeUntil x hx).append q).edges (p.dropUntil x hx).edges := by
    intro e he hedrop
    rw [Walk.edges_append, List.mem_append] at he
    rcases he with het | heq
    · exact htd het hedrop
    · exact hdisj (p.edges_dropUntil_subset hx hedrop) heq
  exact append_isTrail h1 hd hdisj_rest

lemma length_splice {u v x : V} (p : G.Walk u v) (q : G.Walk x x)
    (hx : x ∈ p.support) :
    (((p.takeUntil x hx).append q).append (p.dropUntil x hx)).length =
      p.length + q.length := by
  have hspec := congr_arg Walk.length (p.take_spec hx)
  rw [Walk.length_append] at hspec
  simp only [Walk.length_append]
  omega

lemma exists_support_unused_edge {u v : V} {p : G.Walk u v}
    (hG : G.Connected) (he : ∃ e, e ∈ G.edgeSet ∧ e ∉ p.edges) :
    ∃ x w : V, x ∈ p.support ∧ G.Adj x w ∧ s(x, w) ∉ p.edges := by
  obtain ⟨e, heG, hnotin⟩ := he
  have hpair : ∀ e : Sym2 V, e ∈ G.edgeSet →
      ∃ a b : V, e = s(a, b) ∧ G.Adj a b := by
    refine Sym2.ind ?_
    intro a b hab
    exact ⟨a, b, rfl, by rwa [mem_edgeSet] at hab⟩
  obtain ⟨a, b, rfl, hadj⟩ := hpair e heG
  let S : Set V := {x | x ∈ p.support}
  have huS : u ∈ S := Walk.start_mem_support p
  by_cases haS : a ∈ S
  · exact ⟨a, b, haS, hadj, hnotin⟩
  · obtain ⟨q⟩ := hG u a
    obtain ⟨d, _hd, hdfst, hdsnd⟩ := Walk.exists_boundary_dart q S huS haS
    refine ⟨d.toProd.1, d.toProd.2, hdfst, d.adj, ?_⟩
    intro hin
    have hsnd : d.toProd.2 ∈ S :=
      mem_support_of_mem_edges hin ((Sym2.mem_iff).2 (Or.inr rfl))
    exact hdsnd hsnd

lemma isEulerian_of_longest_from_odd (hG : G.Connected) {u v : V}
    {p : G.Walk u v} (hp : p.IsTrail)
    (hmax : ∀ {v' : V} (q : G.Walk u v'), q.IsTrail → q.length ≤ p.length)
    (hu : Odd (G.degree u))
    (hcard : Fintype.card { y : V | Odd (G.degree y) } = 2) :
    u ≠ v ∧ Odd (G.degree v) ∧ p.IsEulerian := by
  have hne : u ≠ v := longest_from_odd_open hp hmax hu
  have hsatv : ∀ w, G.Adj v w → s(v, w) ∈ p.edges := fun w hw =>
    saturated_end_from hp hmax hw
  have hcountv : p.edges.countP (fun e => v ∈ e) = G.degree v :=
    countP_eq_degree_of_saturated hp hsatv
  have hv : Odd (G.degree v) := by
    have hparity := hp.even_countP_edges_iff v
    have hnot : ¬ Even (p.edges.countP (fun e => v ∈ e)) := by
      intro heven
      have := hparity.mp heven
      exact (this hne).2 rfl
    have : ¬ Even (G.degree v) := by rwa [hcountv] at hnot
    exact Nat.odd_iff_not_even.mpr this
  refine ⟨hne, hv, ?_⟩
  rw [Walk.isEulerian_iff]
  refine ⟨hp, ?_⟩
  intro e he
  by_contra hnotin
  obtain ⟨x, w, hxS, hxw, hunused⟩ :=
    exists_support_unused_edge (p := p) hG ⟨e, he, hnotin⟩
  let s : Set (Sym2 V) := {e' | e' ∈ p.edges}
  let G' := G.deleteEdges s
  have hxG' : G'.Adj x w := (deleteEdges_adj (s := s)).mpr ⟨hxw, hunused⟩
  have heven' : ∀ y : V, Even (G'.degree y) :=
    even_degree_delete_trail_edges (G := G) hp hne hu hv hcard
  obtain ⟨z, q, hq, hqmax⟩ := exists_longest_trail_from (G := G') x
  have hz : z = x :=
    (longest_closed_of_even_from (G := G') hq hqmax heven').symm
  cases hz
  have hqpos : 0 < q.length := by
    have ht : hxG'.toWalk.IsTrail := by
      simp [Adj.toWalk, Walk.isTrail_def]
    have := hqmax hxG'.toWalk ht
    simpa [Adj.toWalk] using this
  let qG : G.Walk x x := q.mapLe (G.deleteEdges_le s)
  have hqG : qG.IsTrail := mapLe_isTrail (G.deleteEdges_le s) hq
  have hedges : qG.edges = q.edges := mapLe_edges _ q
  have hdisj : List.Disjoint p.edges qG.edges := by
    intro e' hep heq
    rw [hedges] at heq
    have hem : e' ∈ G'.edgeSet := q.edges_subset_edgeSet heq
    have : e' ∈ G.edgeSet ∧ e' ∉ s := by
      simpa [G', edgeSet_deleteEdges] using hem
    exact this.2 hep
  let p' := ((p.takeUntil x hxS).append qG).append (p.dropUntil x hxS)
  have hp' : p'.IsTrail := splice_isTrail hp hqG hxS hdisj
  have hlen' : p'.length = p.length + qG.length := length_splice p qG hxS
  have hle : p'.length ≤ p.length := hmax p' hp'
  have : qG.length = q.length := Walk.length_map _ _
  omega

/-- STATEMENT trail clause. Start-at-odd longest trail; no dummy-edge. -/
theorem eulerian_hierholzer_trail (hG : G.Connected)
    (hodd : Fintype.card { v : V | Odd (G.degree v) } = 2) :
    ∃ u v : V, u ≠ v ∧ Odd (G.degree u) ∧ Odd (G.degree v) ∧
      ∃ p : G.Walk u v, p.IsEulerian := by
  haveI := hG.nonempty
  have hcard := oddDeg_filter_card hodd
  rw [card_eq_two] at hcard
  obtain ⟨u, _, _, hs⟩ := hcard
  have hu : Odd (G.degree u) := by
    have : u ∈ univ.filter (fun z => Odd (G.degree z)) := by
      rw [hs, mem_insert]
      exact Or.inl rfl
    exact (mem_filter.mp this).2
  obtain ⟨v, p, hp, hmax⟩ := exists_longest_trail_from (G := G) u
  obtain ⟨hne, hv, hEul⟩ :=
    isEulerian_of_longest_from_odd hG hp hmax hu hodd
  exact ⟨u, v, hne, hu, hv, p, hEul⟩

end ProofLab.Eulerian

