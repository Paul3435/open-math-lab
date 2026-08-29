/-
Brooks' theorem scaffolding: χ ≤ Δ except complete graphs and odd cycles.

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 has `Colorable` / `chromaticNumber` / `maxDegree` /
`chromaticNumber_top` / `Walk.three_le_chromaticNumber_of_odd_loop`
but ZERO `brooks` (Mathlib+Archive) and ZERO `cycleGraph`.

Pin: `catalog/problems/brooks-coloring/STATEMENT.md` (OPE-658).
Encoding: Mathlib `Colorable` + `maxDegree` + `⊤`. Odd-cycle pin is the
ProofLab predicate `IsOddCycle` (connected + odd `card V` + 2-regular).
Do **not** invent `cycleGraph` as a Mathlib-gap claim.
Zero `sorry`. Do not import `Archive.*`.
This is **not** greedy (`χ ≤ Δ+1` always). Reuse
`ProofLab.GreedyChromatic.greedy_colorable`; do not re-prove Δ+1.
This is **not** Vizing / 4CT / 5CT / list-colouring Brooks.

Level A (OPE-651 / PR #58): exception families (`⊤` has `χ = Δ+1`;
odd cycle has `χ = 3 = Δ+1`) + greedy lemma by dependence. Zero sorry.
Level B (OPE-658): Diestel first family — connected `Δ ≤ 2`, not `⊤`,
not `IsOddCycle` ⇒ `Colorable maxDegree`. Named: even cycles along the
Hierholzer circuit; paths by deleting a degree-1 vertex. Namesake
`brooks_colorable` residual on Δ-regular Δ ≥ 3 (Kempe / Lovász sink).
Do **not** `sorry` the namesake.
-/
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.ConcreteColorings
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Trails
import Mathlib.Tactic
import ProofLab.Eulerian
import ProofLab.GreedyChromatic

open Finset Function SimpleGraph

noncomputable section

namespace ProofLab.Brooks

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## Odd-cycle pin (no `cycleGraph`) -/

/-- Connected, odd order, 2-regular. Equivalent (not a second theorem):
Hamiltonian cycle whose edge-set is `G.edgeSet`, of odd length. -/
def IsOddCycle (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  G.Connected ∧ Odd (Fintype.card V) ∧ ∀ v : V, G.degree v = 2

/-! ## Greedy Δ+1, reused (not Brooks) -/

/-- Folklore / Diestel `χ ≤ Δ+1`. Not Brooks. -/
theorem greedy_colorable : G.Colorable (G.maxDegree + 1) :=
  ProofLab.GreedyChromatic.greedy_colorable

lemma chromaticNumber_le_maxDegree_add_one :
    G.chromaticNumber ≤ G.maxDegree + 1 :=
  greedy_colorable.chromaticNumber_le

/-! ## Level A: complete-graph exception (`χ = Δ+1`) -/

lemma maxDegree_top [Nonempty V] :
    (⊤ : SimpleGraph V).maxDegree = Fintype.card V - 1 :=
  ProofLab.GreedyChromatic.maxDegree_top

/-- Load-bearing exception: nonempty complete graphs need `Δ+1` colours.
Dropping `G ≠ ⊤` makes Brooks false. -/
lemma chromaticNumber_top_eq_maxDegree_add_one [Nonempty V] :
    (⊤ : SimpleGraph V).chromaticNumber =
      ((⊤ : SimpleGraph V).maxDegree + 1 : ℕ) :=
  ProofLab.GreedyChromatic.chromaticNumber_top_eq_maxDegree_add_one

/-! ## Level A: 2-regular glue -/

lemma maxDegree_eq_two_of_two_regular [Nonempty V] (hdeg : ∀ v, G.degree v = 2) :
    G.maxDegree = 2 :=
  le_antisymm
    (G.maxDegree_le_of_forall_degree_le 2 fun v => (hdeg v).le)
    (by
      obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
      rw [hv, hdeg])

lemma oddDeg_card_zero_of_two_regular (hdeg : ∀ v, G.degree v = 2) :
    Fintype.card { v : V | Odd (G.degree v) } = 0 := by
  rw [Fintype.card_eq_zero_iff]
  refine ⟨fun ⟨v, hv⟩ => ?_⟩
  have hv' : Odd (G.degree v) := hv
  rw [hdeg v] at hv'
  exact (by decide : ¬ Odd (2 : ℕ)) hv'

lemma card_edgeFinset_eq_card_of_two_regular (hdeg : ∀ v, G.degree v = 2) :
    G.edgeFinset.card = Fintype.card V := by
  have hsum := G.sum_degrees_eq_twice_card_edges
  have hconst : ∑ v : V, G.degree v = ∑ _v : V, (2 : ℕ) :=
    Finset.sum_congr rfl fun v _ => hdeg v
  have htwo : ∑ _v : V, (2 : ℕ) = 2 * Fintype.card V := by
    simp [sum_const, card_univ, nsmul_eq_mul, mul_comm]
  have : 2 * G.edgeFinset.card = 2 * Fintype.card V := by
    rw [← hsum, hconst, htwo]
  exact Nat.mul_left_cancel (by decide : 0 < 2) this

lemma edgeSet_nonempty_of_two_regular (hConn : G.Connected)
    (hdeg : ∀ v, G.degree v = 2) : G.edgeSet.Nonempty := by
  haveI := hConn.nonempty
  obtain ⟨v⟩ := hConn.nonempty
  have hpos : 0 < G.degree v := by
    rw [hdeg]
    exact two_pos
  obtain ⟨w, hw⟩ := (G.degree_pos_iff_exists_adj (v := v)).mp hpos
  exact ⟨s(v, w), hw⟩

/-! ## Level A: odd closed walk from the 2-regular pin -/

/-- Hierholzer circuit (reused, not re-proved) of a 2-regular connected graph
has length `|V|`. Odd order ⇒ odd closed walk. -/
lemma exists_odd_loop_of_isOddCycle (h : IsOddCycle G) :
    ∃ (u : V) (p : G.Walk u u), Odd p.length := by
  obtain ⟨hConn, hOdd, hdeg⟩ := h
  have hodd0 := oddDeg_card_zero_of_two_regular hdeg
  have hE := edgeSet_nonempty_of_two_regular hConn hdeg
  obtain ⟨u, p, hEul, _hCirc⟩ :=
    ProofLab.Eulerian.eulerian_hierholzer_circuit hConn hodd0 hE
  refine ⟨u, p, ?_⟩
  have hlen : p.length = Fintype.card V := by
    have hcard : p.length = G.edgeFinset.card := by
      have heq := hEul.edgesFinset_eq
      have hpcard : p.edges.length = G.edgeFinset.card := by
        simpa [Walk.IsTrail.edgesFinset] using congrArg Finset.card heq
      exact (Walk.length_edges p).symm.trans hpcard
    exact hcard.trans (card_edgeFinset_eq_card_of_two_regular hdeg)
  simpa [hlen] using hOdd

lemma three_le_chromaticNumber_of_isOddCycle (h : IsOddCycle G) :
    3 ≤ G.chromaticNumber := by
  obtain ⟨u, p, hodd⟩ := exists_odd_loop_of_isOddCycle h
  exact Walk.three_le_chromaticNumber_of_odd_loop p hodd

/-- 2-regular ⇒ `Δ = 2`; greedy supplies the 3-colouring. Not Brooks. -/
lemma colorable_three_of_isOddCycle (h : IsOddCycle G) : G.Colorable 3 := by
  haveI := h.1.nonempty
  have hΔ : G.maxDegree = 2 := maxDegree_eq_two_of_two_regular h.2.2
  simpa [hΔ] using (greedy_colorable : G.Colorable (G.maxDegree + 1))

/-- Load-bearing exception: odd cycles need `Δ+1 = 3` colours.
Dropping `¬ IsOddCycle` makes Brooks false. -/
lemma chromaticNumber_eq_three_of_isOddCycle (h : IsOddCycle G) :
    G.chromaticNumber = 3 :=
  le_antisymm (colorable_three_of_isOddCycle h).chromaticNumber_le
    (three_le_chromaticNumber_of_isOddCycle h)

lemma chromaticNumber_eq_maxDegree_add_one_of_isOddCycle (h : IsOddCycle G) :
    G.chromaticNumber = (G.maxDegree + 1 : ℕ) := by
  haveI := h.1.nonempty
  rw [chromaticNumber_eq_three_of_isOddCycle h,
    maxDegree_eq_two_of_two_regular h.2.2]
  norm_cast

/-! ## Level B: Diestel first family (`Δ ≤ 2`)

Named published argument (Brooks 1941 / Diestel, the Δ ≤ 2 case):
a connected graph with `Δ ≤ 2` is a path or a cycle. Excluding `⊤`
and odd cycles leaves paths and even cycles, both 2-colourable.

Even 2-regular: Hierholzer circuit is a Hamiltonian cycle of even
length; colour by index mod 2.
Not 2-regular: delete a degree-1 vertex and extend a 2-colouring.

Residual namesake: `Δ`-regular with `Δ ≥ 3`, not complete — Kempe /
Lovász contraction, not this heartbeat. Do not `sorry`.
-/

lemma exists_isPath (hConn : G.Connected) (a b : V) :
    ∃ p : G.Walk a b, p.IsPath :=
  ⟨(hConn a b).some.bypass, Walk.bypass_isPath _⟩

lemma support_get_eq_getVert {u v : V} (p : G.Walk u v) (n : ℕ)
    (hn : n < p.support.length) :
    p.support.get ⟨n, hn⟩ = p.getVert n := by
  induction p generalizing n with
  | nil =>
    have hn0 : n = 0 := by
      simp only [Walk.support_nil, List.length_singleton] at hn
      exact Nat.lt_one_iff.mp hn
    subst n
    rfl
  | cons h q ih =>
    cases n with
    | zero =>
      simp [Walk.support_cons]
    | succ n =>
      have hn' : n < q.support.length := by
        simpa [Walk.support_cons] using (Nat.succ_lt_succ_iff.mp hn)
      simpa [Walk.support_cons, Walk.cons_getVert_succ] using ih n hn'

lemma support_tail_length {u v : V} (p : G.Walk u v) :
    p.support.tail.length = p.length := by
  have h := Walk.support_eq_cons p
  have hs := Walk.length_support p
  rw [h, List.length_cons] at hs
  omega

lemma support_tail_get_eq_getVert_succ {u v : V} :
    ∀ (p : G.Walk u v) (k : ℕ) (hk : k < p.support.tail.length),
      p.support.tail.get ⟨k, hk⟩ = p.getVert (k + 1)
  | Walk.nil, k, hk => by
    simp [Walk.support_nil] at hk
  | Walk.cons h q, k, hk => by
    simpa [Walk.support_cons, Walk.cons_getVert_succ] using
      support_get_eq_getVert q k (by simpa [Walk.support_cons] using hk)

lemma two_le_degree_of_isPath_length_ge_two {a b : V} {p : G.Walk a b}
    (hp : p.IsPath) (hlen : 2 ≤ p.length) :
    2 ≤ G.degree (p.getVert 1) := by
  have h0 : 0 < p.length := by omega
  have h1 : 1 < p.length := by omega
  have hadj0 : G.Adj (p.getVert 0) (p.getVert 1) := Walk.adj_getVert_succ p h0
  have hadj1 : G.Adj (p.getVert 1) (p.getVert 2) := Walk.adj_getVert_succ p h1
  have hne : p.getVert 0 ≠ p.getVert 2 := by
    intro h
    have hs0 : 0 < p.support.length := by
      simp [Walk.length_support]
    have hs2 : 2 < p.support.length := by
      simp [Walk.length_support]
      omega
    have hinj := List.nodup_iff_injective_get.mp hp.support_nodup
    have h0eq := support_get_eq_getVert p 0 hs0
    have h2eq := support_get_eq_getVert p 2 hs2
    have heq := hinj (h0eq.trans (h.trans h2eq.symm))
    exact (by decide : (0 : ℕ) ≠ 2) (congrArg Fin.val heq)
  have hsub : ({p.getVert 0, p.getVert 2} : Finset V) ⊆ G.neighborFinset (p.getVert 1) := by
    intro z hz
    simp only [mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact (mem_neighborFinset _ _ _).mpr hadj0.symm
    · exact (mem_neighborFinset _ _ _).mpr hadj1
  have hnotin : p.getVert 0 ∉ ({p.getVert 2} : Finset V) := by
    exact mt mem_singleton.mp hne
  have hcard : ({p.getVert 0, p.getVert 2} : Finset V).card = 2 := by
    rw [card_insert_of_not_mem hnotin, card_singleton]
  have hle := card_le_card hsub
  rw [hcard, card_neighborFinset_eq_degree] at hle
  exact hle

lemma eq_top_of_subsingleton [Subsingleton V] : G = ⊤ := by
  ext a b
  constructor
  · intro h
    exact G.ne_of_adj h
  · intro hne
    exact (hne (Subsingleton.elim a b)).elim

lemma eq_top_of_card_eq_two_of_adj (hcard : Fintype.card V = 2) {a b : V}
    (hne : a ≠ b) (hab : G.Adj a b) : G = ⊤ := by
  have hall : ∀ z : V, z = a ∨ z = b := by
    intro z
    by_contra hz
    push_neg at hz
    have ha_notin : a ∉ ({b, z} : Finset V) := by
      simp only [mem_insert, mem_singleton, not_or]
      exact ⟨hne, hz.1.symm⟩
    have hb_notin : b ∉ ({z} : Finset V) := by
      simp only [mem_singleton]
      exact hz.2.symm
    have h3 : ({a, b, z} : Finset V).card = 3 := by
      rw [card_insert_of_not_mem, card_insert_of_not_mem, card_singleton]
      · exact hb_notin
      · exact ha_notin
    have : 3 ≤ Fintype.card V := by
      have := card_le_card (subset_univ ({a, b, z} : Finset V))
      simpa [card_univ, h3] using this
    omega
  ext x y
  constructor
  · intro hxy
    exact G.ne_of_adj hxy
  · intro hxy
    rcases hall x with hx | hx <;> rcases hall y with hy | hy
    · exact (hxy (hx.trans hy.symm)).elim
    · rw [hx, hy]; exact hab
    · rw [hx, hy]; exact hab.symm
    · exact (hxy (hx.trans hy.symm)).elim

/-- Connected + `Δ ≤ 1` ⇒ complete (`K_1` or `K_2`). -/
lemma eq_top_of_connected_maxDegree_le_one (hConn : G.Connected)
    (hΔ : G.maxDegree ≤ 1) : G = ⊤ := by
  haveI := hConn.nonempty
  by_cases hle1 : Fintype.card V ≤ 1
  · haveI : Subsingleton V := (Fintype.card_le_one_iff_subsingleton).mp hle1
    exact eq_top_of_subsingleton
  · have ⟨a, b, hne⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card V)
    obtain ⟨p, hp⟩ := exists_isPath hConn a b
    have hlen1 : p.length = 1 := by
      have hpos : 0 < p.length := by
        have : ¬ p.Nil := Walk.not_nil_of_ne hne
        rw [Walk.nil_iff_length_eq] at this
        omega
      have : p.length < 2 := by
        by_contra h
        have h2 : 2 ≤ p.length := by omega
        have hdeg := two_le_degree_of_isPath_length_ge_two hp h2
        have := (G.degree_le_maxDegree (p.getVert 1)).trans hΔ
        omega
      omega
    have hab : G.Adj a b := by
      have hadj := Walk.adj_getVert_succ p (by omega : 0 < p.length)
      rw [Walk.getVert_zero] at hadj
      have hend : p.getVert 1 = b := by
        have : 1 = p.length := by omega
        rw [this, Walk.getVert_length]
      rwa [hend] at hadj
    by_cases h3 : 3 ≤ Fintype.card V
    · obtain ⟨c, hc1, hc2⟩ : ∃ c : V, c ≠ a ∧ c ≠ b := by
        by_contra h
        push_neg at h
        have : (univ : Finset V) ⊆ {a, b} := by
          intro x _
          by_cases hx : x = a
          · exact mem_insert.mpr (Or.inl hx)
          · exact mem_insert.mpr (Or.inr (mem_singleton.mpr (h x hx)))
        have : Fintype.card V ≤ ({a, b} : Finset V).card := by
          simpa [card_univ] using card_le_card this
        have : ({a, b} : Finset V).card ≤ 2 :=
          (card_insert_le a {b}).trans (by simp)
        omega
      obtain ⟨q, hq⟩ := exists_isPath hConn a c
      have hqlen : q.length = 1 := by
        have hpos : 0 < q.length := by
          have : ¬ q.Nil := Walk.not_nil_of_ne hc1.symm
          rw [Walk.nil_iff_length_eq] at this
          omega
        have : q.length < 2 := by
          by_contra h
          have h2 : 2 ≤ q.length := by omega
          have hdeg := two_le_degree_of_isPath_length_ge_two hq h2
          have := (G.degree_le_maxDegree (q.getVert 1)).trans hΔ
          omega
        omega
      have hac : G.Adj a c := by
        have hadj := Walk.adj_getVert_succ q (by omega : 0 < q.length)
        rw [Walk.getVert_zero] at hadj
        have hend : q.getVert 1 = c := by
          have : 1 = q.length := by omega
          rw [this, Walk.getVert_length]
        rwa [hend] at hadj
      have hdeg2 : 2 ≤ G.degree a := by
        have hsub : ({b, c} : Finset V) ⊆ G.neighborFinset a := by
          intro z hz
          simp only [mem_insert, mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact (mem_neighborFinset _ _ _).mpr hab
          · exact (mem_neighborFinset _ _ _).mpr hac
        have hnotin : b ∉ ({c} : Finset V) := mt mem_singleton.mp hc2.symm
        have hcard : ({b, c} : Finset V).card = 2 := by
          rw [card_insert_of_not_mem hnotin, card_singleton]
        have hle := card_le_card hsub
        rw [hcard, card_neighborFinset_eq_degree] at hle
        exact hle
      have := (G.degree_le_maxDegree a).trans hΔ
      omega
    · have h2 : Fintype.card V = 2 := by omega
      exact eq_top_of_card_eq_two_of_adj h2 hne hab

/-- Vacuous under Brooks hypotheses: connected `Δ ≤ 1` graphs are complete. -/
lemma brooks_colorable_of_maxDegree_le_one (hConn : G.Connected)
    (hNotComplete : G ≠ ⊤) (hΔ : G.maxDegree ≤ 1) :
    G.Colorable G.maxDegree :=
  (hNotComplete (eq_top_of_connected_maxDegree_le_one hConn hΔ)).elim

lemma eulerian_circuit_length_eq_card_of_two_regular
    (hdeg : ∀ v, G.degree v = 2) {u : V} {p : G.Walk u u}
    (hEul : p.IsEulerian) : p.length = Fintype.card V := by
  have hcard : p.length = G.edgeFinset.card := by
    have heq := hEul.edgesFinset_eq
    have hpcard : p.edges.length = G.edgeFinset.card := by
      simpa [Walk.IsTrail.edgesFinset] using congrArg Finset.card heq
    exact (Walk.length_edges p).symm.trans hpcard
  exact hcard.trans (card_edgeFinset_eq_card_of_two_regular hdeg)

lemma exists_getVert_of_mem_edges {u v : V} :
    ∀ (p : G.Walk u v) {e : Sym2 V}, e ∈ p.edges →
      ∃ i, i < p.length ∧ s(p.getVert i, p.getVert (i + 1)) = e
  | Walk.nil, e, he => by simp [Walk.edges_nil] at he
  | Walk.cons h q, e, he => by
    rw [Walk.edges_cons, List.mem_cons] at he
    rcases he with hEq | hmem
    · refine ⟨0, Nat.succ_pos _, ?_⟩
      simpa [Walk.getVert_zero] using hEq.symm
    · obtain ⟨i, hi, hie⟩ := exists_getVert_of_mem_edges q hmem
      refine ⟨i + 1, Nat.succ_lt_succ hi, ?_⟩
      simpa [Walk.cons_getVert_succ] using hie

lemma mem_support_of_two_regular_eulerian {u : V} {p : G.Walk u u}
    (hEul : p.IsEulerian) (hdeg : ∀ v, G.degree v = 2) (x : V) :
    x ∈ p.support := by
  have hpos : 0 < G.degree x := by
    rw [hdeg]
    exact two_pos
  obtain ⟨w, hw⟩ := (G.degree_pos_iff_exists_adj (v := x)).mp hpos
  have he : s(x, w) ∈ p.edges := (Walk.IsEulerian.mem_edges_iff hEul).mpr hw
  exact p.fst_mem_support_of_mem_edges he

lemma end_mem_tail_support_of_not_nil {u v : V} {p : G.Walk u v}
    (h : ¬ p.Nil) : v ∈ p.support.tail := by
  obtain ⟨w, hw, q, rfl⟩ := Walk.not_nil_iff.mp h
  simp [Walk.support_cons, Walk.end_mem_support]

lemma isCycle_of_eulerian_two_regular {u : V} {p : G.Walk u u}
    (hEul : p.IsEulerian) (hCirc : p.IsCircuit)
    (hdeg : ∀ v, G.degree v = 2)
    (hlen : p.length = Fintype.card V) : p.IsCycle := by
  refine ⟨hCirc, ?_⟩
  have htail_u : u ∈ p.support.tail :=
    end_mem_tail_support_of_not_nil hCirc.not_nil
  have htail : ∀ x : V, x ∈ p.support.tail := by
    intro x
    have hx : x ∈ p.support := mem_support_of_two_regular_eulerian hEul hdeg x
    rw [Walk.mem_support_iff] at hx
    rcases hx with rfl | hx
    · exact htail_u
    · exact hx
  have hlen_tail : p.support.tail.length = Fintype.card V := by
    rw [support_tail_length, hlen]
  let f : Fin p.support.tail.length → V := fun i => p.support.tail.get i
  have hsurj : Surjective f := by
    intro x
    have hx : x ∈ p.support.tail := htail x
    obtain ⟨n, hn⟩ := List.mem_iff_get.mp hx
    exact ⟨n, hn⟩
  have hcard : Fintype.card (Fin p.support.tail.length) = Fintype.card V := by
    simp [Fintype.card_fin, hlen_tail]
  have hinj : Injective f :=
    ((Fintype.bijective_iff_surjective_and_card f).2 ⟨hsurj, hcard⟩).1
  exact List.nodup_iff_injective_get.mpr hinj

lemma exists_lt_length_getVert_closed {u : V} {p : G.Walk u u}
    (hpos : 0 < p.length) {x : V} (hx : x ∈ p.support) :
    ∃ n < p.length, p.getVert n = x := by
  obtain ⟨n, hn, hle⟩ := (Walk.mem_support_iff_exists_getVert (p := p)).mp hx
  rcases eq_or_lt_of_le hle with hEq | hLt
  · refine ⟨0, hpos, ?_⟩
    rw [Walk.getVert_zero, ← Walk.getVert_length p, ← hEq, hn]
  · exact ⟨n, hLt, hn⟩

lemma getVert_injective_of_isCycle {u : V} {p : G.Walk u u}
    (hc : p.IsCycle) {i j : ℕ}
    (hi : i < p.length) (hj : j < p.length)
    (heq : p.getVert i = p.getVert j) : i = j := by
  have hnodup := hc.support_nodup
  wlog hle : i ≤ j generalizing i j
  · exact (this hj hi heq.symm (le_of_not_le hle)).symm
  rcases eq_or_lt_of_le hle with rfl | hlt
  · rfl
  · have hlen_tail : p.support.tail.length = p.length := support_tail_length p
    by_cases hi0 : i = 0
    · subst i
      have hj_u : p.getVert j = u := by
        simpa [Walk.getVert_zero] using heq.symm
      have hj1 : j - 1 < p.support.tail.length := by
        rw [hlen_tail]; omega
      have hget_j : p.support.tail.get ⟨j - 1, hj1⟩ = u := by
        have hj' : j = (j - 1) + 1 := by omega
        have := support_tail_get_eq_getVert_succ p (j - 1) hj1
        rw [← hj'] at this
        exact this.trans hj_u
      have hpos : 0 < p.length := lt_of_le_of_lt (Nat.zero_le j) hj
      have hlast : p.length - 1 < p.support.tail.length := by
        rw [hlen_tail]; omega
      have hget_last : p.support.tail.get ⟨p.length - 1, hlast⟩ = u := by
        have := support_tail_get_eq_getVert_succ p (p.length - 1) hlast
        have hsum : p.length - 1 + 1 = p.length := Nat.sub_add_cancel hpos
        rw [hsum] at this
        exact this.trans (Walk.getVert_length p)
      have hne : (⟨j - 1, hj1⟩ : Fin p.support.tail.length) ≠ ⟨p.length - 1, hlast⟩ := by
        intro hfin
        have : j - 1 = p.length - 1 := Fin.mk.inj hfin
        omega
      have hinj := List.nodup_iff_injective_get.mp hnodup
      exact (hne (hinj (hget_j.trans hget_last.symm))).elim
    · have hi1 : 0 < i := Nat.pos_of_ne_zero hi0
      have hj1 : 0 < j := lt_of_lt_of_le hi1 hle
      have hi_t : i - 1 < p.support.tail.length := by rw [hlen_tail]; omega
      have hj_t : j - 1 < p.support.tail.length := by rw [hlen_tail]; omega
      have hgi : p.support.tail.get ⟨i - 1, hi_t⟩ = p.getVert i := by
        have hi' : i = (i - 1) + 1 := by omega
        have := support_tail_get_eq_getVert_succ p (i - 1) hi_t
        rwa [← hi'] at this
      have hgj : p.support.tail.get ⟨j - 1, hj_t⟩ = p.getVert j := by
        have hj' : j = (j - 1) + 1 := by omega
        have := support_tail_get_eq_getVert_succ p (j - 1) hj_t
        rwa [← hj'] at this
      have hinj := List.nodup_iff_injective_get.mp hnodup
      have hfin : (⟨i - 1, hi_t⟩ : Fin p.support.tail.length) = ⟨j - 1, hj_t⟩ :=
        hinj (hgi.trans (heq.trans hgj.symm))
      have : i - 1 = j - 1 := Fin.mk.inj hfin
      omega

lemma nat_mod_two_succ_ne (n : ℕ) : n % 2 ≠ (n + 1) % 2 := by
  rw [Nat.add_mod n 1]
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · rw [h]; exact Nat.zero_ne_one
  · rw [h]; exact Nat.one_ne_zero

/-- Even 2-regular connected graphs are 2-colourable (even cycles). -/
lemma colorable_two_of_two_regular_even (hConn : G.Connected)
    (hdeg : ∀ v, G.degree v = 2) (hEven : Even (Fintype.card V)) :
    G.Colorable 2 := by
  have hodd0 := oddDeg_card_zero_of_two_regular hdeg
  have hE := edgeSet_nonempty_of_two_regular hConn hdeg
  obtain ⟨u, p, hEul, hCirc⟩ :=
    ProofLab.Eulerian.eulerian_hierholzer_circuit hConn hodd0 hE
  have hlen : p.length = Fintype.card V :=
    eulerian_circuit_length_eq_card_of_two_regular hdeg hEul
  have hcyc : p.IsCycle :=
    isCycle_of_eulerian_two_regular hEul hCirc hdeg hlen
  have hpos : 0 < p.length := by
    have : p ≠ Walk.nil := hCirc.ne_nil
    cases p with
    | nil => exact (this rfl).elim
    | cons _ _ => simp [Walk.length]
  have hspan : ∀ x : V, ∃ n < p.length, p.getVert n = x := fun x =>
    exists_lt_length_getVert_closed hpos
      (mem_support_of_two_regular_eulerian hEul hdeg x)
  have huniq : ∀ {x : V} {i j : ℕ},
      i < p.length → j < p.length → p.getVert i = x → p.getVert j = x → i = j := by
    intro x i j hi hj hi' hj'
    exact getVert_injective_of_isCycle hcyc hi hj (hi'.trans hj'.symm)
  let idx : V → ℕ := fun x => Classical.choose (hspan x)
  have hidx : ∀ x, idx x < p.length ∧ p.getVert (idx x) = x := fun x =>
    Classical.choose_spec (hspan x)
  have hidx_eq : ∀ x i, i < p.length → p.getVert i = x → idx x = i := by
    intro x i hi hx
    exact huniq (hidx x).1 hi (hidx x).2 hx
  have hEvenp : Even p.length := by simpa [hlen] using hEven
  refine ⟨Coloring.mk (fun x => ⟨idx x % 2, Nat.mod_lt _ two_pos⟩) ?_⟩
  intro x y hxy
  have he : s(x, y) ∈ p.edges := (Walk.IsEulerian.mem_edges_iff hEul).mpr hxy
  obtain ⟨i, hi, hie⟩ := exists_getVert_of_mem_edges p he
  have hsym :
      p.getVert i = x ∧ p.getVert (i + 1) = y ∨
        p.getVert i = y ∧ p.getVert (i + 1) = x :=
    (Sym2.eq_iff).mp hie
  have hmod : idx x % 2 ≠ idx y % 2 := by
    have hwrap : (p.length - 1) % 2 ≠ 0 := by
      have : p.length % 2 = 0 := Nat.even_iff.mp hEvenp
      omega
    rcases hsym with ⟨hx, hy⟩ | ⟨hy, hx⟩
    · by_cases hlast : i + 1 = p.length
      · have hy0 : y = u := by
          have := Walk.getVert_length p
          rw [← hlast] at this
          exact hy.symm.trans this
        have hx_idx : idx x = i := hidx_eq x i hi hx
        have hy_idx : idx y = 0 :=
          hidx_eq y 0 hpos (by simp [Walk.getVert_zero, hy0])
        have hi_last : i = p.length - 1 := by omega
        simpa [hx_idx, hy_idx, hi_last] using hwrap
      · have hi1 : i + 1 < p.length :=
          Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hi) hlast
        have hx_idx : idx x = i := hidx_eq x i hi hx
        have hy_idx : idx y = i + 1 := hidx_eq y (i + 1) hi1 hy
        simpa [hx_idx, hy_idx] using nat_mod_two_succ_ne i
    · by_cases hlast : i + 1 = p.length
      · have hx0 : x = u := by
          have := Walk.getVert_length p
          rw [← hlast] at this
          exact hx.symm.trans this
        have hy_idx : idx y = i := hidx_eq y i hi hy
        have hx_idx : idx x = 0 :=
          hidx_eq x 0 hpos (by simp [Walk.getVert_zero, hx0])
        have hi_last : i = p.length - 1 := by omega
        simpa [hy_idx, hx_idx, hi_last] using Ne.symm hwrap
      · have hi1 : i + 1 < p.length :=
          Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hi) hlast
        have hy_idx : idx y = i := hidx_eq y i hi hy
        have hx_idx : idx x = i + 1 := hidx_eq x (i + 1) hi1 hx
        simpa [hx_idx, hy_idx] using (nat_mod_two_succ_ne i).symm
  exact Fin.ne_of_val_ne hmod

lemma colorable_two_of_card_le_one (h : Fintype.card V ≤ 1) : G.Colorable 2 :=
  Colorable.mono (Nat.le_trans h (by decide : 1 ≤ 2)) G.colorable_of_fintype

lemma card_eq_one_of_connected_degree_zero (hConn : G.Connected) {v : V}
    (hdeg : G.degree v = 0) : Fintype.card V = 1 := by
  haveI := hConn.nonempty
  rw [Fintype.card_eq_one_iff]
  refine ⟨v, fun w => ?_⟩
  obtain ⟨p⟩ := hConn v w
  by_contra hne
  have hnil : ¬ p.Nil := Walk.not_nil_of_ne (Ne.symm hne)
  obtain ⟨x, hx, _, _⟩ := Walk.not_nil_iff.mp hnil
  have : 0 < G.degree v := (G.degree_pos_iff_exists_adj (v := v)).mpr ⟨x, hx⟩
  omega

lemma colorable_extend_of_degree_le_one {v : V} (hdeg : G.degree v ≤ 1)
    (h : (G.induce {x | x ≠ v}).Colorable 2) : G.Colorable 2 := by
  obtain ⟨c⟩ := h
  let used : Finset (Fin 2) :=
    (G.neighborFinset v).attach.image fun ⟨w, hw⟩ =>
      c ⟨w, (G.ne_of_adj ((mem_neighborFinset G v w).mp hw)).symm⟩
  have hused : used.card ≤ G.degree v := by
    have hle : used.card ≤ (G.neighborFinset v).attach.card := card_image_le
    have hdeg' : (G.neighborFinset v).attach.card = G.degree v := by
      rw [card_attach, degree]
    exact hle.trans hdeg'.le
  have hex : ∃ col : Fin 2, col ∉ used := by
    have hlt : used.card < Fintype.card (Fin 2) := by
      rw [Fintype.card_fin]
      omega
    by_contra hnone
    push_neg at hnone
    have : used = univ := eq_univ_iff_forall.mpr hnone
    rw [this, card_univ] at hlt
    exact (lt_irrefl _ hlt)
  obtain ⟨col, hcol⟩ := hex
  let color : V → Fin 2 := fun x =>
    if hx : x = v then col else c ⟨x, hx⟩
  refine ⟨Coloring.mk color ?_⟩
  intro x y hxy
  dsimp [color]
  split_ifs with hx hy hy
  · exact (G.ne_of_adj hxy (hx.trans hy.symm)).elim
  · intro hceq
    apply hcol
    have hadj : G.Adj v y := by rwa [hx] at hxy
    rw [hceq]
    exact mem_image.mpr
      ⟨⟨y, (mem_neighborFinset G v y).mpr hadj⟩, mem_attach _ _, rfl⟩
  · intro hceq
    apply hcol
    have hadj : G.Adj v x := by
      rw [hy] at hxy
      exact hxy.symm
    rw [← hceq]
    exact mem_image.mpr
      ⟨⟨x, (mem_neighborFinset G v x).mpr hadj⟩, mem_attach _ _, rfl⟩
  · exact c.valid hxy

lemma not_mem_support_of_isPath_of_degree_le_one {a b v : V}
    {p : G.Walk a b} (hp : p.IsPath) (ha : a ≠ v) (hb : b ≠ v)
    (hdeg : G.degree v ≤ 1) : v ∉ p.support := by
  intro hv
  obtain ⟨q, r, rfl⟩ := Walk.mem_support_iff_exists_append.mp hv
  have hqnil : ¬ q.Nil := Walk.not_nil_of_ne ha
  have hrnil : ¬ r.Nil := Walk.not_nil_of_ne hb.symm
  have hqrev_nil : ¬ q.reverse.Nil := by
    rw [Walk.nil_iff_length_eq, Walk.length_reverse, ← Walk.nil_iff_length_eq]
    exact hqnil
  let w := q.reverse.sndOfNotNil hqrev_nil
  have hw : G.Adj v w := q.reverse.adj_sndOfNotNil hqrev_nil
  let z := r.sndOfNotNil hrnil
  have hz : G.Adj v z := r.adj_sndOfNotNil hrnil
  have hw_edge : s(v, w) ∈ q.edges := by
    have : s(v, w) ∈ q.reverse.edges := by
      rw [← Walk.cons_tail_eq q.reverse hqrev_nil, Walk.edges_cons]
      exact List.mem_cons_self _ _
    simpa [Walk.edges_reverse] using this
  have hz_edge : s(v, z) ∈ r.edges := by
    rw [← Walk.cons_tail_eq r hrnil, Walk.edges_cons]
    exact List.mem_cons_self _ _
  have hnd : (q.append r).edges.Nodup := hp.edges_nodup
  rw [Walk.edges_append] at hnd
  have dj := List.disjoint_of_nodup_append hnd
  by_cases hwz : w = z
  · have hz_edge' : s(v, w) ∈ r.edges := hwz.symm ▸ hz_edge
    exact dj hw_edge hz_edge'
  · have : 2 ≤ G.degree v := by
      have hsub : ({w, z} : Finset V) ⊆ G.neighborFinset v := by
        intro t ht
        simp only [mem_insert, mem_singleton] at ht
        rcases ht with rfl | rfl
        · exact (mem_neighborFinset _ _ _).mpr hw
        · exact (mem_neighborFinset _ _ _).mpr hz
      have hnotin : w ∉ ({z} : Finset V) := mt mem_singleton.mp hwz
      have hcard : ({w, z} : Finset V).card = 2 := by
        rw [card_insert_of_not_mem hnotin, card_singleton]
      have hle := card_le_card hsub
      rw [hcard, card_neighborFinset_eq_degree] at hle
      exact hle
    omega

lemma induce_reachable_of_support_subset {s : Set V} [DecidablePred (· ∈ s)]
    {a b : V} (p : G.Walk a b) :
    ∀ (ha : a ∈ s) (hb : b ∈ s),
      (∀ x ∈ p.support, x ∈ s) →
        (G.induce s).Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
  induction p with
  | nil =>
    intro ha hb _
    exact ⟨Walk.nil.copy rfl (Subtype.ext rfl)⟩
  | @cons u v w h q ih =>
    intro ha hb hsub
    have hv : v ∈ s :=
      hsub v (by simp [Walk.support_cons, Walk.start_mem_support q])
    obtain ⟨q'⟩ := ih hv hb (fun x hx => hsub x (by simp [Walk.support_cons, hx]))
    have hadj : (G.induce s).Adj ⟨u, ha⟩ ⟨v, hv⟩ := h
    exact ⟨Walk.cons hadj (q'.copy (Subtype.ext rfl) rfl)⟩

lemma connected_induce_erase_of_degree_le_one (hConn : G.Connected) {v : V}
    (hdeg : G.degree v ≤ 1) (hcard : 2 ≤ Fintype.card V) :
    (G.induce {x | x ≠ v}).Connected := by
  haveI : Nonempty ({x | x ≠ v} : Set V) := by
    have : 0 < Fintype.card ({x | x ≠ v} : Set V) := by
      rw [ProofLab.GreedyChromatic.card_induce_erase v]
      omega
    exact Fintype.card_pos_iff.mp this
  refine ⟨fun a b => ?_⟩
  obtain ⟨p, hp⟩ := exists_isPath hConn (a : V) (b : V)
  have hvout : v ∉ p.support :=
    not_mem_support_of_isPath_of_degree_le_one hp a.property b.property hdeg
  have hsub : ∀ x ∈ p.support, x ∈ ({x | x ≠ v} : Set V) := by
    intro x hx hxv
    exact hvout (hxv ▸ hx)
  exact induce_reachable_of_support_subset p a.property b.property hsub

lemma not_isOddCycle_induce_erase_leaf {v w : V}
    (hΔ : G.maxDegree ≤ 2) (hw : G.Adj v w) :
    ¬ IsOddCycle (G.induce {x | x ≠ v}) := by
  intro hOdd
  have hne : w ≠ v := G.ne_of_adj hw.symm
  have hdeg' := hOdd.2.2 ⟨w, hne⟩
  have hvn : v ∈ G.neighborFinset w := (G.mem_neighborFinset w v).mpr hw.symm
  let f : ({x | x ≠ v} : Set V) ↪ V := Embedding.subtype _
  have hsub :
      ((G.induce {x | x ≠ v}).neighborFinset ⟨w, hne⟩).map f ⊆
        (G.neighborFinset w).erase v := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
    have hy' : G.Adj w (y : V) := by
      simpa [mem_neighborFinset] using hy
    exact mem_erase.mpr ⟨y.property, (mem_neighborFinset _ _ _).mpr hy'⟩
  have hcard := card_le_card hsub
  have hf :
      (((G.induce {x | x ≠ v}).neighborFinset ⟨w, hne⟩).map f).card =
        (G.induce {x | x ≠ v}).degree ⟨w, hne⟩ := by
    rw [card_map, degree]
  rw [hf] at hcard
  have herase : ((G.neighborFinset w).erase v).card = G.degree w - 1 := by
    rw [card_erase_of_mem hvn, degree]
  have : G.degree w ≤ 2 := (G.degree_le_maxDegree w).trans hΔ
  omega

/-- Diestel Δ ≤ 2 family: connected, not an odd cycle, `Δ ≤ 2` ⇒ 2-colourable. -/
lemma colorable_two_of_maxDegree_le_two_of_card :
    ∀ (k : ℕ) (V : Type*) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      Fintype.card V ≤ k →
      G.Connected →
      G.maxDegree ≤ 2 →
      ¬ IsOddCycle G →
      G.Colorable 2 := by
  intro k
  induction k with
  | zero =>
    intro V _ _ G _ hle _ _ _
    exact colorable_two_of_card_le_one (Nat.le_trans hle (by decide : (0 : ℕ) ≤ 1))
  | succ k ih =>
    intro V _ _ G _ hle hConn hΔ hNotOdd
    by_cases hsmall : Fintype.card V ≤ 1
    · exact colorable_two_of_card_le_one hsmall
    · have hcard2 : 2 ≤ Fintype.card V := by omega
      by_cases hreg : ∀ v : V, G.degree v = 2
      · have hOdd : ¬ Odd (Fintype.card V) := fun hO =>
          hNotOdd ⟨hConn, hO, hreg⟩
        have hEven : Even (Fintype.card V) := by
          cases Nat.even_or_odd (Fintype.card V) with
          | inl hE => exact hE
          | inr hO => exact (hOdd hO).elim
        exact colorable_two_of_two_regular_even hConn hreg hEven
      · push_neg at hreg
        obtain ⟨v, hvne⟩ := hreg
        have hdv : G.degree v ≤ 1 := by
          have := G.degree_le_maxDegree v
          omega
        by_cases h0 : G.degree v = 0
        · have h1 : Fintype.card V = 1 :=
            card_eq_one_of_connected_degree_zero hConn h0
          exact colorable_two_of_card_le_one h1.le
        · let s : Set V := {x | x ≠ v}
          let G' : SimpleGraph s := G.induce s
          have hle' : Fintype.card s ≤ k := by
            rw [ProofLab.GreedyChromatic.card_induce_erase v]
            omega
          have hConn' : G'.Connected :=
            connected_induce_erase_of_degree_le_one hConn hdv hcard2
          have hΔ' : G'.maxDegree ≤ 2 :=
            (ProofLab.GreedyChromatic.maxDegree_induce_le s).trans hΔ
          have hNotOdd' : ¬ IsOddCycle G' := by
            obtain ⟨w, hw⟩ := (G.degree_pos_iff_exists_adj (v := v)).mp
              (by omega : 0 < G.degree v)
            exact not_isOddCycle_induce_erase_leaf (w := w) hΔ hw
          have ih' : G'.Colorable 2 := ih s G' hle' hConn' hΔ' hNotOdd'
          exact colorable_extend_of_degree_le_one hdv ih'

lemma colorable_two_of_maxDegree_le_two (hConn : G.Connected)
    (hΔ : G.maxDegree ≤ 2) (hNotOdd : ¬ IsOddCycle G) : G.Colorable 2 :=
  colorable_two_of_maxDegree_le_two_of_card (Fintype.card V) V G le_rfl
    hConn hΔ hNotOdd

/-- Named Diestel family: connected, not complete, not odd cycle, `Δ = 2`
⇒ `Colorable Δ`. Even cycles and paths. -/
lemma brooks_colorable_of_maxDegree_eq_two (hConn : G.Connected)
    (_hNotComplete : G ≠ ⊤) (hNotOddCycle : ¬ IsOddCycle G)
    (hΔ : G.maxDegree = 2) : G.Colorable G.maxDegree := by
  rw [hΔ]
  exact colorable_two_of_maxDegree_le_two hConn hΔ.le hNotOddCycle

/-- Named Diestel family: connected, not complete, not odd cycle, `Δ ≤ 2`
⇒ `Colorable Δ`. `Δ ≤ 1` is vacuous (those graphs are complete). -/
lemma brooks_colorable_of_maxDegree_le_two (hConn : G.Connected)
    (hNotComplete : G ≠ ⊤) (hNotOddCycle : ¬ IsOddCycle G)
    (hΔ : G.maxDegree ≤ 2) : G.Colorable G.maxDegree := by
  rcases le_or_gt G.maxDegree 1 with h1 | h2
  · exact brooks_colorable_of_maxDegree_le_one hConn hNotComplete h1
  · have hEq : G.maxDegree = 2 := by omega
    exact brooks_colorable_of_maxDegree_eq_two hConn hNotComplete hNotOddCycle hEq

lemma chromaticNumber_le_maxDegree_of_maxDegree_le_two (hConn : G.Connected)
    (hNotComplete : G ≠ ⊤) (hNotOddCycle : ¬ IsOddCycle G)
    (hΔ : G.maxDegree ≤ 2) : G.chromaticNumber ≤ G.maxDegree :=
  (brooks_colorable_of_maxDegree_le_two hConn hNotComplete hNotOddCycle hΔ).chromaticNumber_le

/-! ## Namesake residual

Intended namesake (not proved here — Kempe / Lovász budget sink on
Δ-regular Δ ≥ 3 not-complete graphs):

```text
theorem brooks_colorable
    (hConn : G.Connected)
    (hNotComplete : G ≠ ⊤)
    (hNotOddCycle : ¬ IsOddCycle G) :
    G.Colorable G.maxDegree
```

Landed this heartbeat: `brooks_colorable_of_maxDegree_le_two`.
Do not label `greedy_colorable` as Brooks. Do not `sorry` the namesake.
-/

end ProofLab.Brooks
