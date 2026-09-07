/-
Andrásfai–Erdős–Sós 1974, triangle-free / r=3 case — Level A glue only.

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 has `CliqueFree` / `Colorable` / `minDegree` / `Walk` and ZERO
named Andrásfai–Erdős–Sós. Completing the Level A shortest-odd-cycle glue is
the gap this ticket lands. The Level B namesake `andrasfai_erdos_sos`
(`5 * minDegree > 3 * n ⇒ Colorable 2`) is **out of this ticket** and is
**not** sorry-ed.

Pin: `catalog/problems/andrasfai-erdos-sos/STATEMENT.md` (OPE-1083; Scout
OPE-1078 prime; Director OPE-1082). Encoding: Mathlib `CliqueFree 3` +
`Colorable 2` + closed `Walk`. Zero `sorry`. Do not import `Archive.*`.

This is **not** Turán / Mantel (already Mathlib; max-edges, a different
theorem). This is **not** `colorable_two_iff_no_odd_walk`
(`ProofLab/BipartiteOddCycle.lean`, PR #79) — characterisation ≠ degree
condition; **USE encoding, do not re-prove**. This is **not** Mycielski
(`ProofLab/Mycielski.lean`, PR #65) — unbounded χ of triangle-free graphs
is the opposite direction. This is **not** Moore / cages / Hoffman–Singleton
/ KST / Zarankiewicz / expander-mixing / greedy / Brooks / Vizing / 4CT.
This is **not** ostrowski-q (leftover, unassigned). This is **not**
frobenius-real-division Level B / noether-normalization Level B / krenn-gu /
hou-zeng-pfc / sun-135. Do not re-prime the consumed mill. Leave OPE-403
alone.

v1 is the triangle-free / r=3 case only. General `K_r`-free AES is residual.
**Do not label any theorem AES.** C5 is a landmine without `CliqueFree 3`
and without the strict `ℕ` inequality (Level B).

Level A: if G is not `Colorable 2`, there is an odd closed walk; a shortest
one is an induced cycle of length `2k+1 ≥ 5` (no triangles). A vertex
outside the cycle has at most two neighbours on it. **Not** labelled AES.
-/
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import ProofLab.BipartiteOddCycle

set_option maxHeartbeats 800000
set_option linter.unusedVariables false

open Function SimpleGraph

noncomputable section
open Classical

namespace ProofLab.AndrasfaiErdosSos

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## Index / subwalk helpers -/

lemma length_support {u v : V} (p : G.Walk u v) :
    p.support.length = p.length + 1 := by
  induction p with
  | nil => simp
  | cons _ _ ih => simp [Walk.length_cons, ih]

lemma get?_support_eq_getVert {u v : V} (p : G.Walk u v) {n : ℕ}
    (hn : n ≤ p.length) : p.support.get? n = some (p.getVert n) := by
  induction p generalizing n with
  | nil =>
    have hn0 : n = 0 := by simpa [Walk.length_nil] using hn
    subst n
    simp [Walk.getVert_zero]
  | cons h q ih =>
    cases n with
    | zero => simp [Walk.getVert_zero]
    | succ n =>
      simp only [Walk.support_cons, List.get?_cons_succ, Walk.cons_getVert_succ]
      exact ih (Nat.succ_le_succ_iff.mp hn)

lemma getVert_eq_support_get {u v : V} (p : G.Walk u v) {n : ℕ}
    (hn : n < p.support.length) :
    p.support.get ⟨n, hn⟩ = p.getVert n := by
  have hn' : n ≤ p.length := by
    rw [length_support] at hn
    exact Nat.lt_succ_iff.mp hn
  have h := get?_support_eq_getVert (G := G) p hn'
  rw [List.get?_eq_get hn] at h
  exact Option.some_injective _ h

lemma get?_lt_length {α : Type*} {l : List α} {n : ℕ} {x : α}
    (h : l.get? n = some x) : n < l.length := by
  by_contra hle
  have : l.get? n = none := List.get?_eq_none.mpr (Nat.le_of_not_lt hle)
  rw [this] at h
  cases h

lemma exists_duplicate_indices {α : Type*} [DecidableEq α] (x : α) :
    ∀ (l : List α), 1 < l.count x →
      ∃ i j : ℕ, i < j ∧ j < l.length ∧ l.get? i = some x ∧ l.get? j = some x
  | [], h => by simp at h
  | a :: l, h => by
    by_cases ha : a = x
    · have hpos : 0 < l.count x := by
        rw [List.count_cons, if_pos ha.symm] at h
        omega
      have hx : x ∈ l := List.count_pos_iff_mem.mp hpos
      obtain ⟨⟨j, hjlen⟩, hjget⟩ := List.get_of_mem hx
      refine ⟨0, j + 1, Nat.succ_pos _, Nat.succ_lt_succ hjlen, ?_, ?_⟩
      · simp [ha]
      · rw [List.get?_cons_succ, List.get?_eq_get hjlen, hjget]
    · have h' : 1 < l.count x := by
        rw [List.count_cons, if_neg (mt Eq.symm ha)] at h
        exact h
      obtain ⟨i, j, hij, hj, hi, hjx⟩ := exists_duplicate_indices x l h'
      refine ⟨i + 1, j + 1, Nat.succ_lt_succ hij, Nat.succ_lt_succ hj, ?_, ?_⟩
      · simpa [List.get?_cons_succ] using hi
      · simpa [List.get?_cons_succ] using hjx

/-- The subwalk of `p` from index `i` to index `j`. -/
def subwalk {u v : V} :
    ∀ (p : G.Walk u v) (i j : ℕ), i ≤ j → j ≤ p.length →
      G.Walk (p.getVert i) (p.getVert j)
  | .nil, i, j, hij, hj => by
    have hj0 : j = 0 := by simpa [Walk.length_nil] using hj
    have hi0 : i = 0 := by omega
    subst i; subst j
    exact Walk.nil
  | .cons _h _q, 0, 0, _hij, _hj => Walk.nil
  | .cons h q, 0, j + 1, _hij, hj =>
    Walk.cons h
      ((subwalk q 0 j (Nat.zero_le _) (Nat.succ_le_succ_iff.mp hj)).copy
        q.getVert_zero rfl)
  | .cons _h _q, i + 1, 0, hij, _hj =>
    False.elim (Nat.not_succ_le_zero i hij)
  | .cons _h q, i + 1, j + 1, hij, hj =>
    subwalk q i j (Nat.succ_le_succ_iff.mp hij) (Nat.succ_le_succ_iff.mp hj)

lemma length_subwalk {u v : V} :
    ∀ (p : G.Walk u v) (i j : ℕ) (hij : i ≤ j) (hj : j ≤ p.length),
      (subwalk (G := G) p i j hij hj).length = j - i
  | .nil, i, j, hij, hj => by
    have hj0 : j = 0 := by simpa [Walk.length_nil] using hj
    have hi0 : i = 0 := by omega
    subst i; subst j
    simp [subwalk]
  | .cons _h _q, 0, 0, _hij, _hj => by simp [subwalk]
  | .cons h q, 0, j + 1, _hij, hj => by
    simp [subwalk, Walk.length_cons, Walk.length_copy, length_subwalk q 0 j]
  | .cons _h _q, i + 1, 0, hij, _hj =>
    (Nat.not_succ_le_zero i hij).elim
  | .cons _h q, i + 1, j + 1, hij, hj => by
    simp [subwalk, length_subwalk q i j, Nat.succ_sub_succ]

def toClosed {u v : V} (p : G.Walk u v) (i j : ℕ)
    (hij : i ≤ j) (hj : j ≤ p.length) (heq : p.getVert i = p.getVert j) :
    G.Walk (p.getVert i) (p.getVert i) :=
  (subwalk (G := G) p i j hij hj).copy rfl heq.symm

lemma length_toClosed {u v : V} (p : G.Walk u v) (i j : ℕ)
    (hij : i ≤ j) (hj : j ≤ p.length) (heq : p.getVert i = p.getVert j) :
    (toClosed (G := G) p i j hij hj heq).length = j - i := by
  simp [toClosed, length_subwalk]

lemma odd_add_iff {m n : ℕ} (h : Odd (m + n)) : Odd m ↔ ¬ Odd n := by
  simp only [Nat.odd_iff] at h ⊢
  have hm : m % 2 = 0 ∨ m % 2 = 1 := Nat.mod_two_eq_zero_or_one m
  have hn : n % 2 = 0 ∨ n % 2 = 1 := Nat.mod_two_eq_zero_or_one n
  rcases hm with hm | hm <;> rcases hn with hn | hn <;>
    simp [Nat.add_mod, hm, hn] at h ⊢

lemma mem_edges_of_adj_getVert {u v : V} (p : G.Walk u v) {k : ℕ}
    (hk : k < p.length) : s(p.getVert k, p.getVert (k + 1)) ∈ p.edges := by
  induction p generalizing k with
  | nil => simp [Walk.length_nil] at hk
  | cons h q ih =>
    cases k with
    | zero =>
      simp [Walk.getVert_zero, Walk.cons_getVert_succ, Walk.edges_cons, Walk.getVert]
    | succ k =>
      simp only [Walk.edges_cons, Walk.cons_getVert_succ]
      exact List.mem_cons_of_mem _ (ih (Nat.succ_lt_succ_iff.mp hk))

/-! ## Existence of a shortest odd closed walk -/

/-- Reuse the consumed bipartite characterisation. **Not** re-proved. -/
theorem exists_odd_closed_walk_of_not_colorable_two (h : ¬ G.Colorable 2) :
    ∃ (u : V) (p : G.Walk u u), Odd p.length := by
  have hiff := BipartiteOddCycle.colorable_two_iff_no_odd_walk (G := G)
  by_contra hno
  exact h (hiff.mpr fun u p hp => hno ⟨u, p, hp⟩)

theorem exists_shortest_odd_closed_walk (h : ¬ G.Colorable 2) :
    ∃ (u : V) (p : G.Walk u u), Odd p.length ∧
      ∀ ⦃w : V⦄ (q : G.Walk w w), Odd q.length → p.length ≤ q.length := by
  obtain ⟨u0, p0, hp0⟩ := exists_odd_closed_walk_of_not_colorable_two G h
  let P : ℕ → Prop := fun n => ∃ (u : V) (p : G.Walk u u), Odd p.length ∧ p.length = n
  have hP : ∃ n, P n := ⟨p0.length, u0, p0, hp0, rfl⟩
  obtain ⟨u, p, hodd, hlen⟩ := Nat.find_spec hP
  refine ⟨u, p, hodd, ?_⟩
  intro w q hq
  have : P q.length := ⟨w, q, hq, rfl⟩
  simpa [hlen] using Nat.find_min' hP this

/-! ## Shortest odd closed walk is a cycle of length ≥ 5 -/

lemma getVert_of_tail_get? {u : V} {p : G.Walk u u} {i : ℕ} {x : V}
    (h : p.support.tail.get? i = some x) :
    p.getVert (i + 1) = x := by
  have hs : p.support = u :: p.support.tail := p.support_eq_cons
  have hsup : p.support.get? (i + 1) = some x := by
    rw [hs, List.get?_cons_succ]
    exact h
  have hle : i + 1 ≤ p.length := by
    have hlt := get?_lt_length hsup
    rw [length_support] at hlt
    exact Nat.lt_succ_iff.mp hlt
  have hgv := get?_support_eq_getVert (G := G) p hle
  rw [hgv] at hsup
  exact Option.some_injective _ hsup

/-- Complement of the `i..j` subwalk along a closed walk. -/
def complementClosed {u : V} (p : G.Walk u u) (i j : ℕ)
    (hi : i ≤ p.length) (hj : j ≤ p.length) (hij : i ≤ j)
    (heq : p.getVert i = p.getVert j) :
    G.Walk (p.getVert i) (p.getVert i) :=
  let q1 : G.Walk (p.getVert j) u :=
    (subwalk (G := G) p j p.length hj le_rfl).copy rfl p.getVert_length
  let q2 : G.Walk u (p.getVert i) :=
    (subwalk (G := G) p 0 i (Nat.zero_le _) hi).copy p.getVert_zero rfl
  (q1.copy heq.symm rfl).append q2

lemma length_complementClosed {u : V} (p : G.Walk u u) (i j : ℕ)
    (hi : i ≤ p.length) (hj : j ≤ p.length) (hij : i ≤ j)
    (heq : p.getVert i = p.getVert j) :
    (complementClosed (G := G) p i j hi hj hij heq).length = p.length - (j - i) := by
  simp only [complementClosed, Walk.length_append, Walk.length_copy, length_subwalk]
  omega

lemma getVert_injective_of_isPath {u v : V} {p : G.Walk u v} (hp : p.IsPath)
    {i j : ℕ} (hi : i ≤ p.length) (hj : j ≤ p.length)
    (heq : p.getVert i = p.getVert j) : i = j := by
  have hi' : i < p.support.length := by rw [length_support]; omega
  have hj' : j < p.support.length := by rw [length_support]; omega
  have gi : p.support.get? i = some (p.getVert i) :=
    get?_support_eq_getVert (G := G) p hi
  have gj : p.support.get? j = some (p.getVert j) :=
    get?_support_eq_getVert (G := G) p hj
  by_cases hij : i = j
  · exact hij
  · rcases Nat.lt_or_gt_of_ne hij with h | h
    · have hne :=
        (List.nodup_iff_get?_ne_get?.mp hp.support_nodup) i j h hj'
      exact (hne (by rw [gi, gj, heq])).elim
    · have hne :=
        (List.nodup_iff_get?_ne_get?.mp hp.support_nodup) j i h hi'
      exact (hne (by rw [gj, gi, heq])).elim

lemma exists_getVert_of_mem_edges {u v : V} {p : G.Walk u v} {x y : V}
    (h : s(x, y) ∈ p.edges) :
    ∃ k, k < p.length ∧
      (p.getVert k = x ∧ p.getVert (k + 1) = y ∨
        p.getVert k = y ∧ p.getVert (k + 1) = x) := by
  induction p with
  | nil =>
    simp [Walk.edges] at h
  | cons hadj q ih =>
    simp only [Walk.edges_cons, List.mem_cons] at h
    rcases h with h | h
    · refine ⟨0, Nat.succ_pos _, ?_⟩
      have h1 : (Walk.cons hadj q).getVert 0 = (by exact (Walk.cons hadj q).getVert 0) := rfl
      -- `hadj : Adj a b` and `q : Walk b c`; the first edge is `s(a, b)`.
      rw [Walk.getVert_zero, Walk.cons_getVert_succ, Walk.getVert_zero]
      rw [Sym2.eq_iff] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
    · obtain ⟨k, hk, hk'⟩ := ih h
      refine ⟨k + 1, Nat.succ_lt_succ hk, ?_⟩
      simpa [Walk.cons_getVert_succ] using hk'

theorem isCycle_of_shortest_odd_closed_walk {u : V} {p : G.Walk u u}
    (hodd : Odd p.length)
    (hmin : ∀ ⦃w : V⦄ (q : G.Walk w w), Odd q.length → p.length ≤ q.length) :
    p.IsCycle := by
  have htail : p.support.tail.Nodup := by
    by_contra hrep
    have hcnt : ∃ x, 1 < p.support.tail.count x := by
      rw [List.nodup_iff_count_le_one] at hrep
      push_neg at hrep
      exact hrep
    obtain ⟨x, hxc⟩ := hcnt
    obtain ⟨i', j', hij', hj', hi', hjx'⟩ := exists_duplicate_indices x p.support.tail hxc
    let i := i' + 1
    let j := j' + 1
    have hij : i < j := Nat.succ_lt_succ hij'
    have htaillen : p.support.tail.length = p.length := by
      have hlen := length_support (G := G) p
      rw [Walk.support_eq_cons p, List.length_cons] at hlen
      omega
    have hj_le : j ≤ p.length := by
      have : j' < p.support.tail.length := hj'
      omega
    have hi_le : i ≤ p.length := le_trans (le_of_lt hij) hj_le
    have gi : p.getVert i = x := getVert_of_tail_get? (G := G) hi'
    have gj : p.getVert j = x := getVert_of_tail_get? (G := G) hjx'
    have heq : p.getVert i = p.getVert j := by rw [gi, gj]
    have hij_le : i ≤ j := le_of_lt hij
    have hlt : j - i < p.length := by
      have : 1 ≤ i := Nat.succ_pos _
      omega
    let q := toClosed (G := G) p i j hij_le hj_le heq
    have hqlen : q.length = j - i := length_toClosed (G := G) p i j hij_le hj_le heq
    by_cases hodq : Odd q.length
    · have := hmin q (by simpa [hqlen] using hodq)
      omega
    · let r := complementClosed (G := G) p i j hi_le hj_le hij_le heq
      have hrlen : r.length = p.length - (j - i) :=
        length_complementClosed (G := G) p i j hi_le hj_le hij_le heq
      have hsum' : (p.length - (j - i)) + (j - i) = p.length := by omega
      have hsumodd : Odd ((p.length - (j - i)) + (j - i)) := by simpa [hsum'] using hodd
      have hrodd : Odd r.length := by
        have hn : ¬ Odd (j - i) := by simpa [hqlen] using hodq
        simpa [hrlen] using
          (odd_add_iff (m := p.length - (j - i)) (n := j - i) hsumodd).mpr hn
      have := hmin r hrodd
      omega
  cases p with
  | nil =>
    simp [Walk.length_nil] at hodd
  | cons h q =>
    rw [Walk.cons_isCycle_iff]
    have hqpath : q.IsPath := Walk.IsPath.mk' (by simpa [Walk.support_cons] using htail)
    refine ⟨hqpath, ?_⟩
    intro hedge
    obtain ⟨k, hk, hk'⟩ := exists_getVert_of_mem_edges (p := q) hedge
    have hqlen1 : q.length = 1 := by
      have hk0 : k ≤ q.length := le_of_lt hk
      have hk1 : k + 1 ≤ q.length := Nat.succ_le_of_lt hk
      rcases hk' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hk_eq : k = q.length :=
          getVert_injective_of_isPath (G := G) hqpath hk0 le_rfl
            (by rw [h1, q.getVert_length])
        omega
      · have hk_eq : k = 0 :=
          getVert_injective_of_isPath (G := G) hqpath hk0 (Nat.zero_le q.length)
            (by rw [h1, q.getVert_zero])
        have hlen : k + 1 = q.length :=
          getVert_injective_of_isPath (G := G) hqpath hk1 le_rfl
            (by rw [h2, q.getVert_length])
        omega
    simp [Walk.length_cons, hqlen1, Nat.odd_iff] at hodd

lemma not_length_three_of_cliqueFree {u : V} {p : G.Walk u u}
    (h3 : G.CliqueFree 3) (hc : p.IsCycle) : p.length ≠ 3 := by
  intro hlen
  obtain ⟨s, hs⟩ :=
    (is3Clique_iff_exists_cycle_length_three (G := G)).mpr ⟨u, p, hc, hlen⟩
  exact h3 s hs

/-- Triangle-free shortest odd closed walk has length ≥ 5. Not labelled AES. -/
theorem five_le_length_of_odd_cycle (h3 : G.CliqueFree 3)
    {u : V} {p : G.Walk u u} (hodd : Odd p.length) (hc : p.IsCycle) :
    5 ≤ p.length := by
  have hge := Walk.IsCycle.three_le_length hc
  have hne : p.length ≠ 3 := not_length_three_of_cliqueFree G h3 hc
  have : p.length % 2 = 1 := Nat.odd_iff.mp hodd
  omega

/-- Level A glue (not labelled AES): a non-2-colourable triangle-free finite
graph has a shortest odd closed walk that is a cycle of length ≥ 5.

Induced (no chords) and “off-cycle vertex has ≤ 2 neighbours on the cycle”
are the companion Level A theorems below. Level B namesake
`andrasfai_erdos_sos` (`5 * minDegree > 3 * n ⇒ Colorable 2`) is **out of
this ticket** and is **not** sorry-ed. -/
theorem shortest_odd_cycle_glue (h3 : G.CliqueFree 3) (h : ¬ G.Colorable 2) :
    ∃ (u : V) (p : G.Walk u u),
      Odd p.length ∧ 5 ≤ p.length ∧ p.IsCycle := by
  obtain ⟨u, p, hodd, hmin⟩ := exists_shortest_odd_closed_walk G h
  have hc : p.IsCycle := isCycle_of_shortest_odd_closed_walk G hodd hmin
  exact ⟨u, p, hodd, five_le_length_of_odd_cycle G h3 hodd hc, hc⟩

/-! ## Induced cycle (no chords) -/

lemma get?_tail_eq_getVert {u : V} (p : G.Walk u u) {k : ℕ}
    (hk : k < p.length) :
    p.support.tail.get? k = some (p.getVert (k + 1)) := by
  have hs : p.support = u :: p.support.tail := p.support_eq_cons
  have hsup : p.support.get? (k + 1) = some (p.getVert (k + 1)) :=
    get?_support_eq_getVert (G := G) p (Nat.succ_le_of_lt hk)
  rwa [hs, List.get?_cons_succ] at hsup

lemma tail_length_eq {u : V} (p : G.Walk u u) :
    p.support.tail.length = p.length := by
  have h := length_support (G := G) p
  rw [Walk.support_eq_cons p, List.length_cons] at h
  omega

lemma getVert_injective_of_isCycle {u : V} {p : G.Walk u u} (hc : p.IsCycle)
    {i j : ℕ} (hi : i < p.length) (hj : j < p.length)
    (heq : p.getVert i = p.getVert j) : i = j := by
  wlog hle : i ≤ j generalizing i j
  · exact (this hj hi heq.symm (le_of_not_le hle)).symm
  rcases lt_or_eq_of_le hle with hlt | rfl
  · have htail := hc.support_nodup
    have hlen := tail_length_eq (G := G) p
    by_cases hi0 : i = 0
    · subst i
      have hjpos : 0 < j := hlt
      have gj : p.support.tail.get? (j - 1) = some (p.getVert j) := by
        have h1 : j - 1 < p.length := by omega
        have hgv := get?_tail_eq_getVert (G := G) p h1
        have hj1 : j - 1 + 1 = j := by omega
        rwa [hj1] at hgv
      have hnpos : 0 < p.length := lt_of_le_of_lt (Nat.zero_le j) hj
      have gn : p.support.tail.get? (p.length - 1) = some u := by
        have h1 : p.length - 1 < p.length := by omega
        have hgv := get?_tail_eq_getVert (G := G) p h1
        have hn1 : p.length - 1 + 1 = p.length := by omega
        rwa [hn1, Walk.getVert_length] at hgv
      have hix : j - 1 < p.length - 1 := by omega
      have hjlen : p.length - 1 < p.support.tail.length := by omega
      have hne := (List.nodup_iff_get?_ne_get?.mp htail) (j - 1) (p.length - 1) hix hjlen
      have : p.getVert j = u := by simpa [Walk.getVert_zero] using heq.symm
      exact (hne (by rw [gj, gn, this])).elim
    · have gi : p.support.tail.get? (i - 1) = some (p.getVert i) := by
        have h1 : i - 1 < p.length := by omega
        have hgv := get?_tail_eq_getVert (G := G) p h1
        have hi1 : i - 1 + 1 = i := by omega
        rwa [hi1] at hgv
      have gj : p.support.tail.get? (j - 1) = some (p.getVert j) := by
        have h1 : j - 1 < p.length := by omega
        have hgv := get?_tail_eq_getVert (G := G) p h1
        have hj1 : j - 1 + 1 = j := by omega
        rwa [hj1] at hgv
      have hix : i - 1 < j - 1 := by omega
      have hjlen : j - 1 < p.support.tail.length := by omega
      have hne := (List.nodup_iff_get?_ne_get?.mp htail) (i - 1) (j - 1) hix hjlen
      exact (hne (by rw [gi, gj, heq])).elim
  · rfl

/-- Close a walk `i → j` along `p` with the reverse of a chord. -/
def chordShort {u : V} (p : G.Walk u u) (i j : ℕ)
    (hij : i ≤ j) (hj : j ≤ p.length)
    (h : G.Adj (p.getVert j) (p.getVert i)) :
    G.Walk (p.getVert i) (p.getVert i) :=
  (subwalk (G := G) p i j hij hj).concat h

lemma length_chordShort {u : V} (p : G.Walk u u) (i j : ℕ)
    (hij : i ≤ j) (hj : j ≤ p.length)
    (h : G.Adj (p.getVert j) (p.getVert i)) :
    (chordShort (G := G) p i j hij hj h).length = j - i + 1 := by
  simp [chordShort, Walk.length_concat, length_subwalk]

/-- Close the complementary arc `j → u → i` with the chord `i → j`. -/
def chordLong {u : V} (p : G.Walk u u) (i j : ℕ)
    (hi : i ≤ p.length) (hj : j ≤ p.length)
    (h : G.Adj (p.getVert i) (p.getVert j)) :
    G.Walk (p.getVert j) (p.getVert j) :=
  let q1 : G.Walk (p.getVert j) u :=
    (subwalk (G := G) p j p.length hj le_rfl).copy rfl p.getVert_length
  let q2 : G.Walk u (p.getVert i) :=
    (subwalk (G := G) p 0 i (Nat.zero_le _) hi).copy p.getVert_zero rfl
  (q1.append q2).concat h

lemma length_chordLong {u : V} (p : G.Walk u u) (i j : ℕ)
    (hi : i ≤ p.length) (hj : j ≤ p.length) (hij : i ≤ j)
    (h : G.Adj (p.getVert i) (p.getVert j)) :
    (chordLong (G := G) p i j hi hj h).length = p.length - (j - i) + 1 := by
  simp only [chordLong, Walk.length_concat, Walk.length_append, Walk.length_copy, length_subwalk]
  have : i ≤ p.length := hi
  omega

/-- Consecutive on the cycle, including the wrap-around edge. -/
def consecutiveOnCycle {u : V} (p : G.Walk u u) (i j : ℕ) : Prop :=
  j = i + 1 ∨ (i = 0 ∧ j + 1 = p.length)

/-- Level A (not labelled AES): a shortest odd closed walk that is a cycle
has no chords. -/
theorem no_chord_of_shortest_odd_closed_walk {u : V} {p : G.Walk u u}
    (hodd : Odd p.length)
    (hmin : ∀ ⦃w : V⦄ (q : G.Walk w w), Odd q.length → p.length ≤ q.length)
    {i j : ℕ} (hi : i < p.length) (hj : j < p.length) (hij : i < j)
    (hadj : G.Adj (p.getVert i) (p.getVert j)) :
    consecutiveOnCycle (G := G) p i j := by
  by_contra hcons
  unfold consecutiveOnCycle at hcons
  push_neg at hcons
  have hij_le : i ≤ j := le_of_lt hij
  have hj_le : j ≤ p.length := le_of_lt hj
  have hi_le : i ≤ p.length := le_of_lt hi
  have hgap : 2 ≤ j - i := by omega
  have hgap' : j - i ≤ p.length - 2 := by
    have : j + 1 ≠ p.length ∨ i ≠ 0 := by tauto
    omega
  have hn2 : 2 ≤ p.length := by omega
  let q := chordShort (G := G) p i j hij_le hj_le (G.adj_symm hadj)
  let r := chordLong (G := G) p i j hi_le hj_le hadj
  have hqlen : q.length = j - i + 1 := length_chordShort (G := G) p i j hij_le hj_le _
  have hrlen : r.length = p.length - (j - i) + 1 :=
    length_chordLong (G := G) p i j hi_le hj_le hij_le hadj
  have hsum : q.length + r.length = p.length + 2 := by omega
  have hql : q.length < p.length := by omega
  have hrl : r.length < p.length := by omega
  have hsumodd : Odd (q.length + r.length) := by
    have : p.length + 2 = q.length + r.length := by omega
    simpa [this] using (Odd.add_even hodd (⟨1, rfl⟩ : Even 2))
  by_cases hodq : Odd q.length
  · have := hmin q hodq
    omega
  · have hrodd : Odd r.length := by
      simpa using (odd_add_iff (m := r.length) (n := q.length)
        (by simpa [Nat.add_comm] using hsumodd)).mpr hodq
    have := hmin r hrodd
    omega

/-! ## Off-cycle vertex has ≤ 2 neighbours on the cycle -/

/-- Indices `0 .. length-1` of neighbours of `x` on a closed walk. -/
def cycleNeighborIndices {u : V} (p : G.Walk u u) (x : V) : Finset ℕ :=
  (Finset.range p.length).filter (fun i => G.Adj x (p.getVert i))

lemma mem_cycleNeighborIndices {u : V} {p : G.Walk u u} {x : V} {i : ℕ} :
    i ∈ cycleNeighborIndices (G := G) p x ↔
      i < p.length ∧ G.Adj x (p.getVert i) := by
  simp [cycleNeighborIndices]

lemma getVert_mem_support {u v : V} (p : G.Walk u v) {n : ℕ}
    (hn : n ≤ p.length) : p.getVert n ∈ p.support :=
  (Walk.mem_support_iff_exists_getVert).mpr ⟨n, rfl, hn⟩

/-- Two consecutive neighbours of an off-cycle vertex would form a triangle. -/
lemma not_consecutive_neighbors_of_cliqueFree (h3 : G.CliqueFree 3)
    {u : V} {p : G.Walk u u} (hc : p.IsCycle) {x : V}
    (hx : x ∉ p.support) {i j : ℕ}
    (hi : i < p.length) (hj : j < p.length) (hij : i < j)
    (hxi : G.Adj x (p.getVert i)) (hxj : G.Adj x (p.getVert j)) :
    ¬ consecutiveOnCycle (G := G) p i j := by
  intro hcons
  have hadj_ij : G.Adj (p.getVert i) (p.getVert j) := by
    rcases hcons with h | ⟨hi0, hjn⟩
    · subst j
      exact Walk.adj_getVert_succ p (by omega)
    · subst i
      have hnpos : 0 < p.length := lt_of_le_of_lt (Nat.zero_le j) hj
      have : j = p.length - 1 := by omega
      subst j
      have := Walk.adj_getVert_succ p (Nat.sub_lt hnpos (by decide : (0 : ℕ) < 1))
      simpa [Walk.getVert_length, Nat.sub_add_cancel hnpos, Walk.getVert_zero] using this.symm
  have hne_ij : p.getVert i ≠ p.getVert j := by
    intro heq
    exact (Nat.ne_of_lt hij) (getVert_injective_of_isCycle (G := G) hc hi hj heq)
  have hxi_ne : x ≠ p.getVert i := by
    intro h
    subst h
    exact hx (getVert_mem_support (G := G) p (le_of_lt hi))
  have hxj_ne : x ≠ p.getVert j := by
    intro h
    subst h
    exact hx (getVert_mem_support (G := G) p (le_of_lt hj))
  have hcl : G.IsNClique 3 ({x, p.getVert i, p.getVert j} : Finset V) :=
    is3Clique_triple_iff.mpr ⟨hxi, hxj, hadj_ij⟩
  exact h3 _ hcl

/-- Walk `x → v_i → … → v_j → x`. -/
def viaOffVertex {u : V} (p : G.Walk u u) (x : V) (i j : ℕ)
    (hij : i ≤ j) (hj : j ≤ p.length)
    (hxi : G.Adj x (p.getVert i)) (hxj : G.Adj (p.getVert j) x) :
    G.Walk x x :=
  (Walk.cons hxi (subwalk (G := G) p i j hij hj)).concat hxj

lemma length_viaOffVertex {u : V} (p : G.Walk u u) (x : V) (i j : ℕ)
    (hij : i ≤ j) (hj : j ≤ p.length)
    (hxi : G.Adj x (p.getVert i)) (hxj : G.Adj (p.getVert j) x) :
    (viaOffVertex (G := G) p x i j hij hj hxi hxj).length = j - i + 2 := by
  simp [viaOffVertex, Walk.length_concat, Walk.length_cons, length_subwalk]

/-- Walk `x → v_j → … → u → … → v_i → x` (wrap-around arc). -/
def viaOffVertexWrap {u : V} (p : G.Walk u u) (x : V) (i j : ℕ)
    (hi : i ≤ p.length) (hj : j ≤ p.length)
    (hxj : G.Adj x (p.getVert j)) (hxi : G.Adj (p.getVert i) x) :
    G.Walk x x :=
  let q1 : G.Walk (p.getVert j) u :=
    (subwalk (G := G) p j p.length hj le_rfl).copy rfl p.getVert_length
  let q2 : G.Walk u (p.getVert i) :=
    (subwalk (G := G) p 0 i (Nat.zero_le _) hi).copy p.getVert_zero rfl
  (Walk.cons hxj (q1.append q2)).concat hxi

lemma length_viaOffVertexWrap {u : V} (p : G.Walk u u) (x : V) (i j : ℕ)
    (hi : i ≤ p.length) (hj : j ≤ p.length) (hij : i ≤ j)
    (hxj : G.Adj x (p.getVert j)) (hxi : G.Adj (p.getVert i) x) :
    (viaOffVertexWrap (G := G) p x i j hi hj hxj hxi).length =
      p.length - (j - i) + 2 := by
  simp only [viaOffVertexWrap, Walk.length_concat, Walk.length_cons, Walk.length_append,
    Walk.length_copy, length_subwalk]
  omega

lemma odd_add_two {n : ℕ} (h : Odd n) : Odd (n + 2) :=
  Odd.add_even h ⟨1, rfl⟩

/-- Level A (not labelled AES): an off-cycle vertex has at most two
neighbours on a shortest odd cycle of a triangle-free graph. -/
theorem neighbor_indices_card_le_two (h3 : G.CliqueFree 3)
    {u : V} {p : G.Walk u u}
    (hodd : Odd p.length)
    (hmin : ∀ ⦃w : V⦄ (q : G.Walk w w), Odd q.length → p.length ≤ q.length)
    (hc : p.IsCycle) {x : V} (hx : x ∉ p.support) :
    (cycleNeighborIndices (G := G) p x).card ≤ 2 := by
  set s := cycleNeighborIndices (G := G) p x
  by_contra hcard
  have h3le : 3 ≤ s.card := Nat.succ_le_of_lt (lt_of_not_ge (by exact hcard))
  have hsne : s.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le (by decide : (0 : ℕ) < 3) h3le)
  let a := s.min' hsne
  have ha : a ∈ s := Finset.min'_mem _ _
  have herase : (s.erase a).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hem
    have : s.card = 1 := by
      have := Finset.card_erase_of_mem ha
      rw [hem, Finset.card_empty] at this
      omega
    omega
  let b := (s.erase a).min' herase
  have hb' : b ∈ s.erase a := Finset.min'_mem _ _
  have hb : b ∈ s := Finset.mem_of_mem_erase hb'
  have herase2 : ((s.erase a).erase b).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hem
    have hca : (s.erase a).card = s.card - 1 := Finset.card_erase_of_mem ha
    have hcb : ((s.erase a).erase b).card = (s.erase a).card - 1 :=
      Finset.card_erase_of_mem hb'
    rw [hem, Finset.card_empty] at hcb
    omega
  let c := ((s.erase a).erase b).min' herase2
  have hc' : c ∈ (s.erase a).erase b := Finset.min'_mem _ _
  have hcmem : c ∈ s := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hc')
  have hab : a < b := Finset.min'_lt_of_mem_erase_min' (H := hsne) hb'
  have hbc : b < c := by
    change (s.erase a).min' herase < c
    exact Finset.min'_lt_of_mem_erase_min' (H := herase) hc'
  have hac : a < c := Nat.lt_trans hab hbc
  have ha_mem := (mem_cycleNeighborIndices (G := G) (p := p) (x := x) (i := a)).mp ha
  have hb_mem := (mem_cycleNeighborIndices (G := G) (p := p) (x := x) (i := b)).mp hb
  have hc_mem := (mem_cycleNeighborIndices (G := G) (p := p) (x := x) (i := c)).mp hcmem
  have hncons_ab : ¬ consecutiveOnCycle (G := G) p a b :=
    not_consecutive_neighbors_of_cliqueFree (G := G) h3 hc hx ha_mem.1 hb_mem.1 hab
      ha_mem.2 hb_mem.2
  have hncons_bc : ¬ consecutiveOnCycle (G := G) p b c :=
    not_consecutive_neighbors_of_cliqueFree (G := G) h3 hc hx hb_mem.1 hc_mem.1 hbc
      hb_mem.2 hc_mem.2
  have hncons_ac : ¬ consecutiveOnCycle (G := G) p a c :=
    not_consecutive_neighbors_of_cliqueFree (G := G) h3 hc hx ha_mem.1 hc_mem.1 hac
      ha_mem.2 hc_mem.2
  have hgap_ab : 2 ≤ b - a := by
    unfold consecutiveOnCycle at hncons_ab
    omega
  have hgap_bc : 2 ≤ c - b := by
    unfold consecutiveOnCycle at hncons_bc
    omega
  have hgap_ca : 2 ≤ a + p.length - c := by
    unfold consecutiveOnCycle at hncons_ac
    omega
  have hsum : (b - a) + (c - b) + (a + p.length - c) = p.length := by omega
  have hodd_sum : Odd ((b - a) + (c - b) + (a + p.length - c)) := by simpa [hsum] using hodd
  have hi_le_a : a ≤ p.length := le_of_lt ha_mem.1
  have hj_le_b : b ≤ p.length := le_of_lt hb_mem.1
  have hj_le_c : c ≤ p.length := le_of_lt hc_mem.1
  have hcase : Odd (b - a) ∨ Odd (c - b) ∨ Odd (a + p.length - c) := by
    by_contra hno
    push_neg at hno
    have h1 : (b - a) % 2 = 0 := Nat.not_odd_iff.mp hno.1
    have h2 : (c - b) % 2 = 0 := Nat.not_odd_iff.mp hno.2.1
    have h3e : (a + p.length - c) % 2 = 0 := Nat.not_odd_iff.mp hno.2.2
    have hsum0 : ((b - a) + (c - b) + (a + p.length - c)) % 2 = 0 := by omega
    exact Nat.not_odd_iff.mpr hsum0 hodd_sum
  rcases hcase with hodd_ab | hodd_bc | hodd_ca
  · let q := viaOffVertex (G := G) p x a b (le_of_lt hab) hj_le_b ha_mem.2 (G.adj_symm hb_mem.2)
    have hqlen : q.length = b - a + 2 := length_viaOffVertex (G := G) p x a b _ _ _ _
    have hodq : Odd q.length := by simpa [hqlen] using odd_add_two hodd_ab
    have hql : q.length < p.length := by omega
    have := hmin q hodq
    omega
  · let q := viaOffVertex (G := G) p x b c (le_of_lt hbc) hj_le_c hb_mem.2 (G.adj_symm hc_mem.2)
    have hqlen : q.length = c - b + 2 := length_viaOffVertex (G := G) p x b c _ _ _ _
    have hodq : Odd q.length := by simpa [hqlen] using odd_add_two hodd_bc
    have hql : q.length < p.length := by omega
    have := hmin q hodq
    omega
  · let q := viaOffVertexWrap (G := G) p x a c hi_le_a hj_le_c hc_mem.2 (G.adj_symm ha_mem.2)
    have hqlen : q.length = p.length - (c - a) + 2 :=
      length_viaOffVertexWrap (G := G) p x a c hi_le_a hj_le_c (le_of_lt hac) _ _
    have harc : a + p.length - c = p.length - (c - a) := by omega
    have hodq : Odd q.length := by
      simpa [hqlen, harc] using odd_add_two hodd_ca
    have hql : q.length < p.length := by omega
    have := hmin q hodq
    omega

/-- Packaged Level A (not labelled AES): shortest odd closed walk is an
induced cycle of length ≥ 5, and every off-cycle vertex has ≤ 2 neighbours
on it.

Level B namesake `andrasfai_erdos_sos` (`5 * minDegree > 3 * n ⇒ Colorable 2`)
is **out of this ticket**, not sorry-ed. -/
theorem shortest_odd_induced_cycle_glue (h3 : G.CliqueFree 3)
    (h : ¬ G.Colorable 2) :
    ∃ (u : V) (p : G.Walk u u),
      Odd p.length ∧ 5 ≤ p.length ∧ p.IsCycle ∧
      (∀ {i j : ℕ}, i < p.length → j < p.length → i < j →
        G.Adj (p.getVert i) (p.getVert j) → consecutiveOnCycle (G := G) p i j) ∧
      (∀ x : V, x ∉ p.support →
        (cycleNeighborIndices (G := G) p x).card ≤ 2) := by
  obtain ⟨u, p, hodd, hmin⟩ := exists_shortest_odd_closed_walk G h
  have hc : p.IsCycle := isCycle_of_shortest_odd_closed_walk G hodd hmin
  refine ⟨u, p, hodd, five_le_length_of_odd_cycle G h3 hodd hc, hc, ?_, ?_⟩
  · intro i j hi hj hij hadj
    exact no_chord_of_shortest_odd_closed_walk (G := G) hodd hmin hi hj hij hadj
  · intro x hx
    exact neighbor_indices_card_le_two (G := G) h3 hodd hmin hc hx

end ProofLab.AndrasfaiErdosSos
