/-
Symmetric Lovász Local Lemma, finite uniform counting 4d form (formalize-only).

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 has `Fintype.card` / `Finset.card` / `Finset.biUnion`,
`SimpleGraph.degree` / `Adj`, and (optional, unused here) `condCount` /
`iIndepSet`. ZERO Lovász Local Lemma / `LocalLemma` theorem under
`Mathlib/` or `Archive/` (Jacobian.lean "Local lemmas" is a section title,
not LLL). Completing the namesake is the gap.

Pin: `catalog/problems/lovasz-local-lemma/STATEMENT.md` (OPE-810;
Scout OPE-804 prime; Director OPE-809). Encoding: finite `Ω`,
`B : ι → Finset Ω`, dependency `SimpleGraph ι`, counting `IndepOfOthers`.
v1 is the ℕ-friendly `4d` form, not `e(d+1)p`. Zero `sorry`.
Do not import `Archive.*`.

This is **not** Chernoff (`measure_ge_le_exp_cgf` / `measure_ge_le_exp_mul_mgf`
already Mathlib — do not re-prove; never cite as this gap).
This is **not** Markov / Chebyshev (`ChebyshevMarkov.lean`).
This is **not** Borel–Cantelli (`Probability/BorelCantelli.lean`).
This is **not** Azuma / Hoeffding / McDiarmid (out of v1).
This is **not** a general MeasureTheory LLL (counting form only).
This is **not** a Ramsey / Schur / VdW application (those are consumed
ProofLab theorems).
This is **not** lopsided LLL / Shearer / Moser–Tardos / algorithmic LLL.
This is **not** vosper / heron / euclid-euler / bipartite-odd-cycle /
moore / stirling / KST / pentagonal / sunflower / CNS / Kruskal–Katona /
Oddtown / Cayley / Mycielski / Friendship / Havel / Menger / greedy /
Brooks / Dilworth / Eulerian / König / Dirac / EKR.
Do **not** prove korselt-carmichael.
Leave OPE-403 alone.

Level A `union_bound_complements` / `empty_index` / `independent_complements`
are **not** labelled LLL.
Level B namesake `lovasz_local_lemma` uses the standard inductive
conditional-counting bound `P(B i | ∩_{j∈S} B_j^c) ≤ 2p` under `4 d p ≤ 1`.
`1 ≤ d` is load-bearing. Empty `Ω` makes `∃ ω` false independently of LLL
(`Nonempty Ω` is load-bearing on the namesake and on empty-index glue).

Transcribed classical argument (Erdős–Lovász 1975; Alon–Spencer symmetric
Local Lemma, 4d form). No novelty claim.
-/
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

set_option maxHeartbeats 800000
set_option linter.unusedVariables false
set_option linter.dupNamespace false

open Finset SimpleGraph
open scoped BigOperators

noncomputable section
open Classical

namespace ProofLab.LovaszLocalLemma

variable {ι Ω : Type*}

/-! ## Encoding: counting independence (not MeasureTheory LLL) -/

/-- Mutual independence of bad event `B i` from a family `J` of non-neighbours
of `i`, as a counting identity on finite `Ω`. Not `iIndepSet`. -/
def IndepOfOthers [Fintype Ω] [DecidableEq Ω] [DecidableEq ι]
    (B : ι → Finset Ω) (G : SimpleGraph ι) (i : ι) : Prop :=
  ∀ J : Finset ι, (∀ j ∈ J, ¬ G.Adj i j ∧ j ≠ i) →
    let rest := (univ : Finset Ω).filter (fun ω => ∀ j ∈ J, ω ∉ B j)
    Fintype.card Ω * (B i ∩ rest).card = (B i).card * rest.card

/-- Outcomes avoiding every bad event indexed by `S`. Glue, not namesake. -/
def good [Fintype Ω] [DecidableEq Ω] [DecidableEq ι]
    (B : ι → Finset Ω) (S : Finset ι) : Finset Ω :=
  (univ : Finset Ω).filter (fun ω => ∀ j ∈ S, ω ∉ B j)

lemma mem_good [Fintype Ω] [DecidableEq Ω] [DecidableEq ι]
    {B : ι → Finset Ω} {S : Finset ι} {ω : Ω} :
    ω ∈ good B S ↔ ∀ j ∈ S, ω ∉ B j := by
  simp [good]

lemma good_empty [Fintype Ω] [DecidableEq Ω] [DecidableEq ι]
    (B : ι → Finset Ω) : good B (∅ : Finset ι) = univ := by
  ext ω
  simp [good]

lemma good_mono [Fintype Ω] [DecidableEq Ω] [DecidableEq ι]
    {B : ι → Finset Ω} {S T : Finset ι} (h : S ⊆ T) :
    good B T ⊆ good B S := by
  intro ω hω
  rw [mem_good] at hω ⊢
  exact fun j hj => hω j (h hj)

lemma good_union [Fintype Ω] [DecidableEq Ω] [DecidableEq ι]
    (B : ι → Finset Ω) (S T : Finset ι) :
    good B (S ∪ T) = good B S ∩ good B T := by
  ext ω
  simp only [mem_good, mem_union, mem_inter]
  constructor
  · intro h
    exact ⟨fun j hj => h j (Or.inl hj), fun j hj => h j (Or.inr hj)⟩
  · intro h j hj
    cases hj with
    | inl hj => exact h.1 j hj
    | inr hj => exact h.2 j hj

lemma good_insert [Fintype Ω] [DecidableEq Ω] [DecidableEq ι]
    (B : ι → Finset Ω) {i : ι} {S : Finset ι} (_hi : i ∉ S) :
    good B (insert i S) = good B S \ B i := by
  ext ω
  simp only [mem_good, mem_sdiff, mem_insert]
  constructor
  · intro h
    exact ⟨fun j hj => h j (Or.inr hj), h i (Or.inl rfl)⟩
  · intro h j hj
    rcases hj with rfl | hj
    · exact h.2
    · exact h.1 j hj

lemma good_eq_sdiff_biUnion [Fintype Ω] [DecidableEq Ω] [DecidableEq ι]
    (B : ι → Finset Ω) (S T : Finset ι) :
    good B (S ∪ T) = good B S \ T.biUnion B := by
  ext ω
  simp only [mem_good, mem_sdiff, mem_union, mem_biUnion]
  constructor
  · intro h
    refine ⟨fun j hj => h j (Or.inl hj), ?_⟩
    rintro ⟨j, hjT, hjB⟩
    exact h j (Or.inr hjT) hjB
  · intro h j hj
    rcases hj with hj | hj
    · exact h.1 j hj
    · intro hjB
      exact h.2 ⟨j, hj, hjB⟩

lemma sdiff_eq_sdiff_inter {α : Type*} [DecidableEq α] (s t : Finset α) :
    s \ t = s \ (t ∩ s) := by
  ext x
  simp only [mem_sdiff, mem_inter]
  constructor
  · intro h
    exact ⟨h.1, fun ht => h.2 ht.1⟩
  · intro h
    exact ⟨h.1, fun ht => h.2 ⟨ht, h.1⟩⟩

lemma card_sdiff_eq_card_sub_inter {α : Type*} [DecidableEq α] (s t : Finset α) :
    (s \ t).card = s.card - (t ∩ s).card := by
  rw [sdiff_eq_sdiff_inter, card_sdiff inter_subset_right]

lemma card_good_sdiff_le [Fintype Ω] [DecidableEq Ω] [DecidableEq ι]
    (B : ι → Finset Ω) (S T : Finset ι) :
    (good B S).card - ∑ j ∈ T, (B j ∩ good B S).card ≤ (good B (S ∪ T)).card := by
  have hrew : good B (S ∪ T) = good B S \ T.biUnion B := good_eq_sdiff_biUnion B S T
  rw [hrew, card_sdiff_eq_card_sub_inter]
  have hinter : good B S ∩ T.biUnion B ⊆ T.biUnion (fun j => B j ∩ good B S) := by
    intro ω hω
    obtain ⟨hS, hU⟩ := mem_inter.mp hω
    obtain ⟨j, hjT, hjB⟩ := mem_biUnion.mp hU
    exact mem_biUnion.mpr ⟨j, hjT, mem_inter.mpr ⟨hjB, hS⟩⟩
  have hcap : (good B S ∩ T.biUnion B).card
      ≤ ∑ j ∈ T, (B j ∩ good B S).card :=
    (card_le_card hinter).trans card_biUnion_le
  have hcomm : T.biUnion B ∩ good B S = good B S ∩ T.biUnion B := inter_comm _ _
  rw [hcomm]
  exact Nat.sub_le_sub_left hcap _

lemma indep_rest [Fintype Ω] [DecidableEq Ω] [DecidableEq ι]
    {B : ι → Finset Ω} {G : SimpleGraph ι} {i : ι}
    (hdep : IndepOfOthers B G i) {J : Finset ι}
    (hJ : ∀ j ∈ J, ¬ G.Adj i j ∧ j ≠ i) :
    Fintype.card Ω * (B i ∩ good B J).card = (B i).card * (good B J).card := by
  simpa [good] using hdep J hJ

/-! ## Level A — union bound / empty index / fully independent (not labelled LLL) -/

/-- Union bound: if `∑ |B i| < |Ω|` then some outcome avoids every `B i`.
Uses `card_biUnion_le`. **Not** labelled LLL. -/
theorem union_bound_complements [Fintype ι] [DecidableEq ι] [Fintype Ω] [DecidableEq Ω]
    (B : ι → Finset Ω)
    (h : ∑ i : ι, (B i).card < Fintype.card Ω) :
    ∃ ω : Ω, ∀ i : ι, ω ∉ B i := by
  let U : Finset Ω := (univ : Finset ι).biUnion B
  have hle : U.card ≤ ∑ i : ι, (B i).card := by
    simpa using (card_biUnion_le : U.card ≤ ∑ i ∈ univ, (B i).card)
  have hlt : U.card < Fintype.card Ω := hle.trans_lt h
  have hne : (univ : Finset Ω) \ U ≠ ∅ := by
    intro hempty
    have hsub : (univ : Finset Ω) ⊆ U := (sdiff_eq_empty_iff_subset).1 hempty
    have heq : U = univ := Subset.antisymm (subset_univ _) hsub
    have : U.card = Fintype.card Ω := by simp [heq]
    exact (this ▸ hlt).false
  obtain ⟨ω, hω⟩ := nonempty_iff_ne_empty.mpr hne
  refine ⟨ω, ?_⟩
  intro i hi
  have : ω ∉ U := (mem_sdiff.mp hω).2
  exact this (mem_biUnion.mpr ⟨i, mem_univ i, hi⟩)

/-- Empty index type: any outcome of nonempty `Ω` works. Glue, not LLL. -/
theorem empty_index [Fintype ι] [Fintype Ω] [Nonempty Ω]
    (B : ι → Finset Ω) (hι : Fintype.card ι = 0) :
    ∃ ω : Ω, ∀ i : ι, ω ∉ B i := by
  refine ⟨Classical.arbitrary Ω, ?_⟩
  have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hι
  intro i
  exact isEmptyElim i

lemma bot_not_adj {G : SimpleGraph ι} (hG : G = ⊥) (i j : ι) : ¬ G.Adj i j := by
  subst hG
  simp [bot_adj]

lemma indep_of_bot [Fintype Ω] [DecidableEq Ω] [DecidableEq ι]
    {B : ι → Finset Ω} {G : SimpleGraph ι} {i : ι}
    (hG : G = ⊥) (hdep : IndepOfOthers B G i) {J : Finset ι} (hi : i ∉ J) :
    Fintype.card Ω * (B i ∩ good B J).card = (B i).card * (good B J).card := by
  apply indep_rest hdep
  intro j hj
  exact ⟨bot_not_adj hG i j, ne_of_mem_of_not_mem hj hi⟩

lemma good_insert_card_mul [Fintype Ω] [DecidableEq Ω] [DecidableEq ι]
    {B : ι → Finset Ω} {G : SimpleGraph ι} {i : ι} {S : Finset ι}
    (hG : G = ⊥) (hdep : IndepOfOthers B G i) (hi : i ∉ S) :
    Fintype.card Ω * (good B (insert i S)).card
      = (Fintype.card Ω - (B i).card) * (good B S).card := by
  have hrest := indep_of_bot hG hdep hi
  have hrew : good B (insert i S) = good B S \ B i := good_insert B hi
  have hcard : (good B S \ B i).card = (good B S).card - (B i ∩ good B S).card := by
    rw [card_sdiff_eq_card_sub_inter, inter_comm]
  rw [hrew, hcard, Nat.mul_sub_left_distrib, hrest, Nat.mul_sub_right_distrib]

/-- Fully independent case `G = ⊥`: product of complement ratios is positive
when each `|B i| < |Ω|` and `Ω` is nonempty. **Not** labelled LLL. -/
theorem independent_complements [Fintype ι] [DecidableEq ι] [Fintype Ω] [DecidableEq Ω]
    [Nonempty Ω]
    (B : ι → Finset Ω) (G : SimpleGraph ι)
    (hG : G = ⊥) (hdep : ∀ i, IndepOfOthers B G i)
    (hp : ∀ i, (B i).card < Fintype.card Ω) :
    ∃ ω : Ω, ∀ i : ι, ω ∉ B i := by
  have hΩ : 0 < Fintype.card Ω := Fintype.card_pos
  have hpos : ∀ S : Finset ι, 0 < (good B S).card := by
    intro S
    refine Finset.induction_on S ?empty ?insert
    · simpa [good_empty] using hΩ
    · intro i S hi ih
      have hmul := good_insert_card_mul hG (hdep i) hi
      have hsubpos : 0 < Fintype.card Ω - (B i).card := Nat.sub_pos_of_lt (hp i)
      have hprod : 0 < Fintype.card Ω * (good B (insert i S)).card := by
        rw [hmul]
        exact Nat.mul_pos hsubpos ih
      exact Nat.pos_of_mul_pos_left hprod
  obtain ⟨ω, hω⟩ := card_pos.mp (hpos univ)
  refine ⟨ω, ?_⟩
  intro i
  exact (mem_good.mp hω) i (mem_univ i)

/-! ## Level B — namesake 4d counting LLL -/

variable [Fintype ι] [DecidableEq ι] [Fintype Ω] [DecidableEq Ω]
variable (B : ι → Finset Ω) (G : SimpleGraph ι) {d : ℕ}

lemma neighbor_card_le [DecidableRel G.Adj] {i : ι} {S : Finset ι}
    (hdeg : G.degree i ≤ d) :
    (S ∩ G.neighborFinset i).card ≤ d := by
  have hle : (S ∩ G.neighborFinset i).card ≤ (G.neighborFinset i).card :=
    card_le_card inter_subset_right
  simpa [card_neighborFinset_eq_degree] using hle.trans hdeg

lemma two_mul_card_lt
    (hd : 1 ≤ d) (hp : ∀ i, 4 * d * (B i).card ≤ Fintype.card Ω)
    (i : ι) (hΩ : 0 < Fintype.card Ω) :
    2 * (B i).card < Fintype.card Ω := by
  have h4 : 4 * (B i).card ≤ Fintype.card Ω := by
    calc
      4 * (B i).card = 4 * 1 * (B i).card := by ring
      _ ≤ 4 * d * (B i).card :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4 hd)
      _ ≤ Fintype.card Ω := hp i
  omega

lemma cond_bound [DecidableRel G.Adj]
    (hd : 1 ≤ d) (hdeg : ∀ i, G.degree i ≤ d)
    (hdep : ∀ i, IndepOfOthers B G i)
    (hp : ∀ i, 4 * d * (B i).card ≤ Fintype.card Ω)
    (S : Finset ι) (i : ι) (hi : i ∉ S) :
    Fintype.card Ω * (B i ∩ good B S).card
      ≤ 2 * (B i).card * (good B S).card := by
  induction S using Finset.strongInduction generalizing i with
  | H S ih =>
    by_cases hΩz : Fintype.card Ω = 0
    · simp [hΩz]
    have hΩpos : 0 < Fintype.card Ω := Nat.pos_of_ne_zero hΩz
    set S1 : Finset ι := S ∩ G.neighborFinset i
    set S0 : Finset ι := S \ G.neighborFinset i
    have hSsplit : S = S0 ∪ S1 := by
      ext x
      simp only [S0, S1, mem_union, mem_sdiff, mem_inter]
      constructor
      · intro hx
        by_cases hN : x ∈ G.neighborFinset i
        · exact Or.inr ⟨hx, hN⟩
        · exact Or.inl ⟨hx, hN⟩
      · intro hx
        rcases hx with hx | hx
        · exact hx.1
        · exact hx.1
    have hdisj : Disjoint S0 S1 := disjoint_sdiff_inter S _
    have hS1le : S1.card ≤ d := neighbor_card_le (G := G) (d := d) (hdeg i)
    have hS0indep : ∀ j ∈ S0, ¬ G.Adj i j ∧ j ≠ i := by
      intro j hj
      have hjS : j ∈ S := (mem_sdiff.mp hj).1
      have hjN : j ∉ G.neighborFinset i := (mem_sdiff.mp hj).2
      refine ⟨?_, ne_of_mem_of_not_mem hjS hi⟩
      simpa [mem_neighborFinset] using hjN
    have hindepS0 := indep_rest (hdep i) hS0indep
    have hcap_le : (B i ∩ good B S).card ≤ (B i ∩ good B S0).card := by
      apply card_le_card
      intro ω hω
      have hmono : good B S ⊆ good B S0 := good_mono sdiff_subset
      exact mem_inter.mpr ⟨(mem_inter.mp hω).1, hmono (mem_inter.mp hω).2⟩
    by_cases hS1e : S1 = ∅
    · have hS0eq : S0 = S := by
        ext x
        constructor
        · intro hx; exact (mem_sdiff.mp hx).1
        · intro hx
          refine mem_sdiff.mpr ⟨hx, ?_⟩
          intro hxN
          have : x ∈ S1 := mem_inter.mpr ⟨hx, hxN⟩
          rw [hS1e] at this
          exact (not_mem_empty x) this
      rw [hS0eq] at hindepS0
      have : Fintype.card Ω * (B i ∩ good B S).card = (B i).card * (good B S).card :=
        hindepS0
      rw [this]
      nlinarith
    · have hS1ne : S1.Nonempty := nonempty_iff_ne_empty.mpr hS1e
      have hS0ss : S0 ⊂ S := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨sdiff_subset, ?_⟩
        intro heq
        obtain ⟨j, hj⟩ := hS1ne
        have hjS : j ∈ S := (mem_inter.mp hj).1
        have hjN : j ∈ G.neighborFinset i := (mem_inter.mp hj).2
        have hj0 : j ∈ S0 := by simpa [heq] using hjS
        exact (mem_sdiff.mp hj0).2 hjN
      have hdpos : 0 < d := Nat.succ_le_iff.mp hd
      have h4sum : 4 * ∑ j ∈ S1, (B j).card ≤ Fintype.card Ω := by
        have hterm : ∑ j ∈ S1, 4 * (B j).card * d ≤ ∑ j ∈ S1, Fintype.card Ω := by
          apply sum_le_sum
          intro j _hj
          have : 4 * (B j).card * d = 4 * d * (B j).card := by ring
          rw [this]
          exact hp j
        have hleft : ∑ j ∈ S1, 4 * (B j).card * d
            = (∑ j ∈ S1, 4 * (B j).card) * d := by
          simp [sum_mul]
        have hright : ∑ j ∈ S1, Fintype.card Ω = S1.card * Fintype.card Ω := by
          simp [sum_const, nsmul_eq_mul]
        have hScard : S1.card * Fintype.card Ω ≤ d * Fintype.card Ω :=
          Nat.mul_le_mul_right _ hS1le
        have hmul : (∑ j ∈ S1, 4 * (B j).card) * d ≤ Fintype.card Ω * d := by
          rw [← hleft, mul_comm (Fintype.card Ω)]
          exact hterm.trans (hright.le.trans hScard)
        have hsum4 : (∑ j ∈ S1, 4 * (B j).card) = 4 * ∑ j ∈ S1, (B j).card := by
          simp [← mul_sum]
        rw [hsum4] at hmul
        exact Nat.le_of_mul_le_mul_right hmul hdpos
      have hih : ∀ j ∈ S1,
          Fintype.card Ω * (B j ∩ good B S0).card
            ≤ 2 * (B j).card * (good B S0).card := by
        intro j hj
        have hj0 : j ∉ S0 := fun h => disjoint_left.mp hdisj h hj
        exact ih S0 hS0ss j hj0
      have hsumcap :
          ∑ j ∈ S1, Fintype.card Ω * (B j ∩ good B S0).card
            ≤ ∑ j ∈ S1, 2 * (B j).card * (good B S0).card :=
        sum_le_sum hih
      have hleft :
          ∑ j ∈ S1, Fintype.card Ω * (B j ∩ good B S0).card
            = Fintype.card Ω * ∑ j ∈ S1, (B j ∩ good B S0).card := by
        simp [← mul_sum]
      have hright :
          ∑ j ∈ S1, 2 * (B j).card * (good B S0).card
            = 2 * (∑ j ∈ S1, (B j).card) * (good B S0).card := by
        calc
          ∑ j ∈ S1, 2 * (B j).card * (good B S0).card
              = ∑ j ∈ S1, (2 * (good B S0).card) * (B j).card := by
                refine sum_congr rfl ?_
                intro j _hj
                ring
          _ = (2 * (good B S0).card) * ∑ j ∈ S1, (B j).card := by
                simp [← mul_sum]
          _ = 2 * (∑ j ∈ S1, (B j).card) * (good B S0).card := by ring
      have hsumcap' :
          Fintype.card Ω * ∑ j ∈ S1, (B j ∩ good B S0).card
            ≤ 2 * (∑ j ∈ S1, (B j).card) * (good B S0).card := by
        rw [← hleft, ← hright]
        exact hsumcap
      have h2sum :
          2 * ∑ j ∈ S1, (B j ∩ good B S0).card ≤ (good B S0).card := by
        have hstep :
            Fintype.card Ω * (2 * ∑ j ∈ S1, (B j ∩ good B S0).card)
              ≤ Fintype.card Ω * (good B S0).card := by
          calc
            Fintype.card Ω * (2 * ∑ j ∈ S1, (B j ∩ good B S0).card)
                = 2 * (Fintype.card Ω * ∑ j ∈ S1, (B j ∩ good B S0).card) := by ring
            _ ≤ 2 * (2 * (∑ j ∈ S1, (B j).card) * (good B S0).card) :=
                  Nat.mul_le_mul_left 2 hsumcap'
            _ = (4 * ∑ j ∈ S1, (B j).card) * (good B S0).card := by ring
            _ ≤ Fintype.card Ω * (good B S0).card :=
                  Nat.mul_le_mul_right _ h4sum
        exact Nat.le_of_mul_le_mul_left hstep hΩpos
      have hgoodS : (good B S0).card ≤ 2 * (good B S).card := by
        have hle : (good B S0).card - ∑ j ∈ S1, (B j ∩ good B S0).card
            ≤ (good B S).card := by
          simpa [hSsplit] using card_good_sdiff_le B S0 S1
        have : 2 * ((good B S0).card - ∑ j ∈ S1, (B j ∩ good B S0).card)
            ≤ 2 * (good B S).card := Nat.mul_le_mul_left 2 hle
        have hdist :
            2 * ((good B S0).card - ∑ j ∈ S1, (B j ∩ good B S0).card)
              = 2 * (good B S0).card - 2 * ∑ j ∈ S1, (B j ∩ good B S0).card :=
          Nat.mul_sub_left_distrib _ _ _
        have hle2 : 2 * (good B S0).card - 2 * ∑ j ∈ S1, (B j ∩ good B S0).card
            ≤ 2 * (good B S).card := by
          simpa [hdist] using this
        have hdrop : 2 * (good B S0).card - (good B S0).card
            ≤ 2 * (good B S0).card - 2 * ∑ j ∈ S1, (B j ∩ good B S0).card :=
          Nat.sub_le_sub_left h2sum _
        have hsimp : 2 * (good B S0).card - (good B S0).card = (good B S0).card := by
          omega
        exact (hsimp.symm.trans_le hdrop).trans hle2
      have hLHS : Fintype.card Ω * (B i ∩ good B S).card
          ≤ (B i).card * (good B S0).card :=
        (Nat.mul_le_mul_left (Fintype.card Ω) hcap_le).trans hindepS0.le
      have hRHS : (B i).card * (good B S0).card
          ≤ 2 * (B i).card * (good B S).card := by
        calc
          (B i).card * (good B S0).card
              ≤ (B i).card * (2 * (good B S).card) :=
                Nat.mul_le_mul_left _ hgoodS
          _ = 2 * (B i).card * (good B S).card := by ring
      exact hLHS.trans hRHS

lemma good_card_pos [DecidableRel G.Adj] [Nonempty Ω]
    (hd : 1 ≤ d) (hdeg : ∀ i, G.degree i ≤ d)
    (hdep : ∀ i, IndepOfOthers B G i)
    (hp : ∀ i, 4 * d * (B i).card ≤ Fintype.card Ω)
    (S : Finset ι) : 0 < (good B S).card := by
  have hΩ : 0 < Fintype.card Ω := Fintype.card_pos
  refine Finset.induction_on S ?empty ?insert
  · simpa [good_empty] using hΩ
  · intro i S hi ih
    have hbound := cond_bound (B := B) (G := G) (d := d) hd hdeg hdep hp S i hi
    have hrew : good B (insert i S) = good B S \ B i := good_insert B hi
    have hcard : (good B S \ B i).card
        = (good B S).card - (B i ∩ good B S).card := by
      rw [card_sdiff_eq_card_sub_inter, inter_comm]
    have hmul :
        Fintype.card Ω * (good B (insert i S)).card
          ≥ (Fintype.card Ω - 2 * (B i).card) * (good B S).card := by
      rw [hrew, hcard, Nat.mul_sub_left_distrib]
      have hle : Fintype.card Ω * (B i ∩ good B S).card
          ≤ 2 * (B i).card * (good B S).card := hbound
      have : Fintype.card Ω * (good B S).card
            - 2 * (B i).card * (good B S).card
          ≤ Fintype.card Ω * (good B S).card
            - Fintype.card Ω * (B i ∩ good B S).card :=
        Nat.sub_le_sub_left hle _
      have hr : Fintype.card Ω * (good B S).card
            - 2 * (B i).card * (good B S).card
          = (Fintype.card Ω - 2 * (B i).card) * (good B S).card := by
        rw [Nat.mul_sub_right_distrib]
      exact hr ▸ this
    have hfactor : 0 < Fintype.card Ω - 2 * (B i).card :=
      Nat.sub_pos_of_lt (two_mul_card_lt (B := B) (d := d) hd hp i hΩ)
    have hpos' : 0 < (Fintype.card Ω - 2 * (B i).card) * (good B S).card :=
      Nat.mul_pos hfactor ih
    have : 0 < Fintype.card Ω * (good B (insert i S)).card :=
      lt_of_lt_of_le hpos' hmul
    exact Nat.pos_of_mul_pos_left this

/-- Symmetric Lovász Local Lemma, counting 4d form.
`Nonempty Ω` is load-bearing: empty `Ω` makes `∃ ω` false independently of LLL.
`1 ≤ d` is load-bearing (the 4d form degenerates at `d = 0`). -/
theorem lovasz_local_lemma [Nonempty Ω] [DecidableRel G.Adj]
    (hd : 1 ≤ d) (hdeg : ∀ i, G.degree i ≤ d)
    (hdep : ∀ i, IndepOfOthers B G i)
    (hp : ∀ i, 4 * d * (B i).card ≤ Fintype.card Ω) :
    ∃ ω : Ω, ∀ i : ι, ω ∉ B i := by
  have hpos := good_card_pos (B := B) (G := G) (d := d) hd hdeg hdep hp univ
  obtain ⟨ω, hω⟩ := card_pos.mp hpos
  refine ⟨ω, ?_⟩
  intro i
  exact (mem_good.mp hω) i (mem_univ i)

end ProofLab.LovaszLocalLemma
