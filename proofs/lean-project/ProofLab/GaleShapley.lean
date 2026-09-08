/-
Stable matchings — Level A only (empty / n=1 unique perm /
partner-is-top-choice ⇒ stable / n=2 explicit two-profile cases).
**Not labelled Gale–Shapley.**

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 has `Equiv.Perm` / `Function.Bijective` /
`SimpleGraph.Subgraph.IsMatching` / `completeBipartiteGraph` /
`Fin n` and ZERO named Gale–Shapley / `galeShapley` /
`stableMatching` / `IsStableMatching` / `deferredAcceptance`.
Completing the Level A empty / n=1 / partner-is-top / n=2 glue
is the gap this ticket lands. The Level B namesake `gale_shapley`
(existence via deferred acceptance) is **out of this ticket** and
is **not** sorry-ed. Rural hospitals / man-optimal uniqueness /
strategy-proofness / stable roommates extras are residual of
this id.

Pin: `catalog/problems/gale-shapley/STATEMENT.md` (OPE-1179;
Scout OPE-1173 prime; Director OPE-1178). Encoding: Mathlib
`Equiv.Perm (Fin n)` + bijective rankings. Zero `sorry`.
Do not import `Archive.*`.

This is **not** Hall's marriage theorem
(`Finset.all_card_le_biUnion_card_iff_exists_injective`,
`Combinatorics/Hall/Basic.lean` L116) — already Mathlib;
`K_{n,n}` matching existence is trivial. **USE `Equiv.Perm` as
the matching type; do not re-prove Hall; do not cite as
Gale–Shapley.** This is **not** `SimpleGraph.Subgraph.IsMatching`
(Matching.lean L50) as namesake — already Mathlib; optional
matching language only. This is **not** `completeBipartiteGraph`
(already-in infra). This is **not** `Equiv.Perm.permMatrix`
(BvN glue, #123) — different use of `Equiv.Perm`. This is
**not** Gale–Ryser / transportation (BvN #123 residual;
different Gale). This is **not** König matching ν=τ (consumed).
This is **not** Birkhoff–von Neumann (#123) / Nash–Williams
arboricity (#124). This is **not** assignment / Hungarian /
Shapley–Shubik. This is **not** farey-sequence leftover
(unassigned this tick). Do not re-prime the consumed mill.
Leave OPE-403 alone.

v1 is existence of a stable perfect matching on `Fin n`.
Finite `Fin n` is load-bearing. Completeness of both sides'
rankings (bijective rank functions) is load-bearing.
Incomplete lists / ties are a different theorem. Rank `0` =
most preferred.

Level A: `n = 0` empty permutation, no pair to block. `n = 1`
the unique map is stable. If `μ m` is every man's unique
rank-0 woman and symmetrically, no blocking pair exists.
For `n = 2`, enumerate the (finitely many) bijective ranking
pairs and name a stable `μ`. **Not** labelled Gale–Shapley.

Transcribed classical argument (D. Gale and L. S. Shapley,
*College admissions and the stability of marriage*, Amer.
Math. Monthly 69 (1962) 9–15). Textbook: Knuth, *Stable
Marriage and its Relation to Other Combinatorial Problems*;
Gusfield–Irving, *The Stable Marriage Problem*. Compact
form: Wikipedia *Gale–Shapley algorithm* / *Stable marriage
problem*. Type pin: `Equiv.Perm` / `Fin n` / bijective
rankings. Hall is a different already-in theorem. Gale–Ryser
is a different consumed-mill residual. No novelty claim.
Default no claim.
-/
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

set_option linter.unusedVariables false

open Equiv Function

namespace ProofLab.GaleShapley

/-! ## Encoding: rankings / blocking pairs (not labelled Gale–Shapley) -/

/-- A ranking of `n` partners for each of `n` agents. Value `0` is
most preferred. Completeness (each `rank a` bijective) is
load-bearing for the namesake and is assumed on the `n = 2`
existence theorem. Encoding; **not** labelled Gale–Shapley. -/
abbrev Ranking (n : ℕ) := Fin n → Fin n → Fin n

/-- Agent `a` strictly prefers `x` to `y`. Encoding; **not** labelled
Gale–Shapley. -/
def Prefers {n : ℕ} (rank : Ranking n) (a x y : Fin n) : Prop :=
  rank a x < rank a y

/-- Completeness: every agent ranks every partner, no ties.
Load-bearing; incomplete lists / ties are a different theorem.
Encoding; **not** labelled Gale–Shapley. -/
def IsCompleteRanking {n : ℕ} (rank : Ranking n) : Prop :=
  ∀ a, Function.Bijective (rank a)

/-- Pair `(m, w)` blocks matching `μ`: they are unmatched, the man
prefers `w` to his partner, and the woman prefers `m` to hers.
Encoding; **not** labelled Gale–Shapley. Reuses Mathlib
`Equiv.Perm`; does **not** re-prove Hall / `IsMatching`. -/
def Blocks {n : ℕ} (mRank wRank : Ranking n)
    (μ : Equiv.Perm (Fin n)) (m w : Fin n) : Prop :=
  μ m ≠ w ∧ Prefers mRank m w (μ m) ∧ Prefers wRank w m (μ.symm w)

/-- A matching is stable when it has no blocking pair. Encoding;
**not** labelled Gale–Shapley. -/
def IsStable {n : ℕ} (mRank wRank : Ranking n)
    (μ : Equiv.Perm (Fin n)) : Prop :=
  ∀ m w, ¬ Blocks mRank wRank μ m w

/-! ## Level A: n = 0 empty perm is stable (not labelled Gale–Shapley) -/

/-- Empty index: there is no pair `(m, w)` to block, so every
(unique empty) permutation is stable. Glue; **not** labelled
Gale–Shapley. -/
theorem isStable_fin_zero (mRank wRank : Ranking 0)
    (μ : Equiv.Perm (Fin 0)) : IsStable mRank wRank μ :=
  fun m => Fin.elim0 m

/-! ## Level A: n = 1 unique perm is stable (not labelled Gale–Shapley) -/

/-- `Fin 1` is a subsingleton, so the unique map sends the unique
man to the unique woman and cannot leave an unmatched pair.
Glue; **not** labelled Gale–Shapley. -/
theorem isStable_fin_one (mRank wRank : Ranking 1)
    (μ : Equiv.Perm (Fin 1)) : IsStable mRank wRank μ := by
  intro m w h
  exact h.1 (Subsingleton.elim (μ m) w)

/-- The unique permutation of `Fin 1` is `1`. Glue; **not** labelled
Gale–Shapley. -/
theorem unique_perm_fin_one (μ : Equiv.Perm (Fin 1)) : μ = 1 :=
  Subsingleton.elim _ _

/-! ## Level A: partner-is-top ⇒ stable (not labelled Gale–Shapley) -/

/-- If nobody strictly prefers anyone to their `μ`-partner, then
`μ` has no blocking pair. Either side's "partner is top" already
suffices; both are recorded as in the STATEMENT. Glue; **not**
labelled Gale–Shapley. -/
theorem isStable_of_partner_is_top {n : ℕ}
    (mRank wRank : Ranking n) (μ : Equiv.Perm (Fin n))
    (hm : ∀ m x, ¬ Prefers mRank m x (μ m))
    (hw : ∀ w y, ¬ Prefers wRank w y (μ.symm w)) :
    IsStable mRank wRank μ := by
  intro m w h
  exact hm m w h.2.1

/-- If every man ranks his `μ`-partner `0` (most preferred) and
every woman ranks her `μ`-partner `0`, then `μ` is stable:
a blocking man would need a rank `< 0`. Requires `n > 0` so
that `0 : Fin n` exists; the `n = 0` case is
`isStable_fin_zero`. Glue; **not** labelled Gale–Shapley. -/
theorem isStable_of_rank_zero_partner {n : ℕ} [NeZero n]
    (mRank wRank : Ranking n) (μ : Equiv.Perm (Fin n))
    (hm : ∀ m, mRank m (μ m) = 0)
    (hw : ∀ w, wRank w (μ.symm w) = 0) :
    IsStable mRank wRank μ := by
  refine isStable_of_partner_is_top mRank wRank μ ?_ ?_
  · intro m x hx
    have : mRank m x < (0 : Fin n) := by
      simpa [Prefers, hm m] using hx
    exact Nat.not_lt_zero _ (Fin.lt_def.mp this)
  · intro w y hy
    have : wRank w y < (0 : Fin n) := by
      simpa [Prefers, hw w] using hy
    exact Nat.not_lt_zero _ (Fin.lt_def.mp this)

/-! ## Glue: identity rankings (not labelled Gale–Shapley) -/

/-- Everyone ranks partners by their index (`0` first). Complete
(the identity is bijective). Glue; **not** labelled Gale–Shapley. -/
def idRanking (n : ℕ) : Ranking n := fun _ x => x

lemma isCompleteRanking_idRanking (n : ℕ) :
    IsCompleteRanking (idRanking n) := fun _ => bijective_id

/-- Under identical identity rankings the identity matching is
stable: a blocking pair would need `w < m` and `m < w`.
Explicit profile; **not** labelled Gale–Shapley. -/
theorem isStable_one_idRanking (n : ℕ) :
    IsStable (idRanking n) (idRanking n) (1 : Equiv.Perm (Fin n)) := by
  intro m w h
  exact lt_asymm h.2.1 h.2.2

/-! ## Level A: n = 2 explicit two-profile cases (not labelled Gale–Shapley) -/

lemma blocks_one_fin_two {mRank wRank : Ranking 2} {m w : Fin 2} :
    Blocks mRank wRank (1 : Equiv.Perm (Fin 2)) m w ↔
      m ≠ w ∧ Prefers mRank m w m ∧ Prefers wRank w m w := by
  simp [Blocks]

/-- If the identity matching is unstable on `n = 2`, the
transposition is stable. Asymmetry of `<` on ranks: a pair that
blocks `1` is unmatched under `1` and therefore *matched* under
the swap, and the two possible swap-unmatched pairs each reverse
a preference used to block `1`. Glue; **not** labelled
Gale–Shapley. -/
theorem isStable_swap_of_not_isStable_one (mRank wRank : Ranking 2)
    (h : ¬ IsStable mRank wRank (1 : Equiv.Perm (Fin 2))) :
    IsStable mRank wRank (Equiv.swap (0 : Fin 2) 1) := by
  unfold IsStable at h
  push_neg at h
  obtain ⟨m0, w0, hblk⟩ := h
  have h1 := (blocks_one_fin_two (mRank := mRank) (wRank := wRank)).1 hblk
  intro m w hb
  fin_cases m0 <;> fin_cases w0
  · exact False.elim (h1.1 rfl)
  · -- (0,1) blocks identity: man 0 prefers 1 to 0, woman 1 prefers 0 to 1
    fin_cases m <;> fin_cases w
    · have hmp : Prefers mRank 0 0 1 := by
        simpa [Prefers, Equiv.swap_apply_left] using hb.2.1
      exact lt_asymm h1.2.1 hmp
    · exact hb.1 (Equiv.swap_apply_left _ _)
    · exact hb.1 (Equiv.swap_apply_right _ _)
    · have hwp : Prefers wRank 1 1 0 := by
        simpa [Prefers, Equiv.symm_swap, Equiv.swap_apply_right] using hb.2.2
      exact lt_asymm h1.2.2 hwp
  · -- (1,0) blocks identity: man 1 prefers 0 to 1, woman 0 prefers 1 to 0
    fin_cases m <;> fin_cases w
    · have hwp : Prefers wRank 0 0 1 := by
        simpa [Prefers, Equiv.symm_swap, Equiv.swap_apply_left] using hb.2.2
      exact lt_asymm h1.2.2 hwp
    · exact hb.1 (Equiv.swap_apply_left _ _)
    · exact hb.1 (Equiv.swap_apply_right _ _)
    · have hmp : Prefers mRank 1 1 0 := by
        simpa [Prefers, Equiv.swap_apply_right] using hb.2.1
      exact lt_asymm h1.2.1 hmp
  · exact False.elim (h1.1 rfl)

/-- `n = 2`: every pair of complete (bijective) rankings admits a
stable matching — the identity if it is stable, otherwise the
transposition. Enumerates the two permutations of `Fin 2` and
names a stable `μ`. Completeness is load-bearing (STATEMENT);
the argument uses only asymmetry of rank-`<`. Glue; **not**
labelled Gale–Shapley. -/
theorem exists_stable_fin_two (mRank wRank : Ranking 2)
    (hm : IsCompleteRanking mRank) (hw : IsCompleteRanking wRank) :
    ∃ μ : Equiv.Perm (Fin 2), IsStable mRank wRank μ := by
  classical
  by_cases h : IsStable mRank wRank (1 : Equiv.Perm (Fin 2))
  · exact ⟨1, h⟩
  · exact ⟨Equiv.swap (0 : Fin 2) 1, isStable_swap_of_not_isStable_one mRank wRank h⟩

/-- Explicit `n = 2` profile: identity rankings, identity matching.
Specialises `isStable_one_idRanking`. Glue; **not** labelled
Gale–Shapley. -/
theorem isStable_fin_two_idRanking :
    IsStable (idRanking 2) (idRanking 2) (1 : Equiv.Perm (Fin 2)) :=
  isStable_one_idRanking 2

/-- Everyone on `Fin 2` ranks the *other* index first (`a` ranks
`1-a` at `0` and `a` at `1`). Complete. Glue; **not** labelled
Gale–Shapley. -/
def swapRanking_two : Ranking 2 := fun a x => if x = a then (1 : Fin 2) else 0

lemma isCompleteRanking_swapRanking_two :
    IsCompleteRanking swapRanking_two := by
  intro a
  fin_cases a
  · change Function.Bijective fun x : Fin 2 => if x = 0 then (1 : Fin 2) else 0
    have h : (fun x : Fin 2 => if x = 0 then (1 : Fin 2) else 0) =
        Equiv.swap (0 : Fin 2) 1 := by
      ext x
      fin_cases x <;> simp
    rw [h]
    exact (Equiv.swap (0 : Fin 2) 1).bijective
  · change Function.Bijective fun x : Fin 2 => if x = 1 then (1 : Fin 2) else 0
    have h : (fun x : Fin 2 => if x = 1 then (1 : Fin 2) else 0) =
        id := by
      ext x
      fin_cases x <;> simp
    rw [h]
    exact bijective_id

/-- Explicit `n = 2` crossed profile: every agent ranks the other
index first, so the transposition matches everyone to their unique
rank-0 partner and is stable by `isStable_of_rank_zero_partner`.
Glue; **not** labelled Gale–Shapley. -/
theorem isStable_swap_swapRanking_two :
    IsStable swapRanking_two swapRanking_two (Equiv.swap (0 : Fin 2) 1) := by
  refine isStable_of_rank_zero_partner swapRanking_two swapRanking_two
    (Equiv.swap (0 : Fin 2) 1) ?_ ?_
  · intro m
    fin_cases m <;> simp [swapRanking_two]
  · intro w
    fin_cases w <;> simp [swapRanking_two, Equiv.symm_swap]

/-- Named `n = 2` existence for the two explicit complete profiles
above. Glue; **not** labelled Gale–Shapley. -/
theorem exists_stable_fin_two_idRanking :
    ∃ μ : Equiv.Perm (Fin 2), IsStable (idRanking 2) (idRanking 2) μ :=
  ⟨1, isStable_fin_two_idRanking⟩

theorem exists_stable_fin_two_swapRanking :
    ∃ μ : Equiv.Perm (Fin 2),
      IsStable swapRanking_two swapRanking_two μ :=
  ⟨Equiv.swap (0 : Fin 2) 1, isStable_swap_swapRanking_two⟩

/-
Residual (Level B, **out of this ticket**, not sorry-ed):
  theorem gale_shapley {n : ℕ}
      (mRank wRank : Ranking n)
      (hm : ∀ m, Function.Bijective (mRank m))
      (hw : ∀ w, Function.Bijective (wRank w)) :
      ∃ μ : Equiv.Perm (Fin n), IsStable mRank wRank μ
Deferred acceptance (men propose in rounds; women keep the best
so far; a rejected man never re-proposes to that woman). The
terminal matching is perfect and stable. Do not sorry the
namesake. Rural hospitals / man-optimal uniqueness /
strategy-proofness / stable roommates remain residual of this
id. Do not re-prove Hall / König matching / Gale–Ryser /
permMatrix / birkhoff_von_neumann / nash_williams / farey-sequence.
-/

end ProofLab.GaleShapley
