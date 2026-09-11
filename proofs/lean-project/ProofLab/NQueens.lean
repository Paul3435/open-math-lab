/-
Named small-board placement witnesses — Level A only
(n=2 none / n=3 none / n=4 `[1, 3, 0, 2]`).
**Not labelled n-queens / eight-queens / Gauss.**

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 pin `a719ba5c3115` has `List` / `List.length` /
`GetElem` / `List.Nodup` / `Fin` / `Fin.val` as **infra**. ZERO named
`nQueens` / `NQueens` / `n_queens` / `eightQueens` / `EightQueens` /
`isQueens` / `queens_problem` / `eight_queens` under `Mathlib/` or
`Archive/` or `ProofLab/` (this run; the only `queen` hit is
“Queen Mary University” in a comment). Completing the Level A named
small-board witnesses is the gap this ticket lands. The Level B
namesake `n_queens` (exists iff `n ≠ 2, 3`) is **out of this ticket**
and is **not** sorry-ed. Solution-count 92 / completion / uniqueness /
toroidal extras are residual of this id. Do **not** label theorems
`nQueens` / `eightQueens` / `isQueens` / `langford_*` / `gray_*` /
`latin_*` as the namesake.

Pin: `catalog/problems/n-queens/STATEMENT.md`
(OPE-1424; Scout OPE-1419 RECOMMENDED PRIME; Director OPE-1423 APPROVE).
Encoding: `IsNQueens` via Mathlib `List` / `Fin` / `Nodup` / `GetElem`.
Zero `sorry`. Do not import `Archive.*`.

This is **not** `List` / `List.length` / `GetElem` / `List.Nodup` /
`Fin` / `Fin.val` — already Mathlib. **USE, do not re-prove; do not
cite as n-queens.**
This is **not** Langford pairing (`ProofLab/LangfordPairing.lean`,
consumed #160). Between-counts ≠ non-attacking diagonals. Do **not**
revive Skolem sequences.
This is **not** Gray codes (`ProofLab/GrayCode.lean`, consumed #163).
Hamming adjacent listings ≠ queen attacks. Do **not** revive hypercube
Hamiltonian.
This is **not** orthogonal Latin squares
(`ProofLab/OrthogonalLatinSquares.lean`, consumed #157). Latin
orthogonality ≠ queens. Do **not** revive Euler officers / Lo Shu.
This is **not** simpson-paradox (`ProofLab/SimpsonParadox.lean`,
consumed #171). Rates ≠ queens.
This is **not** a4-klein-four (`ProofLab/A4KleinFour.lean`,
consumed #172). Even permutations ≠ board attacks.
This is **not** brocard-factorial-square (OPE-1419 leftover HOLD).
Do **not** prove `4!+1=5^2` here.
Do not re-prime the consumed mill. Leave OPE-403 alone.
Leave OPE-1195 alone.

v1 is named small-board witnesses: n=2 has none, n=3 has none, and
n=4 has `[1, 3, 0, 2]`, **not labelled n-queens / eight-queens / Gauss**.
Distinct columns plus both diagonal families are load-bearing (so
Level A is **not** “some list of Fin n is Nodup”).

Level A: n=2 none / n=3 none / n=4 witness. Optional extra: the other
n=4 fundamental solution `[2, 0, 3, 1]`. **Not** labelled n-queens /
eight-queens / Gauss.

Transcribed classical argument (Gauss 1850 / eight-queens; small-board
exhaustive placement). Compact form: Wikipedia *Eight queens puzzle*.
Type pin: `IsNQueens` / `List (Fin n)`. Langford is a different consumed
theorem. Brocard factorial-square is the leftover of this shortlist.
No novelty claim. Default no claim.
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Tactic

namespace ProofLab.NQueens

/-! ## Encoding: non-attacking placements (not labelled n-queens / eight-queens / Gauss) -/

/-- A list `qs : List (Fin n)` of length `n` is a placement with row `i`
in column `qs[i]`. Non-attacking means `qs.Nodup` (distinct columns;
rows are the indices) and no shared diagonal: for `i ≠ j`,
`i + qs[i] ≠ j + qs[j]` (`/` family) and `i + qs[j] ≠ j + qs[i]`
(`\` family). Encoding; **not** labelled n-queens / eight-queens / Gauss.
Load-bearing: distinct columns plus both diagonal families.
Does **not** re-prove `List` / `Fin` / `Nodup` / `GetElem`.
`GetElem` indices are `i < qs.length`; the first conjunct `length = n`
makes this the STATEMENT pin `i < n`. -/
def IsNQueens {n : ℕ} (qs : List (Fin n)) : Prop :=
  qs.length = n ∧
  qs.Nodup ∧
  ∀ (i j : ℕ) (hi : i < qs.length) (hj : j < qs.length),
    i ≠ j →
      i + qs[i].val ≠ j + qs[j].val ∧
      i + qs[j].val ≠ j + qs[i].val

/-! ## Level A: named small-board witnesses (not labelled n-queens / eight-queens / Gauss) -/

/-- `n = 2` has no placement: the two distinct-column boards both share
a diagonal. Glue; **not** labelled n-queens.
Load-bearing: `queens_two_none` (so Level A is **not**
“some list of Fin n is Nodup”). -/
theorem queens_two_none : ¬ ∃ qs : List (Fin 2), IsNQueens qs := by
  rintro ⟨qs, hlen, hnodup, hdiag⟩
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hlen
  have h0 : 0 < ([a, b] : List (Fin 2)).length := by simp
  have h1 : 1 < ([a, b] : List (Fin 2)).length := by simp
  have hne : a ≠ b := by
    intro h
    subst h
    exact List.not_nodup_pair a hnodup
  fin_cases a <;> fin_cases b
  · exact hne rfl
  · -- `[0, 1]`: anti-diagonal `0 + 1 = 1 + 0`
    exact (hdiag 0 1 h0 h1 (by decide)).2 rfl
  · -- `[1, 0]`: diagonal `0 + 1 = 1 + 0`
    exact (hdiag 0 1 h0 h1 (by decide)).1 rfl
  · exact hne rfl

/-- `n = 3` has no placement (`S₃` is six permutations; each shares a
diagonal). Glue; **not** labelled n-queens. Load-bearing:
`queens_three_none`. -/
theorem queens_three_none : ¬ ∃ qs : List (Fin 3), IsNQueens qs := by
  rintro ⟨qs, hlen, hnodup, hdiag⟩
  obtain ⟨a, b, c, rfl⟩ := List.length_eq_three.mp hlen
  have h0 : 0 < ([a, b, c] : List (Fin 3)).length := by simp
  have h1 : 1 < ([a, b, c] : List (Fin 3)).length := by simp
  have h2 : 2 < ([a, b, c] : List (Fin 3)).length := by simp
  -- Distinct columns first (Nodup).
  have hab : a ≠ b := by
    intro h
    subst h
    have := (List.nodup_iff_getElem?_ne_getElem?).1 hnodup 0 1 (by decide) h1
    exact this rfl
  have hac : a ≠ c := by
    intro h
    subst h
    have := (List.nodup_iff_getElem?_ne_getElem?).1 hnodup 0 2 (by decide) h2
    exact this rfl
  have hbc : b ≠ c := by
    intro h
    subst h
    have := (List.nodup_iff_getElem?_ne_getElem?).1 hnodup 1 2 (by decide) h2
    exact this rfl
  fin_cases a <;> fin_cases b <;> fin_cases c
  all_goals
    first
    | exact hab rfl
    | exact hac rfl
    | exact hbc rfl
    | exact (hdiag 0 1 h0 h1 (by decide)).1 rfl
    | exact (hdiag 0 1 h0 h1 (by decide)).2 rfl
    | exact (hdiag 1 2 h1 h2 (by decide)).1 rfl
    | exact (hdiag 1 2 h1 h2 (by decide)).2 rfl

/-- `GetElem` glue for index `2 = 1+1`. Does **not** re-prove `GetElem`. -/
private lemma getElem_two {α} (a b c : α) (t : List α)
    (h : 2 < (a :: b :: c :: t).length) :
    (a :: b :: c :: t)[2] = c := by
  change (a :: b :: c :: t)[1 + 1] = c
  rw [List.getElem_cons_succ]
  change (b :: c :: t)[0 + 1] = c
  rw [List.getElem_cons_succ, List.getElem_cons_zero]

/-- `GetElem` glue for index `3 = 2+1`. Does **not** re-prove `GetElem`. -/
private lemma getElem_three {α} (a b c d : α) (t : List α)
    (h : 3 < (a :: b :: c :: d :: t).length) :
    (a :: b :: c :: d :: t)[3] = d := by
  change (a :: b :: c :: d :: t)[2 + 1] = d
  rw [List.getElem_cons_succ]
  exact getElem_two b c d t _

/-- Value table for a length-4 `Fin 4` list. Glue; not namesake. -/
private lemma list4_get (a b c d : Fin 4)
    {k : ℕ} (hk : k < ([a, b, c, d] : List (Fin 4)).length) :
    ([a, b, c, d] : List (Fin 4))[k] =
      if k = 0 then a else if k = 1 then b else if k = 2 then c else d := by
  have hk4 : k < 4 := by simpa using hk
  interval_cases k
  · simp [List.getElem_cons_zero]
  · simp [List.getElem_cons_succ, List.getElem_cons_zero]
  · exact getElem_two a b c [d] hk
  · exact getElem_three a b c d [] hk

/-- `n = 4` witness `[1, 3, 0, 2]`
(row 0 col 1, row 1 col 3, row 2 col 0, row 3 col 2).
Glue; **not** labelled n-queens / eight-queens / Gauss. -/
theorem queens_four : IsNQueens ([1, 3, 0, 2] : List (Fin 4)) := by
  refine ⟨rfl, by decide, ?diag⟩
  intro i j hi hj hij
  have hi4 : i < 4 := by simpa using hi
  have hj4 : j < 4 := by simpa using hj
  simp [list4_get (1 : Fin 4) 3 0 2 hi, list4_get (1 : Fin 4) 3 0 2 hj]
  interval_cases i <;> interval_cases j <;> first | contradiction | decide

/-- Optional extra: the other `n = 4` fundamental solution `[2, 0, 3, 1]`.
Glue; **not** labelled n-queens. -/
theorem queens_four_alt : IsNQueens ([2, 0, 3, 1] : List (Fin 4)) := by
  refine ⟨rfl, by decide, ?diag⟩
  intro i j hi hj hij
  have hi4 : i < 4 := by simpa using hi
  have hj4 : j < 4 := by simpa using hj
  simp [list4_get (2 : Fin 4) 0 3 1 hi, list4_get (2 : Fin 4) 0 3 1 hj]
  interval_cases i <;> interval_cases j <;> first | contradiction | decide

/-
Level B namesake OUT of this ticket (do not sorry):
  theorem n_queens :
      ∀ n : ℕ, (∃ qs : List (Fin n), IsNQueens qs) ↔ n ≠ 2 ∧ n ≠ 3
Solution-count 92 / completion / uniqueness / toroidal queens are
residual of this id — do not expand; do not label theorems
`nQueens` / `eightQueens` / `isQueens`.
-/

end ProofLab.NQueens
