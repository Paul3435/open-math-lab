# n-queens small boards (n=2 none / n=3 none / n=4 a witness, formalize-only)

**id:** `n-queens`
**ticket:** OPE-1419 Scout RECOMMENDED PRIME (parent OPE-1418;
post simpson-paradox #171 + a4-klein-four #172)
**expected:** known-classical (Gauss 1850 / eight-queens:
place `n` queens on an `n×n` board so that none share a
row, column, or diagonal; exists iff `n ≠ 2` and `n ≠ 3`) —
**no novelty claim**

## Why not classical / why formalize-only

Settled combinatorial placement. Pin one encoding: a list
`qs : List (Fin n)` of length `n` is a placement with row
`i` in column `qs[i]`. Non-attacking means `qs.Nodup`
(distinct columns; rows are the indices) and no shared
diagonal: for `i ≠ j`,

- `i + qs[i] ≠ j + qs[j]` (same `/` diagonal)
- `i + qs[j] ≠ j + qs[i]` (same `\` diagonal)

Small-board witnesses:

- `n = 2`: none
- `n = 3`: none
- `n = 4`: `[1, 3, 0, 2]` (row 0 col 1, row 1 col 3,
  row 2 col 0, row 3 col 2)

Completely classical. The namesake “exists for every
`n ≠ 2,3` / 92 solutions on `n = 8`” is a **different**,
larger residual — do **not** sorry it.

Not an open problem. Not a novelty claim. Not live cash.

**Not** Langford pairing (consumed #160; between-counts ≠
non-attacking diagonals; do **not** revive Skolem
sequences). **Not** Gray codes (consumed #163; Hamming
adjacent listings ≠ queen attacks; do **not** revive
hypercube Hamiltonian). **Not** orthogonal Latin squares
(consumed #157; Latin orthogonality ≠ queens; do **not**
revive Euler officers / magic squares / Lo Shu). **Not**
graceful trees (heuristic mill; vertex labels ≠ queens).
**Not** a4-klein-four (consumed #172; even permutations ≠
board attacks; do **not** revive KleinFour / A₄ subgroup
order 6). **Not** simpson-paradox (consumed #171; rates ≠
queens). **Not** the 15-puzzle / alternating-group
solvability (Aₙ leftover-risk of #172; do **not** sorry
15-puzzle). **Not** n-queens completion / uniqueness /
solution-count 92 (residual of this id; do **not** sorry
them).

Mathlib v4.10.0 already has the **list / Fin infra this
theorem needs**:

- `List` / `List.length` / `GetElem` / `List.Nodup`
  (Data/List/Nodup.lean properties)
- `Fin` / `Fin.val`
- `Function.Injective` (Logic/Function/Defs.lean L101)
  as optional column-injectivity glue **not** namesake

There is **no** named `nQueens` / `NQueens` / `eightQueens`
/ `EightQueens` / `isQueens` / `queens_problem` theorem
anywhere under `Mathlib/` or `Archive/` or `ProofLab/`
(this run → ZERO on those names; the only `queen` hit is
“Queen Mary University” in a comment). Do **not** import
`Archive.*`.

OPE-1405 shortlist is **CONSUMED** (#171+#172). This is a
**fresh** catalog-audit prime, **not** a simpson leftover
continuation, **not** an a4-klein-four leftover, **not** a
Langford leftover, **not** a prize leftover, **not** a
Formalist Level B revival, **not** a third slot.

Mill NOW: finite small-board n-queens witnesses on Mathlib
`List` / `Fin` / `Nodup`. **Not a rubber-stamp of
Langford.** **Not a rubber-stamp of Gray.** **Not a
rubber-stamp of A₄.**

Do **not** describe an attack as discovering n-queens.
Do **not** expand into existence iff `n ≠ 2,3` as a sorry
(that is leftover-risk of *this* id — do **not** sorry it).
Do **not** label theorems `langford_*` / `skolem_*` /
`gray_*` / `latin_*` as the namesake.

## Pinned convention (exact)

**v1 Level A is named small-board witnesses: n=2 has none,
n=3 has none, and n=4 has `[1, 3, 0, 2]`, not labelled
n-queens / eight-queens / Gauss.** Distinct columns plus
both diagonal families are load-bearing, so the theorem is
**not** “some list of Fin n is Nodup.”

Suggested pin:

```text
-- Level A (not labelled n-queens / eight-queens / Gauss):
-- named small-board witnesses.

def IsNQueens {n : ℕ} (qs : List (Fin n)) : Prop :=
  qs.length = n ∧ qs.Nodup ∧
  ∀ i j : ℕ, i < n → j < n → i ≠ j →
    i + (qs[i]).val ≠ j + (qs[j]).val ∧
    i + (qs[j]).val ≠ j + (qs[i]).val

theorem queens_two_none :
    ¬ ∃ qs : List (Fin 2), IsNQueens qs

theorem queens_three_none :
    ¬ ∃ qs : List (Fin 3), IsNQueens qs

theorem queens_four :
    IsNQueens [1, 3, 0, 2]

-- optional extra: the other n=4 fundamental solution
-- theorem queens_four_alt : IsNQueens [2, 0, 3, 1]

-- Level B namesake (exists iff n ≠ 2, 3; residual OK)
theorem n_queens ...
    -- do not sorry the namesake
```

Named three-line small-board facts are load-bearing.

**Level A may land only** the two non-existence theorems
plus the n=4 witness (optional extra: the other n=4
solution `[2, 0, 3, 1]`), **not** labelled n-queens /
eight-queens / Gauss. Reuse Mathlib `List` / `Fin` /
`Nodup` — **do not re-prove** Langford / Gray / OLS.

**Level B** is the namesake existence iff `n ≠ 2,3`. Do
not sorry it. Solution-count 92 / uniqueness / completion
are extras residual.

## Out of v1 this ticket

- Existence for every `n ≠ 2,3`
- 8-queens solution count 92
- n-queens completion NP-completeness
- Modular / toroidal queens
- Langford / Skolem leftover-revivals
- Gray / hypercube Hamiltonian leftover-revivals
- OLS / Euler officers / Lo Shu leftover-revivals
- a4-klein-four / 15-puzzle leftover-revivals
- simpson-paradox leftover-revivals
- OPE-403 Happy Ending
- OPE-1195 lame-euclid leftover-status

## Claim

Default **no claim**. Formalize-only. No novelty.
