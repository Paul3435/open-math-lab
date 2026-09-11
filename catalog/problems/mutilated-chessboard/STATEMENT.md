# Mutilated chessboard (2×2 opposite corners none / 4×4 color imbalance, formalize-only)

**id:** `mutilated-chessboard`
**ticket:** OPE-1434 Scout RECOMMENDED PRIME (parent OPE-1433;
post n-queens #174 + brocard-factorial-square #175)
**expected:** known-classical (Dudeney / Gomory: an `n×n`
board with two opposite corners removed has no domino
tiling, because those corners have the same 2-color and
every domino covers one black and one white) —
**no novelty claim**

## Why not classical / why formalize-only

Settled board-coloring obstruction. Pin one encoding: cells
`Fin n × Fin n` with color `(i.val + j.val) % 2`. Opposite
corners `(0,0)` and `(n-1,n-1)` have the same color.
A domino covers two orthogonally adjacent cells, hence two
different colors.

Small-board witnesses:

- `n = 2`: removing opposite corners leaves two same-color
  squares; no domino tiling
- `n = 4`: opposite corners same color, remaining board
  6 vs 8 (color imbalance)

Completely classical. The namesake “the 8×8 mutilated board
has no tiling / every even-by-even opposite-corner removal”
is a **different**, larger residual — do **not** sorry it.

Not an open problem. Not a novelty claim. Not live cash.

**Not** n-queens (consumed #174; non-attacking placement ≠
domino covering; do **not** revive eight-queens / Gauss /
exists iff `n≠2,3`). **Not** Langford (consumed #160).
**Not** Gray (consumed #163). **Not** OLS (consumed #157).
**Not** Domineering (Mathlib `SetTheory/Game/Domineering.lean`
L11 already-in *game* on a chessboard; different theorem;
USE board-as-`Finset` idea if needed, do **not** re-prove
Domineering, do **not** cite as mutilated, do **not** label
theorems `domineering_*`). **Not** Sprague–Grundy
(`equiv_nim_grundyValue` already-in). **Not** British-flag
opposite-corner pairing (consumed #145; Euclidean `dist`
on the unit square ≠ grid 2-coloring; do **not** revive
Napoleon / Simson / Viviani). **Not** brocard-factorial-square
(consumed #175). **Not** Hall SDR (already-in
`hall_hard_inductive` Hall/Finite.lean L217; different
matching theorem). **Not** König matching / Gale–Shapley
(consumed). **Not** Sabidussi box-product (consumed #139;
`pathGraph □ pathGraph` is optional *grid glue*, **not**
namesake; do **not** revive Hedetniemi). **Not** L-tromino
deficient-board covering (residual cluster of *this* mill
if both slotted — leftover of this shortlist is Hex, not
tromino). **Not** Golomb ruler (placement leftover of
n-queens).

Mathlib v4.10.0 already has the **grid / parity / matching
infra this theorem needs**:

- `Fin` / `Fin.val` / `Prod`
- `Even` (to_additive of `IsSquare`, Algebra/Group/Even.lean
  L46) as parity glue **not** namesake
- `Subgraph.IsMatching` / `IsPerfectMatching`
  (Matching.lean L50 / L139)
- `IsMatching.even_card` (Matching.lean L150) as
  matching-parity glue **not** namesake
- optional `pathGraph` (Hasse.lean L94) / `boxProd`
  (Prod.lean L39) as grid glue **not** namesake

There is **no** named `mutilated` / `MutilatedChessboard` /
`gomory` / `Gomory` / `chessboard_tiling` theorem anywhere
under `Mathlib/` or `Archive/` or `ProofLab/` (this run →
ZERO on those names; `chessboard` hits only Domineering
comments; `opposite corner` hits British-flag Euclidean
pairing and a Cauchy-integral rectangle, different
theorems). Do **not** import `Archive.*`.

OPE-1419 shortlist is **CONSUMED** (#174+#175). This is a
**fresh** catalog-audit prime, **not** an n-queens leftover
continuation, **not** a Brocard leftover, **not** a
Domineering leftover-revival, **not** a British-flag
leftover, **not** a prize leftover, **not** a Formalist
Level B revival, **not** a third slot.

Mill NOW: finite color-imbalance witnesses on Mathlib
`Fin` / `Even` / matching parity. **Not a rubber-stamp of
n-queens.** **Not a rubber-stamp of Domineering.** **Not a
rubber-stamp of British-flag.**

Do **not** describe an attack as discovering the mutilated
chessboard. Do **not** expand into the 8×8 namesake as a
sorry (that is leftover-risk of *this* id — do **not**
sorry it). Do **not** label theorems `queens_*` /
`domineering_*` / `british_flag_*` / `tromino_*` /
`hex_*` as the namesake.

## Pinned convention (exact)

**v1 Level A is named small-board witnesses: n=2 opposite
corners leave no domino tiling, and n=4 opposite corners
leave a 6-vs-8 color imbalance, not labelled mutilated /
Gomory / Dudeney.** Same-color corners plus “domino covers
two colors” are load-bearing, so the theorem is **not**
“some Finset of Fin n × Fin n has even cardinality.”

Suggested pin:

```text
-- Level A (not labelled mutilated / Gomory / Dudeney):
-- named small-board witnesses.

def BoardColor {n : ℕ} (p : Fin n × Fin n) : ℕ :=
  (p.1.val + p.2.val) % 2

def OppositeCorners (n : ℕ) [NeZero n] :
    Finset (Fin n × Fin n) :=
  {(0, 0), (⟨n - 1, Nat.sub_lt (Nat.pos_of_neZero n) Nat.zero_lt_one⟩,
            ⟨n - 1, Nat.sub_lt (Nat.pos_of_neZero n) Nat.zero_lt_one⟩)}

theorem mutilated_two_none :
    BoardColor (0, 0) = BoardColor (1, 1) ∧
    (∀ p : Fin 2 × Fin 2, p ≠ (0, 0) → p ≠ (1, 1) →
      BoardColor p = BoardColor (0, 0))

theorem mutilated_four_imbalance :
    BoardColor (0 : Fin 4, 0) = BoardColor (3, 3) ∧
    ((Finset.univ.filter (fun p => BoardColor p = 0)).card = 8) ∧
    ((Finset.univ.filter (fun p => BoardColor p = 1)).card = 8)

-- optional extra: n=4 remaining after opposite-corner
-- removal is 6 vs 8
-- theorem mutilated_four_remaining : ...

-- Level B namesake (8×8 / all even n; residual OK)
theorem mutilated_chessboard ...
    -- do not sorry the namesake
```

Named small-board color facts are load-bearing.

**Level A may land only** the n=2 same-color leftover pair
plus the n=4 8-and-8 / remaining 6-vs-8 imbalance
(optional extra: an explicit “no perfect matching” on n=2),
**not** labelled mutilated / Gomory / Dudeney. Reuse
Mathlib `Fin` / `Even` / `IsMatching.even_card` — **do not
re-prove** n-queens / Domineering / British-flag.

**Level B** is the namesake 8×8 (or all even `n`) mutilated
board. Do not sorry it. L-tromino deficient boards /
Aztec diamonds are extras residual.

## Out of v1 this ticket

- 8×8 namesake / all even `n`
- L-tromino / Golomb deficient 2ⁿ board
- Aztec diamond / Kasteleyn
- Domineering CGT analysis
- n-queens leftover-revivals
- British-flag leftover-revivals
- Hex (leftover of this shortlist)
- OPE-403 Happy Ending
- OPE-1195 lame-euclid leftover-status

## Claim

Default **no claim**. Formalize-only. No novelty.
