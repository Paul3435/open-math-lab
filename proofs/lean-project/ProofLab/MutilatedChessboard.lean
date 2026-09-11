/-
Named small-board color witnesses — Level A only
(n=2 opposite corners same color / leftover pair same color;
n=4 color 8-and-8 plus remaining 6-vs-8).
**Not labelled mutilated / Gomory / Dudeney.**

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 pin `a719ba5c3115` has `Fin` / `Fin.val` / `Prod` /
`Even` / `Finset.card` / `Subgraph.IsMatching` /
`IsMatching.even_card` as **infra**. ZERO named `mutilated` /
`MutilatedChessboard` / `gomory` / `Gomory` / `chessboard_tiling`
under `Mathlib/` or `Archive/` or `ProofLab/` (this run; `chessboard`
hits only Domineering comments; opposite-corner hits are British-flag
Euclidean pairing, a different theorem). Completing the Level A named
small-board color facts is the gap this ticket lands. The Level B
namesake `mutilated_chessboard` (8×8 / all even n opposite-corner
removal has no tiling) is **out of this ticket** and is **not**
sorry-ed. L-tromino deficient boards / Aztec diamonds / Kasteleyn
are residual of this id. Do **not** label theorems
`mutilated_chessboard` / `gomory_*` / `dudeney_*` / `domineering_*` /
`queens_*` / `british_flag_*` / `tromino_*` / `hex_*` as the namesake.

Pin: `catalog/problems/mutilated-chessboard/STATEMENT.md`
(OPE-1439; Scout OPE-1434 RECOMMENDED PRIME; Director OPE-1438 APPROVE).
Encoding: `BoardColor` via Mathlib `Fin` / `% 2`. Zero `sorry`.
Do not import `Archive.*`.

This is **not** `Fin` / `Prod` / `Even` / `Finset.card` /
`IsMatching.even_card` — already Mathlib. **USE, do not re-prove;
do not cite as mutilated.**
This is **not** n-queens (`ProofLab/NQueens.lean`, consumed #174).
Placement ≠ covering. Do **not** revive eight-queens / Gauss /
exists iff `n≠2,3`.
This is **not** Domineering (`SetTheory/Game/Domineering.lean`).
Already-in CGT *game*, different theorem. Do **not** re-prove;
do **not** label theorems `domineering_*`.
This is **not** British-flag (`ProofLab/BritishFlag.lean`, consumed
#145). Euclidean `dist` ≠ grid 2-coloring. Do **not** revive
Napoleon / Simson / Viviani.
This is **not** Hall SDR (`hall_hard_inductive`). Different matching
theorem. Do **not** re-prove; do **not** label theorems `hall_*`.
This is **not** Sabidussi box-product (`ProofLab/SabidussiBoxProd.lean`,
consumed #139). Optional `pathGraph` / `boxProd` is grid glue, not
namesake. Do **not** revive Hedetniemi.
This is **not** brocard-factorial-square
(`ProofLab/BrocardFactorialSquare.lean`, consumed #175).
Do **not** prove `4!+1=5^2` here.
This is **not** hex-no-draw (leftover HOLD of this shortlist).
Do **not** prove `n=1` cell-wins / `n=2` Hex winner / HexTheorem /
NashHex / GaleHex here.
Do not re-prime the consumed mill. Leave OPE-403 alone.
Leave OPE-1195 alone.

v1 is named small-board color facts: n=2 opposite corners same color
and leftover pair same color, n=4 color 8-and-8 plus remaining
6-vs-8, **not labelled mutilated / Gomory / Dudeney**. Same-color
corners plus “domino covers two colors” are load-bearing (so Level A
is **not** “some Finset of Fin n × Fin n has even cardinality”).

Level A: `mutilated_two_none` / `mutilated_four_imbalance`.
Optional extra: `mutilated_four_remaining` / `boardColor_of_orthoAdj`
(domino covers two colors) / `mutilated_two_leftover_not_adj`.
**Not** labelled mutilated / Gomory / Dudeney.

Transcribed classical argument (Dudeney / Gomory coloring). Compact
form: Wikipedia *Mutilated chessboard problem*. Type pin: `BoardColor`
/ `Fin n × Fin n`. n-queens, Domineering, and British-flag are
different consumed / already-in theorems. Hex is the leftover of this
shortlist. No novelty claim. Default no claim.

Note on the STATEMENT suggested `mutilated_two_none` body: the
quantifier `leftover p → BoardColor p = BoardColor (0,0)` is a
copy-paste slip (leftover squares are the *other* color). Prose pin
and Director v1 pin are “opposite corners same color / leftover pair
same color.” That is the encoding landed here.

Level B namesake OUT of this ticket (do not sorry):
-- theorem mutilated_chessboard ...
--     -- 8×8 / all even n; do not sorry the namesake
-/
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace ProofLab.MutilatedChessboard

/-! ## Encoding: board 2-coloring (not labelled mutilated / Gomory / Dudeney) -/

/-- Cell color on `Fin n × Fin n` is `(row + col) % 2`.
Encoding; **not** labelled mutilated / Gomory / Dudeney.
Glue: Mathlib `Fin.val` / `%`. Does **not** re-prove `Fin` / `Prod`. -/
def BoardColor {n : ℕ} (p : Fin n × Fin n) : ℕ :=
  (p.1.val + p.2.val) % 2

/-- Orthogonal adjacency (a domino covers two orthogonally adjacent
cells). Encoding glue; **not** namesake. -/
def OrthoAdj {n : ℕ} (p q : Fin n × Fin n) : Prop :=
  (p.1 = q.1 ∧ (p.2.val + 1 = q.2.val ∨ q.2.val + 1 = p.2.val)) ∨
  (p.2 = q.2 ∧ (p.1.val + 1 = q.1.val ∨ q.1.val + 1 = p.1.val))

/-- A domino covers two colors: orthogonally adjacent cells have
different `BoardColor`. Load-bearing (so Level A is **not** “some
Finset has even cardinality”). Glue; **not** labelled mutilated /
Gomory / Dudeney. -/
theorem boardColor_of_orthoAdj {n : ℕ} {p q : Fin n × Fin n}
    (h : OrthoAdj p q) : BoardColor p ≠ BoardColor q := by
  unfold OrthoAdj at h
  unfold BoardColor
  rcases h with (⟨hrow, hcol⟩ | ⟨hcol, hrow⟩)
  · rcases hcol with h | h <;> omega
  · rcases hrow with h | h <;> omega

/-! ## Level A: named small-board witnesses
(not labelled mutilated / Gomory / Dudeney) -/

/-- `n = 2`: opposite corners `(0,0)` and `(1,1)` have the same color,
and the leftover pair `(0,1)` and `(1,0)` have the same color as each
other. Glue; **not** labelled mutilated / Gomory / Dudeney.
Load-bearing: same-color corners plus same-color leftover pair. -/
theorem mutilated_two_none :
    BoardColor ((0 : Fin 2), (0 : Fin 2)) = BoardColor ((1 : Fin 2), (1 : Fin 2)) ∧
    BoardColor ((0 : Fin 2), (1 : Fin 2)) = BoardColor ((1 : Fin 2), (0 : Fin 2)) := by
  constructor <;> rfl

/-- Optional extra: the n=2 leftover pair is not orthogonally adjacent
(coloring obstruction: same color, and a domino covers two colors).
Glue; **not** labelled mutilated / Gomory / Dudeney. -/
theorem mutilated_two_leftover_not_adj :
    ¬ OrthoAdj ((0 : Fin 2), (1 : Fin 2)) ((1 : Fin 2), (0 : Fin 2)) := by
  intro h
  exact (boardColor_of_orthoAdj h) mutilated_two_none.2

/-- `n = 4`: opposite corners `(0,0)` and `(3,3)` have the same color,
and the full board is 8-and-8. Glue; **not** labelled mutilated /
Gomory / Dudeney. Load-bearing: same-color corners plus color counts. -/
theorem mutilated_four_imbalance :
    BoardColor ((0 : Fin 4), (0 : Fin 4)) = BoardColor ((3 : Fin 4), (3 : Fin 4)) ∧
    ((Finset.univ.filter (fun p : Fin 4 × Fin 4 => BoardColor p = 0)).card = 8) ∧
    ((Finset.univ.filter (fun p : Fin 4 × Fin 4 => BoardColor p = 1)).card = 8) := by
  refine ⟨rfl, ?c0, ?c1⟩
  · decide
  · decide

/-- Optional extra: after removing opposite corners, remaining board
is 6 vs 8. Glue; **not** labelled mutilated / Gomory / Dudeney. -/
theorem mutilated_four_remaining :
    ((Finset.univ.filter (fun p : Fin 4 × Fin 4 =>
        p ≠ ((0 : Fin 4), (0 : Fin 4)) ∧
        p ≠ ((3 : Fin 4), (3 : Fin 4)) ∧ BoardColor p = 0)).card = 6) ∧
    ((Finset.univ.filter (fun p : Fin 4 × Fin 4 =>
        p ≠ ((0 : Fin 4), (0 : Fin 4)) ∧
        p ≠ ((3 : Fin 4), (3 : Fin 4)) ∧ BoardColor p = 1)).card = 8) := by
  constructor
  · decide
  · decide

/-
Level B namesake OUT of this ticket (do not sorry):
  theorem mutilated_chessboard :
      -- 8×8 / all even n opposite-corner removal has no domino tiling
L-tromino deficient boards / Aztec diamonds / Kasteleyn are residual
of this id — do not expand; do not label theorems
`mutilated_chessboard` / `gomory_*` / `dudeney_*` / `domineering_*` /
`queens_*` / `british_flag_*` / `tromino_*` / `hex_*`.
-/

end ProofLab.MutilatedChessboard
