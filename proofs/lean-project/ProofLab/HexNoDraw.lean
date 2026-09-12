/-
Named small-board no-draw witnesses — Level A only
(n=1 cell-wins / n=2 every coloring has a winner).
**Not labelled Hex / Nash / Gale.**

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 pin `a719ba5c3115` has `Fin` / `Prod` /
`SimpleGraph.Reachable` (Path.lean L628) / `Walk` as **infra**.
ZERO named `hex_no_draw` / `HexTheorem` / `hex_theorem` /
`NashHex` / `GaleHex` / `HexNoDraw` under `Mathlib/` or
`Archive/` or `ProofLab/` (this run; Hex hits are PGame.lean L83
future-work bullet `* Hex.` — CGT residual of this id, not
Level A — and an unrelated `have Hex` identifier in
PrimitiveRoots.lean L439). Completing the Level A named
small-board no-draw facts is the gap this ticket lands. The
Level B namesake `hex_no_draw` (every n completed coloring has
a winner) is **out of this ticket** and is **not** sorry-ed.
First-player win / Gale pairing / Brouwer / Shannon switching /
Bridg-it / CGT Hex are residual of this id. Do **not** label
theorems `hex_no_draw` / `HexTheorem` / `NashHex` / `GaleHex` /
`gale_*` / `nash_*` / `queens_*` / `mutilated_*` /
`domineering_*` as the namesake.

Pin: `catalog/problems/hex-no-draw/STATEMENT.md`
(OPE-1444; Scout OPE-1434 leftover HOLD; Director OPE-1443 APPROVE).
Encoding: `HexAdj` six neighbors; color-class `Reachable` via
Mathlib `SimpleGraph.induce`. Zero `sorry`. Do not import
`Archive.*`.

This is **not** `Fin` / `Prod` / `SimpleGraph.Reachable` /
`Walk` — already Mathlib. **USE, do not re-prove; do not cite
as Hex.**
This is **not** `Colorable` (Coloring.lean L127). Vertex-coloring
glue, **not** namesake. Hex colors *cells*, not a proper vertex
coloring of the hex graph.
This is **not** n-queens (`ProofLab/NQueens.lean`, consumed #174).
Placement ≠ side-connection. Do **not** revive eight-queens / Gauss.
This is **not** Gale–Shapley (`ProofLab/GaleShapley.lean`, consumed
#126). Stable marriage is a different Gale. Do **not** label
theorems `gale_*`.
This is **not** Nash–Williams (`ProofLab/NashWilliamsArboricity.lean`,
consumed #124). Different Nash. Do **not** label theorems `nash_*`.
This is **not** mutilated-chessboard (`ProofLab/MutilatedChessboard.lean`,
consumed #177). Parity tiling ≠ Hex connection. Do **not** prove
`mutilated_two_none` / `mutilated_four_imbalance` here.
This is **not** Domineering (`SetTheory/Game/Domineering.lean`).
Already-in CGT *game*, different theorem. Do **not** re-prove;
do **not** label theorems `domineering_*`.
This is **not** British-flag (`ProofLab/BritishFlag.lean`, consumed
#145). Do **not** label theorems `british_flag_*`.
This is **not** brocard-factorial-square
(`ProofLab/BrocardFactorialSquare.lean`, consumed #175).
Do **not** prove `4!+1=5^2` here.
Do not re-prime the consumed mill. Leave OPE-403 alone.
Leave OPE-1195 alone.

v1 is named small-board no-draw facts: n=1 the unique cell wins
for its owner, and n=2 every 2-coloring has a winner, **not
labelled Hex / Nash / Gale**. Side-connection via `Reachable`
on each color class is load-bearing (so Level A is **not**
“some function Fin n × Fin n → Fin 2 exists”).

Level A: `hex_one` / `hex_two`. Optional extra: one explicit
n=2 red-win coloring. **Not** labelled Hex / Nash / Gale.

Transcribed classical argument (Nash 1952 / Gale; small-board
exhaustive coloring). Compact form: Wikipedia *Hex (board game)*
no-draw. Type pin: `HexAdj` / `HexColoring` / color-class
`Reachable`. Gale–Shapley and Nash–Williams are different
consumed theorems. Mutilated-chessboard is the consumed prime
of this shortlist. No novelty claim. Default no claim.

Level B namesake OUT of this ticket (do not sorry):
-- theorem hex_no_draw ...
--     -- every n; do not sorry the namesake
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic

namespace ProofLab.HexNoDraw

/-! ## Encoding: hex adjacency and 2-colorings
(not labelled Hex / Nash / Gale) -/

/-- Six in-board hex neighbors of `(i,j)`:
`(i±1,j)`, `(i,j±1)`, `(i+1,j-1)`, `(i-1,j+1)`.
Encoding; **not** labelled Hex / Nash / Gale.
Glue: Mathlib `Fin.val`. Does **not** re-prove `Fin` / `Prod`. -/
def HexNeighbor {n : ℕ} (p q : Fin n × Fin n) : Prop :=
  (p.1.val + 1 = q.1.val ∧ p.2 = q.2) ∨
  (q.1.val + 1 = p.1.val ∧ p.2 = q.2) ∨
  (p.2.val + 1 = q.2.val ∧ p.1 = q.1) ∨
  (q.2.val + 1 = p.2.val ∧ p.1 = q.1) ∨
  (p.1.val + 1 = q.1.val ∧ q.2.val + 1 = p.2.val) ∨
  (q.1.val + 1 = p.1.val ∧ p.2.val + 1 = q.2.val)

lemma hexNeighbor_symm {n : ℕ} : Symmetric (@HexNeighbor n) := by
  intro p q h
  unfold HexNeighbor at *
  rcases h with h | h | h | h | h | h <;> tauto

lemma hexNeighbor_irrefl {n : ℕ} : Irreflexive (@HexNeighbor n) := by
  intro p hp
  unfold HexNeighbor at hp
  rcases hp with h | h | h | h | h | h
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

/-- Hex-adjacency graph on `Fin n × Fin n`. Encoding; **not**
labelled Hex / Nash / Gale. -/
def HexAdj {n : ℕ} : SimpleGraph (Fin n × Fin n) where
  Adj := HexNeighbor
  symm := hexNeighbor_symm
  loopless := hexNeighbor_irrefl

/-- A completed 2-coloring of the `n×n` board. Encoding; **not**
labelled Hex / Nash / Gale. -/
def HexColoring (n : ℕ) := (Fin n × Fin n) → Fin 2

/-- Color 0 connects left `{j = 0}` to right `{j = n-1}` in the
color-0 induced subgraph. Load-bearing `Reachable` (so Level A
is **not** “some function Fin n × Fin n → Fin 2 exists”).
Glue; **not** labelled Hex / Nash / Gale. -/
def RedWins {n : ℕ} (c : HexColoring n) : Prop :=
  ∃ (a b : Fin n × Fin n) (ha : c a = 0) (hb : c b = 0),
    a.2.val = 0 ∧ b.2.val = n - 1 ∧
      (HexAdj.induce {p | c p = 0}).Reachable ⟨a, ha⟩ ⟨b, hb⟩

/-- Color 1 connects top `{i = 0}` to bottom `{i = n-1}` in the
color-1 induced subgraph. Load-bearing `Reachable`.
Glue; **not** labelled Hex / Nash / Gale. -/
def BlueWins {n : ℕ} (c : HexColoring n) : Prop :=
  ∃ (a b : Fin n × Fin n) (ha : c a = 1) (hb : c b = 1),
    a.1.val = 0 ∧ b.1.val = n - 1 ∧
      (HexAdj.induce {p | c p = 1}).Reachable ⟨a, ha⟩ ⟨b, hb⟩

lemma hexAdj_of_row {n : ℕ} {i : Fin n} {j j' : Fin n}
    (h : j.val + 1 = j'.val) : HexAdj.Adj (i, j) (i, j') :=
  Or.inr <| Or.inr <| Or.inl ⟨h, rfl⟩

lemma hexAdj_of_col {n : ℕ} {i i' : Fin n} {j : Fin n}
    (h : i.val + 1 = i'.val) : HexAdj.Adj (i, j) (i', j) :=
  Or.inl ⟨h, rfl⟩

lemma hexAdj_of_diag {n : ℕ} {i i' : Fin n} {j j' : Fin n}
    (hi : i.val + 1 = i'.val) (hj : j'.val + 1 = j.val) :
    HexAdj.Adj (i, j) (i', j') :=
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨hi, hj⟩

lemma induce_adj_of {n : ℕ} {c : HexColoring n} {k : Fin 2}
    {p q : Fin n × Fin n} (hp : c p = k) (hq : c q = k)
    (h : HexAdj.Adj p q) :
    (HexAdj.induce {x | c x = k}).Adj ⟨p, hp⟩ ⟨q, hq⟩ :=
  h

lemma fin2_eq_zero_or_one (x : Fin 2) : x = 0 ∨ x = 1 := by
  fin_cases x <;> simp

lemma fin2_eq_one_of_ne_zero {x : Fin 2} (h : x ≠ 0) : x = 1 := by
  fin_cases x <;> simp at h ⊢

lemma fin2_eq_zero_of_ne_one {x : Fin 2} (h : x ≠ 1) : x = 0 := by
  fin_cases x <;> simp at h ⊢

/-! ## Level A: named small-board witnesses
(not labelled Hex / Nash / Gale) -/

/-- `n = 1`: the unique cell, whatever its color, connects both of
that color’s sides (left=right and top=bottom are the same cell;
`Reachable` is reflexive). Glue; **not** labelled Hex / Nash / Gale.
Load-bearing: side-connection via `Reachable`. -/
theorem hex_one : ∀ c : HexColoring 1, RedWins c ∨ BlueWins c := by
  intro c
  let a : Fin 1 × Fin 1 := (0, 0)
  rcases fin2_eq_zero_or_one (c a) with hc | hc
  · left
    refine ⟨a, a, hc, hc, rfl, rfl, SimpleGraph.Reachable.rfl⟩
  · right
    refine ⟨a, a, hc, hc, rfl, rfl, SimpleGraph.Reachable.rfl⟩

/-- Optional extra: an explicit n=2 red-win coloring (both cells of
row 0 colored 0, so left meets right on that row). Glue; **not**
labelled Hex / Nash / Gale. -/
def hexTwoRow0Red : HexColoring 2 := fun p => if p.1.val = 0 then 0 else 1

theorem hex_two_row0_red : RedWins hexTwoRow0Red := by
  let a : Fin 2 × Fin 2 := (0, 0)
  let b : Fin 2 × Fin 2 := (0, 1)
  have ha : hexTwoRow0Red a = 0 := rfl
  have hb : hexTwoRow0Red b = 0 := rfl
  refine ⟨a, b, ha, hb, rfl, rfl, SimpleGraph.Adj.reachable ?_⟩
  exact induce_adj_of ha hb (hexAdj_of_row (by decide : (0 : Fin 2).val + 1 = (1 : Fin 2).val))

/-- `n = 2`: every 2-coloring of the four cells has a winner (no draw).
Glue; **not** labelled Hex / Nash / Gale. Load-bearing: every coloring,
side-connection via `Reachable` (so Level A is **not** “some function
exists”). -/
theorem hex_two : ∀ c : HexColoring 2, RedWins c ∨ BlueWins c := by
  intro c
  let A : Fin 2 × Fin 2 := (0, 0)
  let B : Fin 2 × Fin 2 := (0, 1)
  let C : Fin 2 × Fin 2 := (1, 0)
  let D : Fin 2 × Fin 2 := (1, 1)
  have hrow : (0 : Fin 2).val + 1 = (1 : Fin 2).val := by decide
  have hAdjAB : HexAdj.Adj A B := hexAdj_of_row hrow
  have hAdjCD : HexAdj.Adj C D := hexAdj_of_row hrow
  have hAdjAC : HexAdj.Adj A C := hexAdj_of_col hrow
  have hAdjBD : HexAdj.Adj B D := hexAdj_of_col hrow
  have hAdjBC : HexAdj.Adj B C := hexAdj_of_diag hrow hrow
  by_cases hA0 : c A = 0
  · by_cases hB0 : c B = 0
    · left
      exact ⟨A, B, hA0, hB0, rfl, rfl, SimpleGraph.Adj.reachable (induce_adj_of hA0 hB0 hAdjAB)⟩
    · have hB1 : c B = 1 := fin2_eq_one_of_ne_zero hB0
      by_cases hC0 : c C = 0
      · by_cases hD0 : c D = 0
        · left
          exact ⟨C, D, hC0, hD0, rfl, rfl, SimpleGraph.Adj.reachable (induce_adj_of hC0 hD0 hAdjCD)⟩
        · have hD1 : c D = 1 := fin2_eq_one_of_ne_zero hD0
          -- A red, B blue, C red, D blue: blue connects B (top) to D (bottom).
          right
          exact ⟨B, D, hB1, hD1, rfl, rfl, SimpleGraph.Adj.reachable (induce_adj_of hB1 hD1 hAdjBD)⟩
      · have hC1 : c C = 1 := fin2_eq_one_of_ne_zero hC0
        -- A red, B blue, C blue: blue connects B (top) to C (bottom) by hex diagonal.
        right
        exact ⟨B, C, hB1, hC1, rfl, rfl, SimpleGraph.Adj.reachable (induce_adj_of hB1 hC1 hAdjBC)⟩
  · have hA1 : c A = 1 := fin2_eq_one_of_ne_zero hA0
    by_cases hC1 : c C = 1
    · right
      exact ⟨A, C, hA1, hC1, rfl, rfl, SimpleGraph.Adj.reachable (induce_adj_of hA1 hC1 hAdjAC)⟩
    · have hC0 : c C = 0 := fin2_eq_zero_of_ne_one hC1
      by_cases hB0 : c B = 0
      · -- A blue, B red, C red: red connects C (left) to B (right) by hex diagonal.
        left
        exact ⟨C, B, hC0, hB0, rfl, rfl, SimpleGraph.Adj.reachable (induce_adj_of hC0 hB0 (HexAdj.symm hAdjBC))⟩
      · have hB1 : c B = 1 := fin2_eq_one_of_ne_zero hB0
        by_cases hD0 : c D = 0
        · left
          exact ⟨C, D, hC0, hD0, rfl, rfl, SimpleGraph.Adj.reachable (induce_adj_of hC0 hD0 hAdjCD)⟩
        · have hD1 : c D = 1 := fin2_eq_one_of_ne_zero hD0
          -- A blue, B blue, C red, D blue: blue connects B (top) to D (bottom).
          right
          exact ⟨B, D, hB1, hD1, rfl, rfl, SimpleGraph.Adj.reachable (induce_adj_of hB1 hD1 hAdjBD)⟩

/-
Level B namesake OUT of this ticket (do not sorry):
  theorem hex_no_draw :
      -- every n completed coloring has a winner
First-player win / Gale pairing / Brouwer / Shannon switching /
Bridg-it / CGT Hex (PGame.lean L83) are residual of this id —
do not expand; do not label theorems `hex_no_draw` / `HexTheorem` /
`NashHex` / `GaleHex` / `gale_*` / `nash_*` / `queens_*` /
`mutilated_*` / `domineering_*`.
-/

end ProofLab.HexNoDraw
