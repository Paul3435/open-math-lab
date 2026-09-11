# Hex no-draw small boards (n=1 cell wins / n=2 every coloring has a winner, formalize-only)

**id:** `hex-no-draw`
**ticket:** OPE-1434 Scout leftover slot #2 (parent OPE-1433;
post n-queens #174 + brocard-factorial-square #175)
**expected:** known-classical (Nash 1952 / Gale: a completed
Hex coloring of an `n×n` rhombus has a winner — one player
connects their pair of opposite sides; there is no draw) —
**no novelty claim**

## Why not classical / why formalize-only

Settled connection theorem on a hex rhombus. Pin one
encoding: cells `Fin n × Fin n`. Hex-adjacency is the six
neighbors
`(i±1,j)`, `(i,j±1)`, `(i+1,j-1)`, `(i-1,j+1)` that stay
in-board. A 2-coloring `cell → Fin 2` is a completed game.
Color `0` wins if the left side `{j=0}` meets the right
side `{j=n-1}` in the color-0 subgraph (Mathlib
`SimpleGraph.Reachable`); color `1` wins if top `{i=0}`
meets bottom `{i=n-1}` in the color-1 subgraph.

Small-board witnesses:

- `n = 1`: the unique cell, whatever its color, connects
  both of that color’s sides
- `n = 2`: every 2-coloring of the four cells has a winner
  (no draw)

Completely classical. The namesake “every `n`, first-player
win with perfect play / Gale pairing / Brouwer” is a
**different**, larger residual — do **not** sorry it.
Brouwer was refused as an IVT wrap; do **not** sorry
Brouwer as Hex.

Not an open problem. Not a novelty claim. Not live cash.

**Not** n-queens (consumed #174; attacks ≠ side-connection;
do **not** revive Gauss). **Not** mutilated-chessboard
(prime of this shortlist; 2-coloring as *parity obstruction
to tiling* ≠ 2-coloring as *Hex players*; do **not** prove
opposite-corner color imbalance here). **Not** Domineering
(already-in CGT game; different rules). **Not** Sprague–Grundy
(already-in). **Not** Gale–Shapley (consumed #126; stable
marriage is a different Gale; do **not** label theorems
`gale_*` as Hex). **Not** Nash–Williams arboricity
(consumed #124; different Nash; do **not** label theorems
`nash_*` as Hex). **Not** Gale–Ryser (BvN residual).
**Not** Brooks / greedy / Mycielski / AES graph-coloring
(consumed; `Colorable` Coloring.lean L127 is vertex-coloring
glue **not** namesake — Hex colors *cells*, not a proper
vertex coloring of the hex graph). **Not** friendship /
Moore / Petersen 1-factor (consumed). **Not** Sabidussi
box-product (consumed #139). **Not** British-flag (#145).
**Not** brocard-factorial-square (#175). **Not** Shannon
switching / Bridg-it (residual of this id; do **not** sorry
Shannon; do **not** label theorems `shannon_*`).

Mathlib v4.10.0 already has the **graph / reachability
infra this theorem needs**:

- `Fin` / `Prod`
- `SimpleGraph.Reachable` (Path.lean L628) / `Walk`
- optional `Colorable` (Coloring.lean L127) as *different*
  vertex-coloring glue **not** namesake
- PGame.lean L83 future-work bullet `* Hex.` documents a
  CGT-analysis gap — that is the **namesake residual of
  this id**, not Level A

There is **no** named `hex_no_draw` / `HexTheorem` /
`hex_theorem` / `no_draw` / `NashHex` / `GaleHex` theorem
anywhere under `Mathlib/` or `Archive/` or `ProofLab/`
(this run → ZERO on those names; the only `Hex` hits are
PGame.lean L83 future work and an unrelated `have Hex`
identifier in PrimitiveRoots.lean L439). Do **not** import
`Archive.*`.

OPE-1419 shortlist is **CONSUMED** (#174+#175). This is a
**fresh** catalog-audit leftover id, **not** an n-queens
leftover continuation, **not** a Brocard leftover, **not**
a Domineering leftover-revival, **not** a Gale–Shapley
leftover, **not** a Nash–Williams leftover, **not** a prize
leftover, **not** a Formalist Level B revival, **not** a
third slot.

Mill NOW: finite Hex no-draw witnesses leftover beside
mutilated-chessboard color imbalance. `Reachable` is
waiting the same way `List.Nodup` waited for n-queens.
**Not a rubber-stamp of n-queens.** **Not a rubber-stamp of
Gale–Shapley.** **Not a rubber-stamp of Domineering.**

Do **not** describe an attack as discovering Hex. Do **not**
expand into first-player win / Gale pairing / Brouwer as a
sorry (that is leftover-risk of *this* id — do **not**
sorry it). Do **not** label theorems `gale_*` / `nash_*` /
`queens_*` / `mutilated_*` / `domineering_*` as the
namesake.

## Pinned convention (exact)

**v1 Level A is named small-board witnesses: n=1 the unique
cell wins for its owner, and n=2 every 2-coloring has a
winner, not labelled Hex / Nash / Gale.** Side-connection
via `Reachable` on each color class is load-bearing, so the
theorem is **not** “some function `Fin n × Fin n → Fin 2`
exists.”

Suggested pin:

```text
-- Level A (not labelled Hex / Nash / Gale):
-- named small-board witnesses.

def HexAdj {n : ℕ} : SimpleGraph (Fin n × Fin n) := ...
-- six neighbors (i±1,j), (i,j±1), (i+1,j-1), (i-1,j+1)

def HexColoring (n : ℕ) := (Fin n × Fin n) → Fin 2

def RedWins {n : ℕ} (c : HexColoring n) : Prop :=
  ∃ a b, a.2.val = 0 ∧ b.2.val = n - 1 ∧
    c a = 0 ∧ c b = 0 ∧
    (HexAdj.induce {p | c p = 0}).Reachable a b

def BlueWins {n : ℕ} (c : HexColoring n) : Prop :=
  ∃ a b, a.1.val = 0 ∧ b.1.val = n - 1 ∧
    c a = 1 ∧ c b = 1 ∧
    (HexAdj.induce {p | c p = 1}).Reachable a b

theorem hex_one :
    ∀ c : HexColoring 1, RedWins c ∨ BlueWins c

theorem hex_two :
    ∀ c : HexColoring 2, RedWins c ∨ BlueWins c

-- optional extra: an explicit n=2 red-win coloring

-- Level B namesake (every n; residual OK)
theorem hex_no_draw ...
    -- do not sorry the namesake
```

Named small-board no-draw facts are load-bearing.

**Level A may land only** n=1 cell-wins plus n=2 every
coloring has a winner (optional extra: one explicit n=2
witness coloring), **not** labelled Hex / Nash / Gale.
Reuse Mathlib `Reachable` / `Fin` — **do not re-prove**
n-queens / Gale–Shapley / Nash–Williams / Domineering /
mutilated-chessboard.

**Level B** is the namesake no-draw for every `n`. Do not
sorry it. First-player win / Gale pairing / Brouwer /
Shannon switching / Bridg-it / CGT temperature (PGame.lean
L83) are extras residual.

## Out of v1 this ticket

- No-draw for every `n`
- First-player win with perfect play
- Gale pairing / Brouwer wrap
- Shannon switching / Bridg-it
- CGT Hex analysis (PGame future work)
- mutilated-chessboard (prime of this shortlist)
- n-queens leftover-revivals
- Gale–Shapley / Nash–Williams leftover-revivals
- OPE-403 Happy Ending
- OPE-1195 lame-euclid leftover-status

## Claim

Default **no claim**. Formalize-only. No novelty.
