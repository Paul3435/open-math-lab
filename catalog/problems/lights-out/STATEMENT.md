# Lights Out small boards (n=1 cell-toggle / n=2 all-ones odd chase, formalize-only)

**id:** `lights-out`
**ticket:** OPE-1449 Scout leftover slot #2 (parent OPE-1448;
post mutilated-chessboard #177 + hex-no-draw #178)
**expected:** known-classical (Sutner 1990 / Anderson–Feil
1998 σ-game: pressing a cell toggles it and its orthogonal
neighbors over `ℤ/2ℤ`; all-ones is solvable on small
boards) — **no novelty claim**

## Why not classical / why formalize-only

Settled linear chase on a grid. Pin one encoding: cells
`Fin n × Fin n`. Pressing `p` *affects* `p` and the
orthogonal neighbors that stay in-board. A press set
solves all-ones when every cell is affected an odd number
of times (`ToggleCount % 2 = 1`).

Small-board witnesses:

- `n = 1`: pressing the unique cell toggles it (count 1)
- `n = 2`: pressing all four cells affects each cell three
  times (self + two neighbors), hence odd — all-ones is
  solvable

Completely classical. The namesake “all-ones solvable for
every `n` / classification `n ≢ 0 (mod 3)` / Garden-of-Eden
/ infinite σ-game / chasing lights on the classic 5×5 toy”
is a **different**, larger residual — do **not** sorry it.

Not an open problem. Not a novelty claim. Not live cash.

**Not** mutilated-chessboard (consumed #177; 2-color tiling
obstruction ≠ F2 toggling; same `Fin n × Fin n` grid is
*glue*, **not** namesake; do **not** label theorems
`mutilated_*`). **Not** hex-no-draw (consumed #178;
Reachable connection ≠ toggle parity; do **not** label
theorems `hex_*`). **Not** n-queens (consumed #174;
non-attacking placement ≠ chase). **Not** Domineering
(already-in *game* on a grid; different theorem; do **not**
label theorems `domineering_*`). **Not** Sprague–Grundy
(already-in CGT). **Not** Gray-code (consumed #163;
Hamming listings ≠ toggle supports). **Not** OLS
(consumed #157). **Not** Langford (consumed #160).
**Not** British-flag (consumed #145). **Not** Hall
(already-in). **Not** Sylvester–Gallai (prime of this
shortlist; incidence ordinary lines ≠ F2 chase). **Not**
Garden-of-Eden / cellular-automata residual of *this* id
(do **not** sorry Sutner’s Garden-of-Eden criterion).

Mathlib v4.10.0 already has the **grid / F2 infra this
theorem needs**:

- `Fin` / `Fin.val` / `Prod` / `Finset`
- `Finset.card` as count glue **not** namesake
- `CharP.Two.add_self_eq_zero` (Algebra/CharP/Two.lean L30)
  as characteristic-2 glue **not** namesake
- optional `ZMod 2` as the toggle ring **not** namesake

There is **no** named `lights_out` / `LightsOut` / `sutner`
/ `Sutner` / `sigma_game` theorem anywhere under `Mathlib/`
or `Archive/` or `ProofLab/` (this run → ZERO on those
names). Do **not** import `Archive.*`.

OPE-1434 shortlist is **CONSUMED** (#177+#178). This is a
**fresh** catalog-audit leftover id, **not** a mutilated
leftover continuation, **not** a Hex leftover, **not** a
Domineering leftover-revival, **not** a prize leftover,
**not** a Formalist Level B revival, **not** a third slot.

Mill NOW: finite odd-chase witnesses on Mathlib `Fin` /
`Finset.card` / char-2. **Not a rubber-stamp of
mutilated-chessboard.** **Not a rubber-stamp of Hex.**
**Not a rubber-stamp of Domineering.**

Do **not** describe an attack as discovering Lights Out.
Do **not** expand into the namesake every-`n` / 5×5
classification as a sorry (that is leftover-risk of
*this* id — do **not** sorry it). Do **not** label
theorems `mutilated_*` / `hex_*` / `queens_*` /
`domineering_*` / `sg_*` as the namesake.

## Pinned convention (exact)

**v1 Level A is named small-board witnesses: n=1
cell-toggle and n=2 all-four-press odd chase, not labelled
Lights Out / Sutner.** Odd affect-counts are load-bearing,
so the theorem is **not** “some Finset of Fin n × Fin n
has even cardinality.”

Suggested pin:

```text
-- Level A (not labelled Lights Out / Sutner):
-- named small-board witnesses.

def Neighbor4 {n : ℕ} (p q : Fin n × Fin n) : Prop :=
  (p.1 = q.1 ∧ (p.2.val + 1 = q.2.val ∨ q.2.val + 1 = p.2.val)) ∨
  (p.2 = q.2 ∧ (p.1.val + 1 = q.1.val ∨ q.1.val + 1 = p.1.val))

def Affects {n : ℕ} (press p : Fin n × Fin n) : Prop :=
  press = p ∨ Neighbor4 press p

def ToggleCount {n : ℕ}
    (presses : Finset (Fin n × Fin n)) (cell : Fin n × Fin n) : ℕ :=
  (presses.filter (fun pr => Affects pr cell)).card

theorem lights_one :
    ToggleCount ({(0, 0)} : Finset (Fin 1 × Fin 1)) (0, 0) % 2 = 1

theorem lights_two_all_ones :
    let presses : Finset (Fin 2 × Fin 2) :=
      {(0, 0), (0, 1), (1, 0), (1, 1)}
    ∀ c : Fin 2 × Fin 2, ToggleCount presses c % 2 = 1

-- optional extra: n=2 a singleton press is even on the
-- opposite corner (not a full all-ones solve)
-- theorem lights_two_corner_even : ...

-- Level B namesake (every n / 5×5 classification;
-- residual OK)
theorem lights_out ...
    -- do not sorry the namesake
```

Named small-board odd-chase facts are load-bearing.

**Level A may land only** the n=1 cell-toggle plus the n=2
all-four-press odd chase (optional extra: a non-solving
press pattern), **not** labelled Lights Out / Sutner.
Reuse Mathlib `Fin` / `Finset.card` / `CharP.Two.add_self_eq_zero`
— **do not re-prove** mutilated / Hex / Domineering.

**Level B** is the namesake all-ones solvable for every `n`
(or the classical `n ≢ 0 (mod 3)` criterion / 5×5 toy).
Do not sorry it. Garden-of-Eden / infinite σ-game are
extras residual.

## Out of v1 this ticket

- namesake every `n` / `n ≢ 0 (mod 3)` classification
- classic 5×5 Lights Out solvability
- Garden-of-Eden / Sutner criterion
- infinite σ-game / cellular automata
- mutilated / Hex leftover-revivals
- Sylvester–Gallai (prime of this shortlist)
- OPE-403 Happy Ending
- OPE-1195 lame-euclid leftover-status

## Claim

Default **no claim**. Formalize-only. No novelty.
