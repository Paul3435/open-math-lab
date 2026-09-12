/-
Named small-board odd-chase witnesses — Level A only
(n=1 cell-toggle / n=2 all-four-press odd chase).
**Not labelled Lights Out / Sutner.**

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 pin `a719ba5c3115` has `Fin` / `Fin.val` / `Prod` /
`Finset.card` / `CharTwo.add_self_eq_zero` (Algebra/CharP/Two.lean L30;
Scout alias `CharP.Two.add_self_eq_zero`) as **infra**. Optional
`ZMod 2` is the toggle ring **not** namesake. ZERO named `lights_out` /
`LightsOut` / `sutner` / `Sutner` / `sigma_game` / `SigmaGame` under
`Mathlib/` or `Archive/` or `ProofLab/` (this run). Completing the
Level A named small-board odd-chase facts is the gap this ticket lands.
The Level B namesake `lights_out` (all-ones solvable for every n /
n ≢ 0 (mod 3) / 5×5 toy) is **out of this ticket** and is **not**
sorry-ed. Garden-of-Eden / Sutner criterion / infinite σ-game /
cellular automata are residual of this id. Do **not** label theorems
`lights_out` / `LightsOut` / `sutner` / `Sutner` / `sigma_game` /
`mutilated_*` / `hex_*` / `queens_*` / `sg_*` / `sylvester_*` /
`ordinary_line` / `domineering_*` as the namesake.

Pin: `catalog/problems/lights-out/STATEMENT.md`
(OPE-1460; Scout OPE-1449 leftover HOLD; Director OPE-1459 APPROVE).
Encoding: cells `Fin n × Fin n`; `Neighbor4` / `Affects` / `ToggleCount`.
Zero `sorry`. Do not import `Archive.*`.

This is **not** `Fin` / `Prod` / `Finset.card` /
`CharTwo.add_self_eq_zero` — already Mathlib. **USE, do not re-prove;
do not cite as Lights Out.**
This is **not** mutilated-chessboard (`ProofLab/MutilatedChessboard.lean`,
consumed #177). 2-color tiling obstruction ≠ F2 toggling. Same
`Fin n × Fin n` grid is *glue*, **not** namesake. Do **not** label
theorems `mutilated_*`.
This is **not** hex-no-draw (`ProofLab/HexNoDraw.lean`, consumed #178).
Reachable connection ≠ toggle parity. Do **not** label theorems `hex_*`.
This is **not** n-queens (`ProofLab/NQueens.lean`, consumed #174).
Non-attacking placement ≠ chase. Do **not** label theorems `queens_*`.
This is **not** Gray-code (`ProofLab/GrayCode.lean`, consumed #163).
Hamming listings ≠ toggle supports. Do **not** label theorems `gray_*`.
This is **not** Domineering (`SetTheory/Game/Domineering.lean`).
Already-in CGT *game*, different theorem. Do **not** re-prove; do **not**
label theorems `domineering_*`.
This is **not** Sylvester–Gallai (`ProofLab/SylvesterGallai.lean`,
consumed #180). Incidence ordinary lines ≠ F2 chase. Do **not** prove
`sg_three_collinear` / `sg_off_line` / `sg_ordinary_vertical` /
`collinearDet` leftover-revivals. Do **not** label theorems `sg_*` /
`sylvester_*` / `ordinary_line`.
This is **not** brocard-factorial-square
(`ProofLab/BrocardFactorialSquare.lean`, consumed #175).
Do not re-prime the consumed mill. Leave OPE-403 alone.
Leave OPE-1195 alone.

v1 is named small-board witnesses: n=1 pressing the unique cell
toggles it (count 1), n=2 pressing all four cells affects each cell
three times (self + two orthogonal neighbors), hence odd — all-ones
is solvable, **not labelled Lights Out / Sutner**. Odd affect-counts
are load-bearing (so Level A is **not** “some Finset of Fin n × Fin n
has even cardinality”).

Level A: `lights_one` / `lights_two_all_ones`. Optional extra:
`lights_two_corner_even` (singleton press is even on the opposite
corner; not a full all-ones solve). **Not** labelled Lights Out /
Sutner.

Transcribed classical argument (Sutner 1990 / Anderson–Feil 1998
σ-game). Compact form: Wikipedia *Lights Out (game)*. Type pin:
`Fin n × Fin n` / `Neighbor4` / `Affects` / `ToggleCount`.
Mutilated-chessboard is a different consumed theorem. Hex-no-draw
is a different consumed theorem. Sylvester–Gallai is the consumed
prime of this shortlist. No novelty claim. Default no claim.

Level B namesake OUT of this ticket (do not sorry):
-- theorem lights_out ...
--     -- every n / n ≢ 0 (mod 3) / 5×5; do not sorry the namesake
-/
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.Finset.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace ProofLab.LightsOut

/-! ## Encoding: orthogonal chase on `Fin n × Fin n`
(not labelled Lights Out / Sutner) -/

/-- Orthogonal in-board neighbors (4-adjacency). Encoding; **not**
labelled Lights Out / Sutner. Glue: Mathlib `Fin` / `Prod`.
Does **not** re-prove mutilated / Hex / Domineering. -/
def Neighbor4 {n : ℕ} (p q : Fin n × Fin n) : Prop :=
  (p.1 = q.1 ∧ (p.2.val + 1 = q.2.val ∨ q.2.val + 1 = p.2.val)) ∨
  (p.2 = q.2 ∧ (p.1.val + 1 = q.1.val ∨ q.1.val + 1 = p.1.val))

/-- A press affects its own cell and its orthogonal in-board
neighbors. Encoding; **not** labelled Lights Out / Sutner. -/
def Affects {n : ℕ} (press p : Fin n × Fin n) : Prop :=
  press = p ∨ Neighbor4 press p

instance neighbor4Decidable {n : ℕ} (p q : Fin n × Fin n) :
    Decidable (Neighbor4 p q) := by
  unfold Neighbor4
  infer_instance

instance affectsDecidable {n : ℕ} (press p : Fin n × Fin n) :
    Decidable (Affects press p) := by
  unfold Affects
  infer_instance

/-- Number of presses that affect `cell`. Encoding; **not** labelled
Lights Out / Sutner. Glue: Mathlib `Finset.card`. Load-bearing odd
counts — Level A is **not** “some Finset has even cardinality.” -/
def ToggleCount {n : ℕ}
    (presses : Finset (Fin n × Fin n)) (cell : Fin n × Fin n) : ℕ :=
  (presses.filter (fun pr => Affects pr cell)).card

/-- Pressing twice is zero in characteristic 2. Glue: Mathlib
`CharTwo.add_self_eq_zero` (Algebra/CharP/Two.lean L30). Optional
`ZMod 2` is the toggle ring **not** namesake. **USE, do not re-prove;
do not cite as Lights Out / Sutner.** -/
lemma press_twice_zero (x : ZMod 2) : x + x = 0 :=
  CharTwo.add_self_eq_zero x

/-- Nat double is even, via the char-2 glue. **Not** labelled Lights
Out / Sutner. -/
lemma even_double (k : ℕ) : (k + k) % 2 = 0 := by
  have h : ((k + k : ℕ) : ZMod 2) = 0 := by
    rw [Nat.cast_add]
    exact press_twice_zero (k : ZMod 2)
  have hdvd : 2 ∣ k + k := (ZMod.natCast_zmod_eq_zero_iff_dvd (k + k) 2).mp h
  exact Nat.mod_eq_zero_of_dvd hdvd

/-! ## Level A: named small-board witnesses
(not labelled Lights Out / Sutner) -/

/-- n=1: pressing the unique cell toggles it (count 1, odd).
Load-bearing odd affect-count. Glue; **not** labelled Lights Out /
Sutner. -/
theorem lights_one :
    ToggleCount ({(0, 0)} : Finset (Fin 1 × Fin 1)) (0, 0) % 2 = 1 := by
  unfold ToggleCount
  rw [Finset.filter_singleton]
  have hA : Affects ((0 : Fin 1), (0 : Fin 1)) (0, 0) := Or.inl rfl
  rw [if_pos hA, Finset.card_singleton]

/-- The four-cell press set on the 2×2 board. Encoding; **not**
labelled Lights Out / Sutner. -/
def allFour : Finset (Fin 2 × Fin 2) := {(0, 0), (0, 1), (1, 0), (1, 1)}

/-- Each cell on the 2×2 board is affected three times by `allFour`
(self + two orthogonal neighbors). Load-bearing count. Glue: Mathlib
`Finset.card`. **Not** labelled Lights Out / Sutner. -/
lemma toggleCount_allFour (c : Fin 2 × Fin 2) :
    ToggleCount allFour c = 3 := by
  rcases c with ⟨i, j⟩
  fin_cases i <;> fin_cases j
  all_goals
    unfold ToggleCount allFour
    decide

/-- n=2: pressing all four cells affects every cell an odd number of
times (all-ones chase). Load-bearing odd affect-counts. Glue; **not**
labelled Lights Out / Sutner. -/
theorem lights_two_all_ones :
    ∀ c : Fin 2 × Fin 2, ToggleCount allFour c % 2 = 1 := by
  intro c
  rw [toggleCount_allFour]

/-- Optional extra: n=2 a singleton press is even on the opposite
corner (not a full all-ones solve). Glue; **not** labelled Lights Out /
Sutner. -/
theorem lights_two_corner_even :
    ToggleCount ({(0, 0)} : Finset (Fin 2 × Fin 2)) (1, 1) % 2 = 0 := by
  unfold ToggleCount
  rw [Finset.filter_singleton]
  have hA : ¬ Affects ((0 : Fin 2), (0 : Fin 2)) (1, 1) := by
    unfold Affects Neighbor4
    decide
  rw [if_neg hA, Finset.card_empty]

/-
Level B namesake OUT of this ticket (do not sorry):
  theorem lights_out :
      -- all-ones solvable for every n / n ≢ 0 (mod 3) / 5×5 toy
Garden-of-Eden / Sutner criterion / infinite σ-game / cellular
automata are residual of this id — do not expand; do not label
theorems `lights_out` / `LightsOut` / `sutner` / `Sutner` /
`sigma_game` / `mutilated_*` / `hex_*` / `queens_*` / `sg_*` /
`sylvester_*` / `ordinary_line` / `domineering_*`.
-/

end ProofLab.LightsOut
