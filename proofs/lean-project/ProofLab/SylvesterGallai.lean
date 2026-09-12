/-
Named small-set ordinary-line witnesses — Level A only
(3-collinear row plus off-line plus ordinary vertical card=2).
**Not labelled Sylvester / Gallai.**

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 pin `a719ba5c3115` has `Int` / `HMul` / `HSub` /
`Finset.card` / `card_eq_two` (Card.lean L696) as **infra**.
Optional `Collinear` (AffineSpace/FiniteDimensional.lean L353) is
affine glue **not** namesake — Level A uses the det encoding
instead and does **not** re-prove `Collinear`. ZERO named
`sylvester_gallai` / `SylvesterGallai` / `ordinary_line` /
`OrdinaryLine` / `gallai_sylvester` under `Mathlib/` or `Archive/`
or `ProofLab/` (this run). Completing the Level A named small-set
incidence facts is the gap this ticket lands. The Level B namesake
`sylvester_gallai` (every finite non-collinear planar set has an
ordinary line) is **out of this ticket** and is **not** sorry-ed.
Kelly closest-point / Melchior / Dirac–Motzkin / de Bruijn–Erdős
incidence extras are residual of this id. Do **not** label theorems
`sylvester_gallai` / `ordinary_line` / `OrdinaryLine` / `heron_*` /
`british_flag_*` / `shoelace_*` / `pick_*` / `ceva_*` / `inertia_*` /
`sylvester_*` (sequence) / `mutilated_*` / `hex_*` / `lights_*` as
the namesake.

Pin: `catalog/problems/sylvester-gallai/STATEMENT.md`
(OPE-1455; Scout OPE-1449 RECOMMENDED PRIME; Director OPE-1454 APPROVE).
Encoding: points `ℤ × ℤ`; `collinearDet` signed parallelogram area;
`Pts` four-point set; ordinary = filter card = 2. Zero `sorry`.
Do not import `Archive.*`.

This is **not** `Int` / `HMul` / `HSub` / `Finset.card` /
`card_eq_two` — already Mathlib. **USE, do not re-prove; do not
cite as Sylvester–Gallai.**
This is **not** `Collinear` (AffineSpace/FiniteDimensional.lean L353).
Affine glue, **not** namesake. Do **not** re-prove `Collinear`.
This is **not** Sylvester inertia
(`equivalent_one_neg_one_weighted_sum_squared`,
QuadraticForm/Real.lean L52). Different Sylvester. Do **not**
label theorems `inertia_*`.
This is **not** Sylvester sequence / greedy Egyptian
(`ProofLab/EgyptianFractions.lean` `sylvesterGreedy`, consumed #148).
Different Sylvester. Do **not** label theorems `sylvester_*` as
this namesake.
This is **not** Heron (`ProofLab/Heron.lean`, consumed #83).
Area formula ≠ ordinary line. Heron.lean L19 already distinguishes
SG. Do **not** label theorems `heron_*`.
This is **not** British-flag (`ProofLab/BritishFlag.lean`, consumed
#145). Euclidean `dist` pairing ≠ incidence. Do **not** revive
Napoleon / Simson / Viviani. Do **not** label theorems
`british_flag_*`.
This is **not** Alcuin (`ProofLab/AlcuinIntegerTriangles.lean`,
consumed #153). Integer-side triangles ≠ incidence. Do **not**
revive Heronian / Pick. Do **not** label theorems `pick_*` /
`shoelace_*` / `ceva_*`.
This is **not** mutilated-chessboard
(`ProofLab/MutilatedChessboard.lean`, consumed #177). Board
2-coloring ≠ point-line incidence. Do **not** label theorems
`mutilated_*`.
This is **not** hex-no-draw (`ProofLab/HexNoDraw.lean`, consumed
#178). Hex connection ≠ ordinary lines. Do **not** label theorems
`hex_*`.
This is **not** n-queens (`ProofLab/NQueens.lean`, consumed #174).
This is **not** brocard-factorial-square
(`ProofLab/BrocardFactorialSquare.lean`, consumed #175).
This is **not** Lights Out (OPE-1449 leftover HOLD). Do **not**
prove `n=1` cell-toggle / `n=2` odd chase / `lights_out` /
`LightsOut` / `sutner` / `sigma_game` here. Do **not** label
theorems `lights_*`.
Do not re-prime the consumed mill. Leave OPE-403 alone.
Leave OPE-1195 alone.

v1 is named small-set witnesses: three collinear on a row
`(0,0)/(1,0)/(2,0)`, one off-line `(0,1)`, and the vertical
through `(0,0)` and `(0,1)` meeting the four-point set in
exactly two points, **not labelled Sylvester / Gallai**.
Collinearity of the row and “the vertical meets the set in
exactly two points” are load-bearing (so Level A is **not**
“some Finset of ℤ × ℤ has cardinality 4”).

Level A: `sg_three_collinear` / `sg_off_line` /
`sg_ordinary_vertical`. Optional extra: the base line through
`(0,0)` and `(1,0)` meets `Pts` in three points (not ordinary).
**Not** labelled Sylvester / Gallai.

Transcribed classical argument (Sylvester 1893 / Gallai 1944;
small-set ordinary-line witness). Compact form: Wikipedia
*Sylvester–Gallai theorem*. Type pin: `ℤ × ℤ` / `collinearDet` /
`Finset.card`. Heron / British-flag / Alcuin are different
consumed theorems. Lights Out is the leftover of this shortlist.
No novelty claim. Default no claim.

Level B namesake OUT of this ticket (do not sorry):
-- theorem sylvester_gallai ...
--     -- every finite non-collinear set; do not sorry the namesake
-/
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace ProofLab.SylvesterGallai

/-! ## Encoding: det collinearity on ℤ × ℤ
(not labelled Sylvester / Gallai) -/

/-- Signed parallelogram area vanishes. Encoding; **not** labelled
Sylvester / Gallai. Glue: Mathlib `Int` / `HMul` / `HSub`.
Does **not** re-prove `Collinear`. -/
def collinearDet (a b c : ℤ × ℤ) : Prop :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1) = 0

/-- Det equality is decidable (Mathlib `Int` / `DecidableEq`). Glue;
not labelled Sylvester / Gallai. -/
instance collinearDet.decidable (a b c : ℤ × ℤ) :
    Decidable (collinearDet a b c) :=
  inferInstanceAs (Decidable (_ = 0))

/-- Four-point set: three on a row plus one off-line. Encoding;
**not** labelled Sylvester / Gallai. Glue: Mathlib `Finset`.
Level A is **not** “this Finset has cardinality 4.” -/
def Pts : Finset (ℤ × ℤ) := {(0, 0), (1, 0), (2, 0), (0, 1)}

/-! ## Level A: named small-set witnesses
(not labelled Sylvester / Gallai) -/

/-- Three collinear on the row `(0,0)`, `(1,0)`, `(2,0)`.
Load-bearing det vanishing. Glue; **not** labelled Sylvester /
Gallai. -/
theorem sg_three_collinear :
    collinearDet (0, 0) (1, 0) (2, 0) := by
  unfold collinearDet
  norm_num

/-- Off-line point `(0,1)` is not collinear with `(0,0)` and
`(1,0)`. Load-bearing det non-vanishing. Glue; **not** labelled
Sylvester / Gallai. -/
theorem sg_off_line :
    ¬ collinearDet (0, 0) (1, 0) (0, 1) := by
  unfold collinearDet
  norm_num

/-- The vertical through `(0,0)` and `(0,1)` meets `Pts` in
exactly two points (ordinary line). Load-bearing filter card.
Glue: Mathlib `Finset.card` / `card_eq_two` (Card.lean L696).
**Not** labelled Sylvester / Gallai. -/
theorem sg_ordinary_vertical :
    (Pts.filter (fun p => collinearDet (0, 0) (0, 1) p)).card = 2 := by
  rw [Finset.card_eq_two]
  refine ⟨(0, 0), (0, 1), by decide, ?_⟩
  decide

/-- Optional extra: the base line through `(0,0)` and `(1,0)`
meets `Pts` in three points (not ordinary). Glue; **not**
labelled Sylvester / Gallai. -/
theorem sg_base_not_ordinary :
    (Pts.filter (fun p => collinearDet (0, 0) (1, 0) p)).card = 3 := by
  decide

/-
Level B namesake OUT of this ticket (do not sorry):
  theorem sylvester_gallai :
      -- every finite non-collinear planar set has an ordinary line
Kelly closest-point / Melchior double counting / Dirac–Motzkin
ordinary-line counts / de Bruijn–Erdős incidence are residual of
this id — do not expand; do not label theorems `sylvester_gallai` /
`ordinary_line` / `OrdinaryLine` / `heron_*` / `british_flag_*` /
`shoelace_*` / `pick_*` / `ceva_*` / `inertia_*` / `sylvester_*`
(sequence) / `mutilated_*` / `hex_*` / `lights_*`.
-/

end ProofLab.SylvesterGallai
