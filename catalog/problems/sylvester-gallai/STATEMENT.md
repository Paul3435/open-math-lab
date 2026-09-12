# Sylvester–Gallai ordinary-line witness (3-collinear plus off-line, formalize-only)

**id:** `sylvester-gallai`
**ticket:** OPE-1449 Scout RECOMMENDED PRIME (parent OPE-1448;
post mutilated-chessboard #177 + hex-no-draw #178)
**expected:** known-classical (Sylvester 1893 / Gallai 1944:
a finite non-collinear point set in the plane has an
*ordinary line* — a line containing exactly two of the
points) — **no novelty claim**

## Why not classical / why formalize-only

Settled incidence theorem. Pin one encoding: points
`ℤ × ℤ`. Three points `a,b,c` are collinear when the
signed parallelogram area vanishes
`(b.1-a.1)*(c.2-a.2) - (b.2-a.2)*(c.1-a.1) = 0`.
An ordinary line through two distinct points `p,q` of a
finite set `S` meets `S` in exactly those two points.

Small-set witnesses:

- three collinear on a row: `(0,0)`, `(1,0)`, `(2,0)`
- one off-line: `(0,1)`
- the vertical through `(0,0)` and `(0,1)` is ordinary
  (exactly two of the four points)

Completely classical. The namesake “every finite
non-collinear set in `ℝ²` has an ordinary line / Kelly
closest-point / Melchior double counting / Dirac–Motzkin
ordinary-line counts” is a **different**, larger residual
— do **not** sorry it.

Not an open problem. Not a novelty claim. Not live cash.

**Not** British-flag (consumed #145; Euclidean `dist`
pairing on a square ≠ incidence ordinary lines; do **not**
revive Napoleon / Simson / Viviani). **Not** Heron
(consumed #83; triangle area formula ≠ ordinary line;
ProofLab/Heron.lean already says this is not
Sylvester–Gallai). **Not** Alcuin (consumed #153;
integer-side triangles ≠ incidence; do **not** revive
Heronian / Pick). **Not** Wantzel (consumed #133;
constructible numbers ≠ ordinary lines; do **not** revive
angle trisection). **Not** Pick / Ceva / Varignon /
shoelace / Menelaus / Desargues / Pappus / Morley / art
gallery (geometry leftover of Heron / #145 / Alcuin /
Wantzel; shoelace-det is *glue*, **not** namesake).
**Not** platonic-solids (consumed #147). **Not** mutilated-chessboard
(consumed #177; board 2-coloring ≠ point-line incidence).
**Not** hex-no-draw (consumed #178; Hex connection ≠
ordinary lines). **Not** n-queens (consumed #174;
placement ≠ incidence). **Not** Sylvester *inertia*
(already-in `QuadraticForm/Real.lean` L52; signatures ≠
ordinary lines; do **not** label theorems `inertia_*`).
**Not** Sylvester *sequence* / greedy Egyptian
(consumed #148 `sylvesterGreedy`; different Sylvester;
do **not** label theorems `sylvester_*` as this namesake).
**Not** Lights Out (leftover of this shortlist; F2 toggling
≠ incidence).

Mathlib v4.10.0 already has the **integer / collinearity
infra this theorem needs**:

- `Int` / `HMul` / `HSub` / `Finset`
- `Finset.card` / `card_eq_two` (Card.lean L696) as
  cardinality glue **not** namesake
- optional `Collinear` (AffineSpace/FiniteDimensional.lean
  L353) as affine collinearity glue **not** namesake —
  Level A may use the det encoding instead; do **not**
  re-prove `Collinear`

There is **no** named `sylvester_gallai` / `SylvesterGallai`
/ `ordinary_line` / `OrdinaryLine` / `gallai_sylvester`
theorem anywhere under `Mathlib/` or `Archive/` or
`ProofLab/` (this run → ZERO on those names; `sylvester`
hits are inertia L52, Egyptian greedy, and Heron.lean L19
explicitly *distinguishing* SG as a different statement).
Do **not** import `Archive.*`.

OPE-1434 shortlist is **CONSUMED** (#177+#178). This is a
**fresh** catalog-audit prime, **not** a mutilated leftover
continuation, **not** a Hex leftover, **not** a Heron
leftover-revival, **not** a British-flag leftover, **not**
a prize leftover, **not** a Formalist Level B revival,
**not** a third slot.

Mill NOW: finite ordinary-line witnesses on Mathlib `Int`
/ det / `Finset.card`. **Not a rubber-stamp of Heron.**
**Not a rubber-stamp of British-flag.** **Not a
rubber-stamp of mutilated-chessboard.**

Do **not** describe an attack as discovering
Sylvester–Gallai. Do **not** expand into the namesake
“every finite non-collinear set” as a sorry (that is
leftover-risk of *this* id — do **not** sorry it). Do
**not** label theorems `heron_*` / `british_flag_*` /
`shoelace_*` / `pick_*` / `ceva_*` / `inertia_*` /
`sylvester_*` (sequence) / `mutilated_*` / `hex_*` /
`lights_*` as the namesake.

## Pinned convention (exact)

**v1 Level A is named small-set witnesses: three collinear
plus one off-line, and one ordinary line through the
off-line point, not labelled Sylvester / Gallai.**
Collinearity of the row and “the vertical meets the set
in exactly two points” are load-bearing, so the theorem
is **not** “some Finset of ℤ × ℤ has cardinality 4.”

Suggested pin:

```text
-- Level A (not labelled Sylvester / Gallai):
-- named small-set witnesses.

def collinearDet (a b c : ℤ × ℤ) : Prop :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1) = 0

def Pts : Finset (ℤ × ℤ) := {(0, 0), (1, 0), (2, 0), (0, 1)}

theorem sg_three_collinear :
    collinearDet (0, 0) (1, 0) (2, 0)

theorem sg_off_line :
    ¬ collinearDet (0, 0) (1, 0) (0, 1)

theorem sg_ordinary_vertical :
    (Pts.filter (fun p => collinearDet (0, 0) (0, 1) p)).card = 2

-- optional extra: the base line through (0,0) and (1,0)
-- meets Pts in three points (not ordinary)
-- theorem sg_base_not_ordinary : ...

-- Level B namesake (every finite non-collinear set;
-- residual OK)
theorem sylvester_gallai ...
    -- do not sorry the namesake
```

Named small-set incidence facts are load-bearing.

**Level A may land only** the 3-collinear row plus
off-line point plus one ordinary line (optional extra:
the base line is *not* ordinary), **not** labelled
Sylvester / Gallai. Reuse Mathlib `Int` / `Finset.card`
— **do not re-prove** Heron / British-flag / Pick /
`Collinear` as namesake.

**Level B** is the namesake every finite non-collinear
planar set. Do not sorry it. Kelly closest-point /
Melchior / Dirac–Motzkin counts / de Bruijn–Erdős
incidence `n` points ⇒ `n` lines are extras residual.

## Out of v1 this ticket

- namesake every finite non-collinear set
- Kelly closest-point sink / Melchior double counting
- Dirac–Motzkin ordinary-line lower bounds
- de Bruijn–Erdős incidence theorem
- Pick / Ceva / shoelace / Varignon as namesake
- Sylvester inertia / Sylvester sequence
- Lights Out (leftover of this shortlist)
- OPE-403 Happy Ending
- OPE-1195 lame-euclid leftover-status

## Claim

Default **no claim**. Formalize-only. No novelty.
