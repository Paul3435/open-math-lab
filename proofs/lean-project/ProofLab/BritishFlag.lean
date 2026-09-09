/-
British flag theorem — Level A only (unit-square origin / vertex C /
centre). **Not labelled British flag / parallelogram law / Napoleon.**

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 pin `a719ba5c3115` has `EuclideanSpace` /
`EuclideanSpace.single` / `dist` / `parallelogram_law` as **infra**.
ZERO named British flag / `britishFlag` / `british_flag` /
`BritishFlag` / Napoleon / Simson / Viviani under `Mathlib/` or
`Archive/` or `ProofLab/`. Completing the Level A unit-square origin /
vertex C / centre glue is the gap this ticket lands. The Level B
namesake `british_flag` (every point of the plane of an axis-aligned
rectangle) is **out of this ticket** and is **not** sorry-ed.
Napoleon / Simson / Viviani / nine-point / angle-bisector extras are
residual of this id.

Pin: `catalog/problems/british-flag/STATEMENT.md`
(OPE-1273; Scout OPE-1263 leftover slot #2; Director OPE-1272).
Encoding: axis-aligned unit square in `EuclideanSpace ℝ (Fin 2)` via
`EuclideanSpace.single`. Zero `sorry`. Do not import `Archive.*`.

This is **not** `EuclideanSpace` (`PiL2.lean` L100) — already Mathlib.
**USE, do not re-prove; do not cite as British flag.**
This is **not** `EuclideanSpace.single` (`PiL2.lean` L223) — already
Mathlib. **USE, do not re-prove.**
This is **not** `dist` (metric) — already Mathlib. **USE, do not
re-prove.**
This is **not** `parallelogram_law` (`InnerProductSpace/Basic.lean`
L590) — DIFFERENT already-in identity
`‖x+y‖² + ‖x−y‖² = 2(‖x‖²+‖y‖²)`. **USE only as optional extra glue;
do not re-prove; do not cite as British flag.**
This is **not** Ptolemy (`Sphere/Ptolemy.lean`) / law of cosines
(`Triangle.lean`) / Euler line (`MongePoint.lean`) — DIFFERENT
already-in Euclidean theorems.
This is **not** Heron (`ProofLab/Heron.lean`, consumed) / Wantzel
(`ProofLab/WantzelConstructible.lean`, PR #133).
This is **not** Fine–Wilf (`ProofLab/FineWilf.lean`, PR #144) /
Lyndon–Schützenberger / Kraft.
This is **not** Sherman–Morrison (`ProofLab/ShermanMorrison.lean`,
PR #141) / Woodbury.
This is **not** Graham–Pollak (`ProofLab/GrahamPollak.lean`, PR #142)
/ biclique cover / Zarankiewicz.
Do not re-prime the consumed mill. Leave OPE-403 alone.
Leave OPE-1195 alone. Do **not** prove Napoleon / Simson / Viviani
here (residual of this id).

v1 is the identity on an axis-aligned unit square in
`EuclideanSpace ℝ (Fin 2)` at named points: origin, vertex C, and
the centre, **not labelled British flag**. Opposite-corner pairing
is load-bearing. `dist` squared is load-bearing. Axis-aligned
rectangle in `Fin 2` is load-bearing.

Level A: unit square `A=(0,0)`, `B=(1,0)`, `C=(1,1)`, `D=(0,1)`.
At the origin, `PA²+PC² = 0+2 = 2` and `PB²+PD² = 1+1 = 2`.
At vertex C, `CA²+CC² = 2+0` and `CB²+CD² = 1+1`.
At the centre `(1/2,1/2)` all four distances squared equal
`1/2+1/2`. **Not** labelled British flag.

Transcribed classical argument (British flag / Union-Jack identity;
a coordinate calculation). Compact form: Wikipedia *British flag
theorem*. Type pin: `EuclideanSpace ℝ (Fin 2)` / `dist` /
axis-aligned corners. `parallelogram_law` is a different already-in
identity. Napoleon is a different residual theorem. No novelty
claim. Default no claim.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

set_option linter.unusedVariables false

namespace ProofLab.BritishFlag

/-- Plane of the axis-aligned unit square. Glue; **not** labelled
British flag. Uses Mathlib `EuclideanSpace`; does **not** re-prove
it. -/
abbrev Plane2 := EuclideanSpace ℝ (Fin 2)

noncomputable section

/-- Unit-square corner `A = (0,0)`. Encoding; **not** labelled
British flag. -/
def unitA : Plane2 := EuclideanSpace.single (0 : Fin 2) 0

/-- Unit-square corner `B = (1,0)`. Encoding; **not** labelled
British flag. -/
def unitB : Plane2 := EuclideanSpace.single (0 : Fin 2) 1

/-- Unit-square corner `C = (1,1)`. Encoding; **not** labelled
British flag. -/
def unitC : Plane2 :=
  EuclideanSpace.single (0 : Fin 2) 1 + EuclideanSpace.single (1 : Fin 2) 1

/-- Unit-square corner `D = (0,1)`. Encoding; **not** labelled
British flag. -/
def unitD : Plane2 := EuclideanSpace.single (1 : Fin 2) 1

/-- Squared Euclidean distance on `Fin 2` is the sum of squared
coordinate differences. Uses Mathlib `EuclideanSpace.dist_eq`;
does **not** re-prove inner product or `parallelogram_law`.
Glue; **not** labelled British flag. -/
theorem dist_sq_fin_two (p q : Plane2) :
    dist p q ^ 2 = (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 := by
  have hsum : 0 ≤ ∑ i : Fin 2, dist (p i) (q i) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt hsum, Fin.sum_univ_two]
  simp [dist_eq_norm, Real.norm_eq_abs, sq_abs]

/-! ## Level A: unit-square origin / vertex C / centre
(not labelled British flag) -/

/-- Opposite-corner pairing at the origin of the unit square.
Glue; **not** labelled British flag. -/
theorem british_flag_unit_origin :
    dist (0 : Plane2) unitA ^ 2 + dist 0 unitC ^ 2
      = dist 0 unitB ^ 2 + dist 0 unitD ^ 2 := by
  simp only [dist_sq_fin_two, unitA, unitB, unitC, unitD,
    EuclideanSpace.single_apply, PiLp.zero_apply]
  norm_num

/-- Opposite-corner pairing at vertex `C` of the unit square.
Glue; **not** labelled British flag. -/
theorem british_flag_unit_at_C :
    dist unitC unitA ^ 2 + dist unitC unitC ^ 2
      = dist unitC unitB ^ 2 + dist unitC unitD ^ 2 := by
  simp only [dist_sq_fin_two, unitA, unitB, unitC, unitD,
    EuclideanSpace.single_apply]
  norm_num

/-- Opposite-corner pairing at the centre `(1/2, 1/2)` of the unit
square. Glue; **not** labelled British flag. -/
theorem british_flag_unit_center
    (p : Plane2)
    (hp : p = EuclideanSpace.single (0 : Fin 2) (1 / 2 : ℝ)
              + EuclideanSpace.single (1 : Fin 2) (1 / 2 : ℝ)) :
    dist p unitA ^ 2 + dist p unitC ^ 2
      = dist p unitB ^ 2 + dist p unitD ^ 2 := by
  subst hp
  simp only [dist_sq_fin_two, unitA, unitB, unitC, unitD,
    EuclideanSpace.single_apply]
  norm_num

/-
Level B namesake OUT of this ticket (do not sorry):

theorem british_flag (a b : ℝ) (p : Plane2) :
    dist p ![(0:ℝ), 0] ^ 2 + dist p ![a, b] ^ 2
      = dist p ![a, 0] ^ 2 + dist p ![0, b] ^ 2

Residual of this id (comment only, not sorry):
Napoleon equilateral-on-sides / Simson line / Viviani /
nine-point circle / angle-bisector theorem. Do not expand this
ticket. Do not prove parallelogram_law as namesake / Ptolemy /
law of cosines as namesake / Euler line / Heron / Wantzel /
fine-wilf / Lyndon–Schützenberger / Kraft / McMillan / Huffman /
Shannon / List.rotate as namesake / sherman-morrison / Woodbury /
graham-pollak / biclique cover / Zarankiewicz.
-/

end

end ProofLab.BritishFlag
