/-
Named face-diagonal witnesses — Level A only
(`44² + 117² = 125²` / `44² + 240² = 244²` / `117² + 240² = 267²`).
**Not labelled Euler / Halcke / cuboid.**

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 pin `a719ba5c3115` has `Nat` / `HPow` / `^` /
`pow_two` / `PythagoreanTriple` as **infra**. ZERO named
`eulerBrick` / `EulerBrick` / `perfectCuboid` / `integerCuboid` /
`euler.?brick` theorem under `Mathlib/` or `Archive/` or
`ProofLab/` (this run; Haar `OfBasis.lean` “cuboid” is a
parallelepiped measure — unrelated). Completing the Level A
named three-face witnesses is the gap this ticket lands. The
Level B namesake `euler_brick` (a primitive Euler brick exists /
infinitely many) is **out of this ticket** and is **not**
sorry-ed. Perfect cuboid (space diagonal also integer) is
**OPEN** residual of this id — **out of v1**, not sorry-ed.
Other famous bricks (scaled 44,117,240; 85,132,720; …) are
residual. Do **not** label theorems `euler_brick` / `eulerian_*`
/ `euclid_euler_*` / `pythagorean_classification_*` / `alcuin_*`
/ `heron_*` as the namesake. Do **not** define the namesake via
a perfect cuboid.

Pin: `catalog/problems/euler-brick/STATEMENT.md`
(OPE-1400; Scout OPE-1390 leftover slot #2; Director OPE-1399).
Encoding: named face-diagonal witnesses via Mathlib `Nat` / `^ 2`.
Zero `sorry`. Do not import `Archive.*`.

This is **not** `Nat` / `HPow` / `^` / `pow_two`
(`Algebra/Group/Defs.lean` L581) — already Mathlib.
**USE, do not re-prove; do not cite as this three-face box.**
This is **not** `PythagoreanTriple`
(`NumberTheory/PythagoreanTriples.lean` L44) — glue **not**
namesake. USE; do **not** re-prove.
This is **not** `PythagoreanTriple.classification`
(`PythagoreanTriples.lean` L649) — DIFFERENT already-in
single-triple parametrization. USE `^ 2`; do **not** re-prove;
do **not** cite as this three-face box.
This is **not** Alcuin integer triangles
(`ProofLab/AlcuinIntegerTriangles.lean`, consumed #153).
Perimeter counts ≠ face diagonals.
This is **not** Heron (`ProofLab/Heron.lean`, consumed).
Triangle area ≠ box.
This is **not** British-flag (`ProofLab/BritishFlag.lean`,
consumed #145). Planar unit-square distances ≠ 3D integer box.
This is **not** cannonball
(`ProofLab/CannonballSquarePyramid.lean`, consumed #154).
This is **not** Euclid–Euler perfect / Euler odd=distinct /
Eulerian trails (`ProofLab/EuclidEulerPerfect.lean` /
`EulerPartition.lean` / `Eulerian.lean`) — different consumed
Euler namesakes. Do **not** label theorems `eulerian_*` /
`euclid_euler_*`.
This is **not** taxicab-1729 (`ProofLab/Taxicab1729.lean`,
consumed #168). Cubes ≠ squares.
This is **not** D8 ≇ Q8 (`ProofLab/D8NeQ8.lean`, consumed #166).
This is **not** ℤ[√-5] not UFD (`ProofLab/Zsqrt5NotUfd.lean`,
consumed #165).
Do not re-prime the consumed mill. Leave OPE-403 alone.
Leave OPE-1195 alone.

v1 is named three-face witnesses: `44²+117²=125²`,
`44²+240²=244²`, `117²+240²=267²` on the *same* edge triple
`44,117,240`, **not labelled Euler / Halcke / cuboid**. Named
three-face witnesses are load-bearing (so Level A is **not**
“some Pythagorean triples exist”).

Level A: `brick_ab` / `brick_ac` / `brick_bc`.
Optional extra: space diagonal `44²+117²+240²` is not a square.
**Not** labelled Euler / Halcke / cuboid.

Transcribed classical argument (Halcke 1719 / Euler brick
(44,117,240) face diagonals 125,244,267). Compact form:
Wikipedia *Euler brick*. Type pin: `Nat` / `^ 2`.
`PythagoreanTriple.classification` is a different already-in
single-triple formula. Alcuin / Heron / British-flag /
cannonball / taxicab-1729 are different consumed mills.
No novelty claim. Default no claim.

Level B namesake OUT of this ticket (do not sorry):
-- theorem euler_brick :
--     ∃ a b c da db dc : ℕ,
--       0 < a ∧ 0 < b ∧ 0 < c ∧
--       a ^ 2 + b ^ 2 = da ^ 2 ∧
--       a ^ 2 + c ^ 2 = db ^ 2 ∧
--       b ^ 2 + c ^ 2 = dc ^ 2
-- Perfect cuboid OPEN — do not sorry it.
-/
import Mathlib.Tactic

namespace ProofLab.EulerBrick

/-! ## Level A: 44²+117²=125² / 44²+240²=244² / 117²+240²=267²
(not labelled Euler / Halcke / cuboid) -/

/-- `44² + 117² = 125²`. Glue: Mathlib `Nat` / `^ 2`.
Not labelled Euler / Halcke / cuboid.
Load-bearing named face on the same edge triple. -/
theorem brick_ab : (44 : ℕ) ^ 2 + 117 ^ 2 = 125 ^ 2 := by
  rfl

/-- `44² + 240² = 244²`. Glue: Mathlib `Nat` / `^ 2`.
Not labelled Euler / Halcke / cuboid.
Load-bearing named face on the same edge triple. -/
theorem brick_ac : (44 : ℕ) ^ 2 + 240 ^ 2 = 244 ^ 2 := by
  rfl

/-- `117² + 240² = 267²`. Glue: Mathlib `Nat` / `^ 2`.
Not labelled Euler / Halcke / cuboid.
Load-bearing named face on the same edge triple. -/
theorem brick_bc : (117 : ℕ) ^ 2 + 240 ^ 2 = 267 ^ 2 := by
  rfl

/-- Optional extra: `44² + 117² + 240²` is not a square.
Glue; **not** labelled Euler / Halcke / cuboid.
Does **not** sorry a perfect cuboid (OPEN residual, out of v1). -/
theorem space_diag_not_square {n : ℕ} :
    n ^ 2 ≠ (44 : ℕ) ^ 2 + 117 ^ 2 + 240 ^ 2 := by
  intro h
  have hs : (44 : ℕ) ^ 2 + 117 ^ 2 + 240 ^ 2 = 73225 := by rfl
  have h270 : (270 : ℕ) ^ 2 = 72900 := by rfl
  have h271 : (271 : ℕ) ^ 2 = 73441 := by rfl
  rw [hs] at h
  by_cases hn : n ≤ 270
  · have hle : n ^ 2 ≤ 270 ^ 2 := Nat.pow_le_pow_of_le_left hn 2
    rw [h, h270] at hle
    exact (by decide : ¬ 73225 ≤ 72900) hle
  · have hge : 271 ≤ n := Nat.succ_le_of_lt (lt_of_not_ge hn)
    have hge' : 271 ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_of_le_left hge 2
    rw [h271, h] at hge'
    exact (by decide : ¬ 73441 ≤ 73225) hge'

/-
Residual (Level B, **out of this ticket**, not sorry-ed):
`euler_brick` — exists a primitive Euler brick / infinitely
many. Do **not** sorry the namesake.
Perfect cuboid (space diagonal also integer) is **OPEN**
residual of this id, **out of v1**; do **not** sorry it.
Other famous bricks / scaled copies remain residual of this
id; do **not** expand them as extra namesakes.
Do **not** prove `PythagoreanTriple.classification` as namesake
/ Alcuin leftover-revivals / Heron leftover-revivals /
British-flag leftover-revivals / cannonball leftover-revivals /
Pick / Ceva / Morley / Euclid–Euler perfect / Euler
odd=distinct / Eulerian trails / taxicab-1729 /
`1³+12³=1729` / `fermatLastTheoremThree` as namesake /
`Nat.Prime.sq_add_sq` as namesake / `Nat.sum_four_squares` as
namesake / zsqrt5-not-ufd / UniqueFactorizationMonoid
leftover-revivals / d8-ne-q8 / order-8 classification.
Leave OPE-403 alone. Leave OPE-1195 alone.
Do **not** label theorems `euler_brick` / `eulerian_*` /
`euclid_euler_*` / `pythagorean_classification_*` / `alcuin_*`
/ `heron_*`.
-/

end ProofLab.EulerBrick
