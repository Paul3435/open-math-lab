# Euler brick 44,117,240 face diagonals (formalize-only)

**id:** `euler-brick`
**ticket:** OPE-1390 Scout leftover slot #2 (parent OPE-1389;
post zsqrt5-not-ufd #165 + d8-ne-q8 #166)
**expected:** known-classical (Halcke 1719 / Euler: a
rectangular box with integer edges whose *face* diagonals
are also integer; (44,117,240) is the smallest primitive
example) —
**no novelty claim**

## Why not classical / why formalize-only

Settled elementary Diophantine arithmetic: the edges
`44, 117, 240` satisfy

- `44² + 117² = 125²`
- `44² + 240² = 244²`
- `117² + 240² = 267²`

so all three face diagonals are integer. Completely
classical. The namesake “infinitely many primitive Euler
bricks / a parametric family” and the **open** perfect-cuboid
question (space diagonal also integer) are **different**,
larger residuals — do **not** sorry them.

Not an open problem. Not a novelty claim. Not live cash.
(The *perfect* cuboid is open; that is residual of *this*
id, not this Level A.)

**Not** `PythagoreanTriple.classification`
(PythagoreanTriples.lean L649 already-in — **different**
parametrization of a *single* triple; USE `x*x+y*y=z*z` /
`pow_two`, do **not** re-prove classification, do **not**
cite as an Euler brick). **Not** Alcuin integer triangles
(consumed #153; counting triangles by perimeter ≠ three
compatible face triples). **Not** Heron (consumed; triangle
area ≠ box face diagonals). **Not** British-flag (consumed
#145; planar unit-square distances ≠ 3D integer box).
**Not** cannonball (consumed #154; pyramidal squares ≠
box). **Not** Pick / Ceva / Morley / Desargues / Pascal /
Feuerbach (geometry leftover cluster of Heron / #145 /
Alcuin; do **not** revive). **Not** Euclid–Euler even
perfect (`euclid-euler-perfect`, consumed). **Not** Euler
odd=distinct partitions (`euler-odd-distinct`, consumed).
**Not** Eulerian trails (`eulerian-hierholzer`, consumed).
Do **not** label theorems `eulerian_*` / `euclid_euler_*` /
`partition_*`. **Not** taxicab-1729 (prime of this
shortlist; cubes ≠ squares). **Not** zsqrt5-not-ufd /
d8-ne-q8 (consumed #165+#166).

Mathlib v4.10.0 already has the **square / triple infra
this theorem needs**:

- `Nat` / `HPow` / `^`
- `pow_two` (Algebra/Group/Defs.lean L581)
- `PythagoreanTriple` (PythagoreanTriples.lean L44) —
  glue **not** namesake
- `PythagoreanTriple.classification` L649 — **different**
  already-in theorem; **not** namesake

There is **no** named `eulerBrick` / `EulerBrick` /
`perfectCuboid` / `integerCuboid` / face-diagonal box
theorem anywhere under `Mathlib/` or `Archive/` or
`ProofLab/` (this run → ZERO on those names; a single
Pythagorean triple is a different theorem). Do **not**
import `Archive.*`.

OPE-1374 shortlist is **CONSUMED** (#165+#166). This is a
**fresh** catalog-audit leftover id, **not** an Alcuin
leftover continuation, **not** a Heron leftover, **not** a
British-flag leftover, **not** a Pythagorean-classification
leftover, **not** a prize leftover, **not** a Formalist
Level B revival, **not** a third slot.

Mill NOW: finite three-face Pythagorean witnesses leftover
beside two-cube 1729. `pow_two` is waiting the same way
`pow_three` waits for the prime. **Not a rubber-stamp of
`PythagoreanTriple.classification`.** **Not a rubber-stamp
of Alcuin.**

Do **not** describe an attack as discovering Euler bricks.
Do **not** expand into infinitely many bricks or a perfect
cuboid as a sorry (perfect cuboid is **open**; infinitely
many is leftover-risk of *this* id — do **not** sorry
either). Do **not** label theorems `alcuin_*` / `heron_*` /
`pythagorean_classification_*` / `eulerian_*` as the
namesake.

## Pinned convention (exact)

**v1 Level A is named small-edge witnesses: `44²+117²=125²`,
`44²+240²=244²`, `117²+240²=267²`, not labelled Euler /
Halcke / cuboid.**

Suggested pin:

```text
-- Level A (not labelled Euler / Halcke / cuboid):
-- named face-diagonal witnesses.

theorem brick_ab :
    (44 : ℕ) ^ 2 + 117 ^ 2 = 125 ^ 2

theorem brick_ac :
    (44 : ℕ) ^ 2 + 240 ^ 2 = 244 ^ 2

theorem brick_bc :
    (117 : ℕ) ^ 2 + 240 ^ 2 = 267 ^ 2

-- optional extra: space diagonal 44²+117²+240² is not a square
-- (so this example is not a perfect cuboid)

-- Level B namesake (a primitive Euler brick exists / infinitely
-- many; residual OK). Perfect cuboid is OPEN — do not sorry it.
theorem euler_brick :
    ∃ a b c da db dc : ℕ,
      0 < a ∧ 0 < b ∧ 0 < c ∧
      a ^ 2 + b ^ 2 = da ^ 2 ∧
      a ^ 2 + c ^ 2 = db ^ 2 ∧
      b ^ 2 + c ^ 2 = dc ^ 2
    -- do not sorry the namesake; Level A already supplies the witness
```

Named three-face witnesses are load-bearing. All three
face diagonals integer on the *same* edge triple, so the
theorem is **not** “some Pythagorean triples exist.”

**Level A may land only** the three equalities (optional
extra: space diagonal not square), **not** labelled Euler /
Halcke / cuboid. Reuse Mathlib `Nat` / `^ 2` —
**do not re-prove** `PythagoreanTriple.classification` /
Alcuin / Heron.

**Level B** is the namesake existence/infinitude. Do not
sorry the namesake; honest partial is allowed (comment
residual, not `sorry`). Perfect cuboid is **open** residual
**out of v1**.

## Landmines

1. **Do not re-prove** `Nat` / `pow_two` /
   `PythagoreanTriple`. Already Mathlib. Use them if needed.
2. **This is not** `PythagoreanTriple.classification`
   (PythagoreanTriples.lean L649 already-in). Different
   theorem (one triple, not three faces). USE `^ 2`.
3. **This is not** Alcuin / Heron / British-flag / cannonball
   / Pick / Ceva / Morley (consumed or geometry leftover
   cluster). Do not revive.
4. **This is not** a perfect cuboid. That is **open**.
   Residual of this id. Do not sorry it.
5. **This is not** Euclid–Euler perfect / Euler odd=distinct
   / Eulerian trails (consumed Euler *namesakes*). Do not
   label theorems `eulerian_*` / `euclid_euler_*`.
6. **This is not** taxicab-1729 (prime of this shortlist).
   Do not prove 1729 here.
7. **This is not** zsqrt5-not-ufd / d8-ne-q8 (consumed
   #165+#166).
8. **Do not** re-prime the consumed mill list.
9. **Leave OPE-403 alone.** Leave OPE-1195 leftover status
   alone.
10. **Do not import `Archive.*`.**
11. Default no claim. No novelty claim.

## Out of v1

- Namesake infinitude / parametric family of Euler bricks
- Perfect cuboid (space diagonal also integer) — **open**
- Other famous bricks (240, 44, 117 scaled; 85,132,720; …)
- Prize claims / Millennium / Beal
