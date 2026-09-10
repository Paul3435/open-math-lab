/-
Integer-sided triangles of named small perimeters — Level A only
(perimeter `1` none / `3 = (1,1,1)` / `5 = (1,2,2)` / `6 = (2,2,2)`).
**Not labelled Alcuin.**

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 pin `a719ba5c3115` has `Nat` / `Finset.filter` /
`Finset.card` as **infra**. ZERO named Alcuin triangle-count /
`alcuin` / `Alcuin` / `integerTriangle` / `IntegerTriangle` /
`triangleCount` under `Mathlib/` or `Archive/` or `ProofLab/`.
Completing the Level A named-perimeter witnesses is the gap this
ticket lands. The Level B namesake `alcuin_integer_triangles`
(closed-form count `round(n²/48)` for every `n`) is **out of this
ticket** and is **not** sorry-ed. Heronian area / Pick /
Brahmagupta are residual of this id.

Pin: `catalog/problems/alcuin-integer-triangles/STATEMENT.md`
(OPE-1316; Scout OPE-1310 RECOMMENDED PRIME; Director OPE-1315).
Encoding: `IsIntegerTriangle` via Mathlib `Nat` order / addition.
Zero `sorry`. Do not import `Archive.*`.

This is **not** `Nat` arithmetic / `Finset.filter` / `Finset.card`
— already Mathlib. **USE, do not re-prove; do not cite as Alcuin.**
This is **not** `PythagoreanTriple.classification`
(`NumberTheory/PythagoreanTriples.lean` L649) — DIFFERENT
right-triangle theorem. Do **not** re-prove; do **not** cite as
Alcuin.
This is **not** Ruzsa triangle inequality
(`Combinatorics/Additive/PluenneckeRuzsa.lean`) — DIFFERENT
additive combinatorics. Do **not** cite as Alcuin.
This is **not** Lucas theorem (`Choose/Lucas.lean` L97) —
DIFFERENT binomial congruence. Never cite as a gap.
This is **not** Heron (`ProofLab/Heron.lean`, consumed) / Pick /
Brahmagupta / Heronian area. Side-count ≠ area.
This is **not** British flag (`ProofLab/BritishFlag.lean`,
consumed #145) / Napoleon / Simson / Viviani / nine-point.
Euclidean `dist` ≠ Nat sides.
This is **not** platonic-solids (`ProofLab/PlatonicSolids.lean`,
PR #147) / Euler polyhedron / Coxeter `H₃`.
This is **not** egyptian-fractions
(`ProofLab/EgyptianFractions.lean`, PR #148) / Erdős–Straus.
This is **not** Frucht graph Aut (`ProofLab/FruchtGraphAut.lean`,
consumed #150) / Cayley-graph / GRR / `Aut(Kₙ)≅Sₙ`.
This is **not** Proth primality (`ProofLab/ProthPrimality.lean`,
consumed #151) / Pépin / Pocklington / `euler_criterion`.
This is **not** cannonball-square-pyramid (OPE-1310 leftover;
unassigned this tick). Do **not** prove cannonball / Faulhaber /
`sum_range_pow` as namesake here.
Do not re-prime the consumed mill. Leave OPE-403 alone.
Leave OPE-1195 alone.

v1 is the integer-triangle predicate on named small perimeters:
perimeter `1` has none, perimeter `3` is exactly `(1,1,1)`,
perimeter `5` is exactly `(1,2,2)`, and perimeter `6` is exactly
`(2,2,2)`, **not labelled Alcuin**. Positive sides, `a ≤ b ≤ c`,
`a+b+c = n`, and strict `a+b > c` are load-bearing (so `(1,1,2)`
of perimeter `4` is excluded).

Level A: `1` / `3` / `5` / `6`. Optional extra: perimeter `7` is
exactly `{(1,3,3),(2,2,3)}`. **Not** labelled Alcuin.

Transcribed classical argument (Alcuin of York, *Propositiones ad
acuendos juvenes*; OEIS A005044). Compact form: Wikipedia
*Integer triangle* (number of triangles with given perimeter).
Type pin: `IsIntegerTriangle a b c n` / `a ≤ b ≤ c` / `a+b > c`.
`PythagoreanTriple.classification` is a different already-in
right-triangle theorem. Heron is a different consumed area
formula. No novelty claim. Default no claim.
-/
import Mathlib.Tactic

set_option linter.unusedVariables false

namespace ProofLab.AlcuinIntegerTriangles

/-! ## Level A: perimeters 1 / 3 / 5 / 6
(not labelled Alcuin) -/

/-- Positive integer sides `a ≤ b ≤ c` of perimeter `n` with strict
triangle inequality. Encoding; **not** labelled Alcuin. Does **not**
re-prove `Nat` order / addition / `PythagoreanTriple.classification`. -/
def IsIntegerTriangle (a b c n : ℕ) : Prop :=
  0 < a ∧ a ≤ b ∧ b ≤ c ∧ a + b + c = n ∧ a + b > c

/-- Perimeter `1` has no positive `a ≤ b ≤ c` summing to `1`.
Glue; **not** labelled Alcuin. -/
theorem alcuin_one (a b c : ℕ) : ¬ IsIntegerTriangle a b c 1 := by
  unfold IsIntegerTriangle
  omega

/-- Perimeter `3` is exactly `(1,1,1)`. Glue; **not** labelled Alcuin. -/
theorem alcuin_three :
    IsIntegerTriangle 1 1 1 3 ∧
      ∀ a b c, IsIntegerTriangle a b c 3 → a = 1 ∧ b = 1 ∧ c = 1 := by
  constructor
  · unfold IsIntegerTriangle; omega
  · intro a b c h
    unfold IsIntegerTriangle at h
    omega

/-- Perimeter `5` is exactly `(1,2,2)`. Glue; **not** labelled Alcuin.
`(1,1,3)` fails strict `a+b > c`. -/
theorem alcuin_five :
    IsIntegerTriangle 1 2 2 5 ∧
      ∀ a b c, IsIntegerTriangle a b c 5 → a = 1 ∧ b = 2 ∧ c = 2 := by
  constructor
  · unfold IsIntegerTriangle; omega
  · intro a b c h
    unfold IsIntegerTriangle at h
    omega

/-- Perimeter `6` is exactly `(2,2,2)`. Glue; **not** labelled Alcuin.
`(1,2,3)` fails strict `a+b > c` (equality is excluded). -/
theorem alcuin_six :
    IsIntegerTriangle 2 2 2 6 ∧
      ∀ a b c, IsIntegerTriangle a b c 6 → a = 2 ∧ b = 2 ∧ c = 2 := by
  constructor
  · unfold IsIntegerTriangle; omega
  · intro a b c h
    unfold IsIntegerTriangle at h
    omega

/-- Optional extra: perimeter `7` is exactly `{(1,3,3),(2,2,3)}`.
Glue; **not** labelled Alcuin. -/
theorem alcuin_seven :
    IsIntegerTriangle 1 3 3 7 ∧
      IsIntegerTriangle 2 2 3 7 ∧
        ∀ a b c, IsIntegerTriangle a b c 7 →
          a = 1 ∧ b = 3 ∧ c = 3 ∨ a = 2 ∧ b = 2 ∧ c = 3 := by
  refine ⟨?w133, ?w223, ?uniq⟩
  · unfold IsIntegerTriangle; omega
  · unfold IsIntegerTriangle; omega
  · intro a b c h
    unfold IsIntegerTriangle at h
    omega

/-
Residual (Level B, **out of this ticket**, not sorry-ed):
`alcuin_integer_triangles` — the number of non-congruent positive
integer-sided triangles of perimeter `n` equals `round(n²/48)`
(OEIS A005044; even/odd convention). Do **not** sorry the closed
form. Heronian area / Pick / Brahmagupta remain residual of this
id; do **not** expand them as extra namesakes.
Do **not** prove cannonball-square-pyramid / Faulhaber /
`sum_range_pow` as namesake / PythagoreanTriple.classification as
namesake / Heron / Pick / Brahmagupta / Ruzsa triangle inequality
as namesake / frucht-graph-aut / Cayley-graph / GRR /
`Aut(Kₙ)≅Sₙ` / proth-primality / Pépin / Pocklington /
`euler_criterion` as namesake / platonic-solids / egyptian-fractions.
Leave OPE-403 alone. Leave OPE-1195 alone.
-/

end ProofLab.AlcuinIntegerTriangles
