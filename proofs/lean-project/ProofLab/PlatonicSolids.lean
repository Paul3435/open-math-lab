/-
Platonic solids — Level A only (tetra / cube / octa / icosa /
dodeca (V,E,F) witnesses + (3,6)/(4,4) fail). **Not labelled
Platonic / Schläfli namesake / Euler polyhedron.**

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 pin `a719ba5c3115` has Nat arithmetic /
`CoxeterMatrix.H₃` as **infra**. ZERO named Platonic-solids
count / `platonic` / `PlatonicSolid` / `schlafli` /
`Schlafli` / `regularPolyhedron` under `Mathlib/` or
`Archive/` or `ProofLab/`. Completing the Level A five named
combinatorial types as `(p,q,V,E,F)` witnesses with
handshaking `2E = pF = qV` and Euler `V − E + F = 2`, plus
two failing Schläfli pairs `(3,6)` and `(4,4)`, is the gap
this ticket lands. The Level B namesake `platonic_schlafli`
(the only `p,q ≥ 3` with `(p-2)(q-2) < 4` are the five
Schläfli pairs) is **out of this ticket** and is **not**
sorry-ed. Euler polyhedron formula (Wiedijk #13) / Coxeter
classification / Kepler–Poinsot / regular 4-polytopes are
residual of this id.

Pin: `catalog/problems/platonic-solids/STATEMENT.md`
(OPE-1284; Scout OPE-1278 RECOMMENDED PRIME; Director
OPE-1283). Encoding: combinatorial `RegularMap` with
integer `p,q ≥ 3`, handshaking, and Euler characteristic
as `ℤ`. Zero `sorry`. Do not import `Archive.*`.

This is **not** Nat subtraction / multiplication / `lt` —
already Mathlib / prelude. **USE, do not re-prove; do not
cite as Platonic.**
This is **not** `CoxeterMatrix.H₃` (`Coxeter/Matrix.lean`
L250) — DIFFERENT dodecahedral/icosahedral reflection-matrix
glue. **USE only as optional extra glue; do not re-prove;
do not cite as the count of solids.**
This is **not** `CategoryTheory.Triangulated.Octahedron` /
`octahedron_axiom` (`Triangulated.lean` L36 / L165) —
DIFFERENT octahedron axiom. **Do not cite as Platonic;
do not re-prove.**
This is **not** Euler's polyhedron formula (Wiedijk #13) —
DIFFERENT planar-graph theorem; residual of this id.
Level A may check `V−E+F=2` on named `(V,E,F)` witnesses;
**do not sorry a planar Euler theorem.**
This is **not** Fine–Wilf (`ProofLab/FineWilf.lean`, PR #144)
/ Lyndon–Schützenberger.
This is **not** British flag (`ProofLab/BritishFlag.lean`,
PR #145) / Napoleon / Simson / Viviani / nine-point.
This is **not** Wantzel (`ProofLab/WantzelConstructible.lean`,
PR #133) / friendship / Moore cages.
This is **not** `egyptian-fractions` (OPE-1278 leftover,
unassigned this tick). Do **not** prove Egyptian fractions
/ Farey as namesake / Stern–Brocot / Calkin–Wilf / Kraft /
McMillan / Huffman / Shannon / Erdős–Straus here.
Do not re-prime the consumed mill. Leave OPE-403 alone.
Leave OPE-1195 alone.

v1 is the five named combinatorial types as `(p,q,V,E,F)`
witnesses satisfying handshaking `2E = pF = qV` and Euler
`V − E + F = 2`, plus two failing Schläfli pairs `(3,6)`
and `(4,4)`, **not labelled Platonic**. Integer `p,q ≥ 3`
is load-bearing. Handshaking is load-bearing. Euler `= 2`
on those witnesses is load-bearing.

Level A: tetra `{3,3}` `(4,6,4)`, cube `{4,3}` `(8,12,6)`,
octa `{3,4}` `(6,12,8)`, icosa `{3,5}` `(12,30,20)`,
dodeca `{5,3}` `(20,30,12)` each satisfy handshaking and
Euler 2. `(3,6)` gives `(p-2)(q-2)=4` not `< 4`; `(4,4)`
likewise. Optional extra: one named solid satisfies
`(p-2)(q-2)<4`. **Not** labelled Platonic.

Transcribed classical argument (Euclid XIII; Wiedijk 100
#50 *The Number of Platonic Solids*, no Mathlib `decl`
this pin). Compact form: Wikipedia *Platonic solid*,
Schläfli symbol `{p,q}`. Type pin: `RegularMap` `p q V E F`
/ `2E=pF=qV` / `V−E+F=2`. Coxeter `H₃` is a different
reflection-matrix glue. Triangulated Octahedron is a
different axiom. No novelty claim. Default no claim.
-/
import Mathlib.Tactic

set_option linter.unusedVariables false

namespace ProofLab.PlatonicSolids

/-- Combinatorial regular map: `p`-gonal faces, `q` faces
per vertex, handshaking `2E = pF = qV`, and integer
`p,q ≥ 3`. Encoding; **not** labelled Platonic. Uses
Mathlib / prelude Nat arithmetic; does **not** re-prove
Nat lemmas, Coxeter `H₃`, or the triangulated octahedron
axiom. -/
structure RegularMap where
  p : ℕ
  q : ℕ
  V : ℕ
  E : ℕ
  F : ℕ
  hp : 3 ≤ p
  hq : 3 ≤ q
  hFace : 2 * E = p * F
  hVert : 2 * E = q * V

/-- Euler characteristic `V − E + F` as `ℤ`. Glue; **not**
labelled Platonic / Euler polyhedron formula. This is **not**
a planar-graph Euler theorem (Wiedijk #13 residual). -/
def euler (m : RegularMap) : ℤ :=
  (m.V : ℤ) - m.E + m.F

/-! ## Level A: tetra / cube / octa / icosa / dodeca
witnesses and (3,6)/(4,4) failures (not labelled Platonic) -/

/-- Tetrahedron `{3,3}` with `(V,E,F) = (4,6,4)`. Encoding;
**not** labelled Platonic. -/
def tetra : RegularMap where
  p := 3
  q := 3
  V := 4
  E := 6
  F := 4
  hp := by decide
  hq := by decide
  hFace := by decide
  hVert := by decide

/-- Cube `{4,3}` with `(V,E,F) = (8,12,6)`. Encoding;
**not** labelled Platonic. -/
def cube : RegularMap where
  p := 4
  q := 3
  V := 8
  E := 12
  F := 6
  hp := by decide
  hq := by decide
  hFace := by decide
  hVert := by decide

/-- Octahedron `{3,4}` with `(V,E,F) = (6,12,8)`. Encoding;
**not** labelled Platonic. This is **not** the triangulated
octahedron axiom. -/
def octa : RegularMap where
  p := 3
  q := 4
  V := 6
  E := 12
  F := 8
  hp := by decide
  hq := by decide
  hFace := by decide
  hVert := by decide

/-- Icosahedron `{3,5}` with `(V,E,F) = (12,30,20)`. Encoding;
**not** labelled Platonic. -/
def icosa : RegularMap where
  p := 3
  q := 5
  V := 12
  E := 30
  F := 20
  hp := by decide
  hq := by decide
  hFace := by decide
  hVert := by decide

/-- Dodecahedron `{5,3}` with `(V,E,F) = (20,30,12)`. Encoding;
**not** labelled Platonic. This is **not** Coxeter `H₃` as
namesake. -/
def dodeca : RegularMap where
  p := 5
  q := 3
  V := 20
  E := 30
  F := 12
  hp := by decide
  hq := by decide
  hFace := by decide
  hVert := by decide

/-- Tetrahedron witness has Euler characteristic 2. Glue;
**not** labelled Platonic / Euler polyhedron. -/
theorem euler_tetra : euler tetra = 2 := by decide

/-- Cube witness has Euler characteristic 2. Glue;
**not** labelled Platonic / Euler polyhedron. -/
theorem euler_cube : euler cube = 2 := by decide

/-- Octahedron witness has Euler characteristic 2. Glue;
**not** labelled Platonic / Euler polyhedron. -/
theorem euler_octa : euler octa = 2 := by decide

/-- Icosahedron witness has Euler characteristic 2. Glue;
**not** labelled Platonic / Euler polyhedron. -/
theorem euler_icosa : euler icosa = 2 := by decide

/-- Dodecahedron witness has Euler characteristic 2. Glue;
**not** labelled Platonic / Euler polyhedron. -/
theorem euler_dodeca : euler dodeca = 2 := by decide

/-- Schläfli pair `(3,6)` fails `(p-2)(q-2) < 4`
(`1 * 4 = 4`). Glue; **not** labelled Platonic. -/
theorem schlafli_fail_three_six : ¬ (3 - 2) * (6 - 2) < 4 := by decide

/-- Schläfli pair `(4,4)` fails `(p-2)(q-2) < 4`
(`2 * 2 = 4`). Glue; **not** labelled Platonic. -/
theorem schlafli_fail_four_four : ¬ (4 - 2) * (4 - 2) < 4 := by decide

/-- Optional extra: tetrahedron satisfies `(p-2)(q-2) < 4`.
Glue; **not** labelled Platonic. This is **not** the Level B
only-five-pairs namesake. -/
theorem schlafli_bound_tetra : (tetra.p - 2) * (tetra.q - 2) < 4 := by
  decide

/-
Level B namesake OUT of this ticket (do not sorry):

theorem platonic_schlafli {p q : ℕ} (hp : 3 ≤ p) (hq : 3 ≤ q) :
    (p - 2) * (q - 2) < 4 ↔
      (p, q) = (3, 3) ∨ (p, q) = (3, 4) ∨ (p, q) = (3, 5) ∨
      (p, q) = (4, 3) ∨ (p, q) = (5, 3)

Residual of this id (comment only, not sorry):
Euler polyhedron formula for planar graphs (Wiedijk #13) /
Coxeter classification / Kepler–Poinsot star polyhedra /
regular 4-polytopes / geometric realization in ℝ³.
Do not expand this ticket. Do not prove CoxeterMatrix.H₃
as namesake / triangulated octahedron axiom as namesake /
egyptian-fractions / Farey as namesake / Stern–Brocot /
Calkin–Wilf / Kraft / McMillan / Huffman / Shannon /
Erdős–Straus / british-flag / Napoleon / Simson / Viviani /
nine-point / fine-wilf / Lyndon–Schützenberger.
-/

end ProofLab.PlatonicSolids
