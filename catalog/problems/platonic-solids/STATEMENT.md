# Number of Platonic solids — formalize-only

**id:** `platonic-solids`
**ticket:** OPE-1278 Scout RECOMMENDED PRIME (parent OPE-1277;
post fine-wilf #144 + british-flag #145)
**expected:** known-classical (Euclid XIII / Wiedijk 100 #50:
exactly five combinatorial regular polyhedra, Schläfli
`{p,q}` with `p,q ≥ 3` and `(p-2)(q-2) < 4`) —
**no novelty claim**

## Why not classical / why formalize-only

Settled discrete geometry: a combinatorial regular
map with `p`-gonal faces, `q` faces per vertex,
handshaking `2E = pF = qV`, and Euler
`V − E + F = 2` forces `1/p + 1/q > 1/2`, i.e.
`(p-2)(q-2) < 4`. The only integer solutions
`p,q ≥ 3` are the five Schläfli symbols
`{3,3}` tetrahedron, `{3,4}` octahedron,
`{3,5}` icosahedron, `{4,3}` cube,
`{5,3}` dodecahedron. Completely classical
(Euclid book XIII; Wiedijk 100 #50 has **no**
Mathlib `decl` this pin).

Not an open problem. Not a novelty claim.

**Not** the triangulated-category octahedron axiom
(`CategoryTheory.Triangulated.Octahedron` /
`octahedron_axiom` — **different octahedron**;
do **not** cite as Platonic). **Not** Coxeter
`H₃` / `H₄` as namesake (Coxeter/Matrix.lean L250
is the dodecahedral/icosahedral reflection
matrix — **USE as optional glue**, do **not**
re-prove, do **not** cite as the count of
solids). **Not** Euler's polyhedron formula as
namesake (Wiedijk #13 residual of *this* id;
Level A may check `V−E+F=2` on named
`(V,E,F)` witnesses; do **not** sorry a
planar-graph Euler theorem). **Not** British
flag / Napoleon / Simson / Viviani / nine-point
(consumed #145 leftover-risk). **Not**
friendship / Moore cages. **Not** Wantzel.
**Not** Egyptian fractions (leftover of this
shortlist).

Mathlib v4.10.0 already has the **Nat / Coxeter
infra this theorem needs**:

- `Nat` subtraction / multiplication / `lt`
- `CoxeterMatrix.H₃` (Coxeter/Matrix.lean L250)
  — **not** namesake
- Turán `isTuranMaximal_iff_nonempty_iso_turanGraph`
  (Turan.lean L300) as negative-control already-in

There is **no** named Platonic-solids count,
**no** `platonic` / `PlatonicSolid` /
`schlafli` / `regularPolyhedron` theorem
anywhere under `Mathlib/` or `Archive/` or
`ProofLab/` (this run → ZERO on those names;
Coxeter `H₃` comment + triangulated
`Octahedron` only). Do **not** import
`Archive.*`.

OPE-1263 shortlist is **CONSUMED**
(#144 fine-wilf Level A + #145 british-flag
Level A). This is a **fresh** catalog-audit
id, **not** a Fine–Wilf leftover continuation,
**not** a British-flag leftover, **not** a
Napoleon revival, **not** a prize leftover,
**not** a Formalist Level B revival, **not**
a third slot.

Mill NOW: finite Schläfli arithmetic after
Fine–Wilf (word periods) + British flag
(rectangle distances). `Nat` + Euler
handshaking are waiting the same way
`List.get` waited for Fine–Wilf.
**Not a rubber-stamp of Coxeter H₃.**
**Not a rubber-stamp of the triangulated
octahedron axiom.**

Do **not** describe an attack as discovering
the five Platonic solids. Do **not** expand
into Euler polyhedron / Coxeter classification
/ Kepler–Poinsot / regular 4-polytopes as
extra namesakes (Euler #13 is leftover-risk
of *this* id).

## Pinned convention (exact)

**v1 Level A is the five named combinatorial
types as `(p,q,V,E,F)` witnesses satisfying
handshaking `2E = pF = qV` and Euler
`V − E + F = 2`, plus two failing Schläfli
pairs `(3,6)` and `(4,4)`, not labelled
Platonic.** Integer `p,q ≥ 3` is
load-bearing. Handshaking is load-bearing.

Suggested pin:

```text
-- Level A (not labelled Platonic):
-- tetra / cube / octa / icosa / dodeca witnesses;
-- (3,6) and (4,4) fail (p-2)*(q-2) < 4.

structure RegularMap where
  p q V E F : ℕ
  hp : 3 ≤ p
  hq : 3 ≤ q
  hFace : 2 * E = p * F
  hVert : 2 * E = q * V

def euler (m : RegularMap) : ℤ :=
  (m.V : ℤ) - m.E + m.F

def tetra : RegularMap :=
  { p := 3, q := 3, V := 4, E := 6, F := 4, .. }
def cube : RegularMap :=
  { p := 4, q := 3, V := 8, E := 12, F := 6, .. }
def octa : RegularMap :=
  { p := 3, q := 4, V := 6, E := 12, F := 8, .. }
def icosa : RegularMap :=
  { p := 3, q := 5, V := 12, E := 30, F := 20, .. }
def dodeca : RegularMap :=
  { p := 5, q := 3, V := 20, E := 30, F := 12, .. }

theorem euler_tetra : euler tetra = 2
theorem euler_cube : euler cube = 2
theorem euler_octa : euler octa = 2
theorem euler_icosa : euler icosa = 2
theorem euler_dodeca : euler dodeca = 2

theorem schlafli_fail_three_six : ¬ (3 - 2) * (6 - 2) < 4
theorem schlafli_fail_four_four : ¬ (4 - 2) * (4 - 2) < 4

-- Level B namesake (only five pairs; residual OK)
theorem platonic_schlafli {p q : ℕ} (hp : 3 ≤ p) (hq : 3 ≤ q) :
    (p - 2) * (q - 2) < 4 ↔
      (p, q) = (3, 3) ∨ (p, q) = (3, 4) ∨ (p, q) = (3, 5) ∨
      (p, q) = (4, 3) ∨ (p, q) = (5, 3)
```

Five named `(V,E,F)` witnesses are load-bearing.
Handshaking `2E = pF = qV` is load-bearing.
Euler `= 2` on those witnesses is load-bearing.

**Level A may land only** the five witnesses +
Euler 2 + two failing pairs (optional extra:
handshaking+Euler ⇒ `(p-2)(q-2)<4` for one
named solid), **not** labelled Platonic.
Reuse Mathlib `Nat` arithmetic — **do not
re-prove** `Nat` lemmas / Coxeter `H₃`.

**Level B** is the namesake: those five
Schläfli pairs are the only solutions
`p,q ≥ 3`. Do not sorry the namesake; honest
partial is allowed (comment residual, not
`sorry`). Euler polyhedron / Coxeter
classification / Kepler–Poinsot are residual.

## Landmines

1. **Do not re-prove** `Nat` arithmetic /
   `CoxeterMatrix.H₃` / triangulated
   `Octahedron`.
   Already Mathlib. Use them if needed.
2. **This is not** the triangulated octahedron
   axiom. Different octahedron. Do not cite
   as Platonic.
3. **This is not** Coxeter `H₃` as namesake.
   Reflection matrix ≠ count of solids.
4. **This is not** Euler's polyhedron formula
   (Wiedijk #13). Residual of this id. Do not
   sorry a planar Euler theorem.
5. **This is not** British flag / Napoleon /
   Simson / Viviani / nine-point (consumed
   #145).
6. **This is not** friendship / Moore /
   Wantzel / Fine–Wilf / Kraft.
7. **This is not** `egyptian-fractions`
   (OPE-1278 leftover). Do not prove Egyptian
   here.
8. **Do not** re-prime the consumed mill list.
9. **Leave OPE-403 alone.** Leave OPE-1195
   leftover status alone.
10. **Do not import `Archive.*`.**
11. Default no claim. No novelty claim.

## Out of v1

- Euler polyhedron formula for planar graphs
  (Wiedijk #13)
- Coxeter classification / Kepler–Poinsot
  star polyhedra / regular 4-polytopes
- Geometric realization in `ℝ³` / metric
  regularity
- Prize claims / Millennium / Beal
