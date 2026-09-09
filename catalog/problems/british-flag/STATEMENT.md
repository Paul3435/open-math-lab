# British flag theorem for a rectangle — formalize-only

**id:** `british-flag`
**ticket:** OPE-1273 Formalist Level A (Scout OPE-1263 leftover slot #2; Director OPE-1272)
**expected:** known-classical (British flag theorem: in the
plane of rectangle `ABCD`, every point `P` satisfies
`PA² + PC² = PB² + PD²`) — **no novelty claim**

## Why not classical / why formalize-only

Settled Euclidean geometry: if `ABCD` is a rectangle
(so opposite corners are the two diagonals) then for
every point `P` in the Euclidean plane,
`dist(P,A)² + dist(P,C)² = dist(P,B)² + dist(P,D)²`.
Completely classical (the Union-Jack identity; a
coordinate / inner-product calculation).

Not an open problem. Not a novelty claim.

**Not** the parallelogram law
`‖x+y‖² + ‖x−y‖² = 2(‖x‖²+‖y‖²)` (already
`parallelogram_law`, InnerProductSpace/Basic.lean L590
— **different theorem**; USE as glue if needed; do
**not** re-prove; do **not** cite as British flag).
**Not** Ptolemy (already Sphere/Ptolemy.lean). **Not**
law of cosines (already Triangle.lean). **Not** Euler
line (already MongePoint.lean). **Not** Heron
(consumed). **Not** Wantzel / `IsConstructible`
(consumed #133). **Not** Napoleon / Simson /
nine-point / angle-bisector (residual of *this* id;
do **not** sorry Napoleon). **Not** Fine–Wilf (prime
of this shortlist).

Mathlib v4.10.0 already has the **Euclidean /
inner-product infra this theorem needs**:

- `EuclideanSpace` (`PiL2.lean` L100)
- `parallelogram_law` (InnerProductSpace/Basic.lean L590)
  — **not** namesake
- `dist` (metric) / `norm_sq` inner-product identities
- `Geometry.Euclidean.Basic` / `Triangle.lean` law of
  cosines — **not** namesake

There is **no** named British flag theorem, **no**
`britishFlag` / `british_flag` / `BritishFlag`
anywhere under `Mathlib/` or `Archive/` or `ProofLab/`
(this run → ZERO on those names; Napoleon / Simson /
Viviani / angle-bisector theorem also ZERO). Do
**not** import `Archive.*`.

OPE-1248 shortlist is **CONSUMED**
(#141+#142). This is a **fresh** catalog-audit
leftover id, **not** a Sherman leftover, **not** a
Graham–Pollak leftover, **not** a Heron leftover,
**not** a Wantzel leftover, **not** a prize leftover,
**not** a Formalist Level B revival, **not** a
third slot.

Mill NOW: finite rectangle distance-sum leftover
beside Fine–Wilf (word periods). `EuclideanSpace` +
`parallelogram_law` are waiting the same way
`completeGraph` waited for Graham–Pollak. **Not a
rubber-stamp of the parallelogram law.** **Not a
rubber-stamp of Ptolemy.**

Do **not** describe an attack as discovering the
British flag theorem. Do **not** expand into Napoleon
/ Simson / nine-point / angle-bisector as extra
namesakes (Napoleon is leftover-risk of *this* id).

## Pinned convention (exact)

**v1 Level A is the identity on an axis-aligned
rectangle in `EuclideanSpace ℝ (Fin 2)` at named
points: origin, a vertex, and the centre of the unit
square, not labelled British flag.** Opposite-corner
pairing is load-bearing. `dist` squared is
load-bearing.

Suggested pin:

```text
-- Level A (not labelled British flag):
-- unit square corners A=(0,0), B=(1,0), C=(1,1), D=(0,1).
-- Origin / vertex C / centre.

abbrev Plane2 := EuclideanSpace ℝ (Fin 2)

-- Encode corners with EuclideanSpace.single / explicit coordinates.
-- Zero holes. Not labelled British flag.

def unitA : Plane2 := EuclideanSpace.single (0 : Fin 2) 0
def unitB : Plane2 := EuclideanSpace.single (0 : Fin 2) 1
def unitC : Plane2 :=
  EuclideanSpace.single (0 : Fin 2) 1 + EuclideanSpace.single (1 : Fin 2) 1
def unitD : Plane2 := EuclideanSpace.single (1 : Fin 2) 1

theorem british_flag_unit_origin :
    dist (0 : Plane2) unitA ^ 2 + dist 0 unitC ^ 2
      = dist 0 unitB ^ 2 + dist 0 unitD ^ 2

theorem british_flag_unit_at_C :
    dist unitC unitA ^ 2 + dist unitC unitC ^ 2
      = dist unitC unitB ^ 2 + dist unitC unitD ^ 2

theorem british_flag_unit_center
    (p : Plane2) (hp : p = EuclideanSpace.single (0 : Fin 2) (1/2)
                          + EuclideanSpace.single (1 : Fin 2) (1/2)) :
    dist p unitA ^ 2 + dist p unitC ^ 2
      = dist p unitB ^ 2 + dist p unitD ^ 2

-- Level B namesake (every point of the plane; residual OK)
theorem british_flag
    (a b : ℝ) (p : Plane2) :
    dist p ![(0:ℝ), 0] ^ 2 + dist p ![a, b] ^ 2
      = dist p ![a, 0] ^ 2 + dist p ![0, b] ^ 2
```

Finite unit-square origin / vertex / centre is
load-bearing. Axis-aligned rectangle in `Fin 2` is
load-bearing. Squared `dist` is load-bearing.

**Level A may land only** origin / a corner / centre
of the unit square (optional extra: a generic
`(x,y)` on the unit square, still not labelled
British flag). Reuse Mathlib `EuclideanSpace` /
`dist` / `parallelogram_law` — **do not re-prove**
inner product or parallelogram law.

**Level B** is the namesake: every point of the plane
of an axis-aligned rectangle. Do not sorry the
namesake; honest partial is allowed (comment
residual, not `sorry`). Napoleon / Simson are
residual. Definition risk: encode corners without
`sorry`; `EuclideanSpace.single` / `![(0:ℝ),0]` is
the intended pin, not a hole.

## Landmines

1. **Do not re-prove** `EuclideanSpace` / `dist` /
   `parallelogram_law` / law of cosines / Ptolemy.
   Already Mathlib. Use them.
2. **This is not** the parallelogram law (already-in).
   Different theorem (rectangle opposite-corners vs
   parallelogram identity). Do not cite as British
   flag.
3. **This is not** Ptolemy / law of cosines / Euler
   line / Heron / Wantzel.
4. **This is not** Napoleon / Simson / nine-point /
   angle-bisector. Residual of this id. Do not sorry
   Napoleon.
5. **This is not** `fine-wilf` (OPE-1263 prime). Do
   not prove Fine–Wilf here.
6. **This is not** `sherman-morrison` (#141) /
   Woodbury / `graham-pollak` (#142).
7. **Do not** re-prime the consumed mill list.
8. **Leave OPE-403 alone.** Leave OPE-1195 leftover
   status alone.
9. **Do not import `Archive.*`.**
10. Default no claim. No novelty claim.

## Out of v1

- Napoleon equilateral-on-sides / Simson line /
  nine-point circle / angle-bisector theorem
- Non-rectangular parallelograms as namesake
  (parallelogram law already-in)
- Prize claims / Millennium / Beal
