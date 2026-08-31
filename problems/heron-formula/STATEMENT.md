# Heron's formula (formalize-only)

**id:** `heron-formula`
**ticket:** OPE-788 Scout leftover slot #2 (support OPE-787; post bipartite #79 + Euclid–Euler #80)
**expected:** known-classical (Heron of Alexandria / Wiedijk 100 no. 57) — **no novelty claim**

## Why not classical / why formalize-only

Settled Euclidean-geometry identity: the area of a triangle
with side lengths `a, b, c` is

```text
√(s (s-a) (s-b) (s-c))    where s = (a+b+c)/2
```

Not an open problem.

Mathlib v4.10.0 already has the **geometry this theorem needs**:

- `law_cos` /
  `dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle`
  (`Geometry/Euclidean/Triangle.lean`) — **law of cosines**.
  Glue, **not** this namesake.
- `∠` / `angle_nonneg` / `angle_le_pi` / `Real.sin` /
  `sin_eq_sqrt_one_sub_cos_sq` / `Real.sqrt`
- `dist` on a Euclidean affine space (`NormedAddTorsor`)

There is **no** Heron theorem and **no** semiperimeter-area
identity anywhere under `Mathlib/` (word-regexp `heron` /
`semiperimeter` this run → ZERO theorem files; Euler–Mascheroni
`γ` hits are a different word). The theorem **is** in
`Archive/Wiedijk100Theorems/HeronsFormula.lean`
(`Theorems100.heron`). **Do not import `Archive.*`.** Re-prove
in ProofLab. Archive existence is feasibility evidence, not a
citation of a Mathlib theorem.

This is **not** Sylvester–Gallai (OPE-770 bench: Kelly
closest-point Euclidean-metric glue **sink**; **different**
statement, **different** proof shape). Heron is an algebraic
trig identity from the law of cosines, not a closest-point
argument. **Not** de Bruijn–Erdős incidence
(`HasLines.card_le` already upstream). **Not** Pick's theorem
(lattice polygons; encoding sink). **Not** five-colour / planar
graph defs.

OPE-770 did **not** consider this id. Fresh leftover after the
Euclid–Euler Archive-transcription leftover was **CONSUMED**
(#80). Mill: geometry/analysis leftover after an additive
prime — not a third additive theorem (Mann/Heilbronn refused).

Do **not** describe an attack as discovering triangle area.
Do **not** expand into Pick / Sylvester–Gallai / Ceva / Morley.

## Pinned convention (exact)

**Encoding pin:** match Archive `Theorems100.heron` **without
importing it**. LHS is the `½ab sin γ` area formula; RHS is
Heron's radical. No new `area` structure required.

```text
theorem heron {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    {p1 p2 p3 : P} (h1 : p1 ≠ p2) (h2 : p3 ≠ p2) :
    let a := dist p1 p2
    let b := dist p3 p2
    let c := dist p1 p3
    let s := (a + b + c) / 2
    1 / 2 * a * b * Real.sin (∠ p1 p2 p3)
      = Real.sqrt (s * (s - a) * (s - b) * (s - c))
```

`h1` / `h2` are load-bearing (`a, b > 0`). Degenerate collinear
triangles are allowed by the identities (sin = 0, radical = 0);
do not add an extra non-degeneracy namesake.

**Level A** may land the cosine-rule rewrite
`cos γ = (a²+b²-c²)/(2ab)` via `law_cos` plus the
`1 - cos² = sin²` split, **not** labelled Heron.
**Level B** is the namesake.

## Landmines

1. **Do not import `Archive.Wiedijk100Theorems.HeronsFormula`.**
   Standing ProofLab rule. Transcribe the classical argument.
2. **This is not the law of cosines.** Already `law_cos`. Use
   it; do not re-prove it as this namesake.
3. **This is not Sylvester–Gallai.** Still a Euclidean bench
   (Kelly closest-point sink). Different statement. Do **not**
   invent it as a leftover of this id.
4. **This is not de Bruijn–Erdős incidence.**
   `HasLines.card_le` is already Mathlib.
5. **This is not Pick's theorem** (lattice `I + B/2 − 1`).
   Encoding-from-scratch; out of v1.
6. **This is not five-colour / planar / Euler `V−E+F=2`.**
   ZERO planar-graph defs. Stay on Euclidean triangles.
7. **Do not re-prime** bipartite-odd-cycle / euclid-euler-perfect
   / moore / stirling / kst / pentagonal / sunflower / CNS /
   kruskal-katona / oddtown / cayley / mycielski / friendship /
   havel / menger / greedy / Brooks / Dilworth / Eulerian /
   König / Dirac / EKR / vosper-cauchy-davenport.
8. **Leave OPE-403 alone.**

## Proof sketch (classical, Archive transcription)

Level A: `law_cos` ⇒ `cos γ = (a²+b²−c²)/(2ab)`; rewrite
`1 − cos² γ` as a four-square difference. **Not** labelled
Heron.

Level B: namesake `heron`. `sin γ = √(1−cos² γ)` on
`γ ∈ [0, π]`; algebra to `√(s(s−a)(s−b)(s−c))`. Cap two
levels. No Pick, no Sylvester–Gallai, no Ceva, no Morley.

## Canonical source (pin in this STATEMENT)

Heron of Alexandria, *Metrica* (the `√s(s−a)(s−b)(s−c)` form).
Wiedijk 100 Theorem 57 is the **same** statement (Archive-only
at this pin) — do not import. Type pin: Euclidean affine
`dist` / `∠` / `Real.sin` / `Real.sqrt`, matching Archive
`Theorems100.heron`. Law of cosines, Sylvester–Gallai, Pick,
and de Bruijn–Erdős incidence are different statements, not
this claim.

## Out of scope

- Archive import
- Law of cosines re-proof
- Sylvester–Gallai / Pick / Ceva / Menelaus / Morley
- Planar-graph five-colour / Euler characteristic
- Re-primes listed above
- Novelty / external claim
