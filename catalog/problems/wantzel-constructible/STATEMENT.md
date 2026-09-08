# Wantzel cube-doubling / constructible degree — formalize-only

**id:** `wantzel-constructible`
**ticket:** OPE-1200 Scout leftover slot #2 (parent OPE-1199; post schur-product #129 + lame-euclid #130)
**expected:** known-classical (Wantzel 1837) — **no novelty claim**

## Why not classical / why formalize-only

Settled field theory / Euclidean
constructibility: a complex number obtained
from `ℚ` by a finite tower of quadratic
extensions has minimal-polynomial degree a
power of `2`. Hence `³√2` (minpoly `X³ − 2`,
degree `3`) is not constructible — doubling
the cube is impossible by straightedge and
compass. Completely classical (Wantzel 1837).
Wiedijk 100 theorems **#8** has **no Mathlib
decl** this pin.

Not an open problem. Not a novelty claim.

**Not** Abel–Ruffini / `IsSolvableByRad`
(already `FieldTheory/AbelRuffini.lean` L194;
Archive Wiedijk also has
`exists_not_solvable_by_rad`). Different
theorem (radicals vs quadratic towers). USE
nothing from Abel–Ruffini as namesake; do
**not** re-prove insolvability of the
quintic; do **not** import `Archive.*`.
**Not** primitive element / Galois
correspondence (Noether leftover-risk;
primitive element already-in). **Not**
Eisenstein criterion as namesake —
`irreducible_of_eisenstein_criterion`
(`EisensteinCriterion.lean` L82) is **glue**,
USE for `X³ − 2`, do **not** re-prove.
**Not** FTA / rational-root / Gauss lemma as
namesake. **Not** angle trisection (the other
half of 100.yaml #8) — residual of *this* id.
**Not** π-transcendental / Hermite–Lindemann
/ e-transcendental (e-irrational consumed
#92 is a **different** theorem).

Mathlib v4.10.0 already has the **minpoly /
tower / Eisenstein infra this theorem needs**:

- `minpoly` (`FieldTheory/Minpoly/Basic.lean` L36)
- `IntermediateField` (`FieldTheory/IntermediateField.lean` L47)
- `irreducible_of_eisenstein_criterion`
  (`RingTheory/EisensteinCriterion.lean` L82)
- `AdjoinRoot` / `Polynomial.X` / `C`
- tower degree multiplicativity (`finrank_mul_finrank`)

There is **no** constructible-number predicate,
**no** named `Wantzel` / `wantzel` /
`IsConstructible` / `constructible` /
`doubling_the_cube` / `trisect` anywhere under
`Mathlib/` or `Archive/` or `ProofLab/`
(this run → ZERO; 100.yaml #8 has no `decl`).
Do **not** import `Archive.*`.

OPE-1189 shortlist is **CONSUMED** (#129+#130).
This is a **fresh** catalog-audit id, **not**
a Lamé leftover, **not** a Schur product
leftover, **not** an Abel–Ruffini re-proof,
**not** a Noether / primitive-element /
Galois leftover, **not** a prize leftover,
**not** a Formalist Level B revival, **not**
a third slot.

Mill NOW: finite Wantzel leftover beside
circulant-det. `minpoly` + Eisenstein are
waiting the same way `Nat.fib` waited for
Lamé. **Not a rubber-stamp of Abel–Ruffini.**

Do **not** describe an attack as discovering
Wantzel's theorem. Do **not** expand into
angle trisection / Galois correspondence /
quintic insolvability as extra namesakes
(leftover-risk of *this* id).

## Pinned convention (exact)

**v1 Level A is the degree obstruction for
`X³ − 2`: Eisenstein irreducibility, adjoin
degree `3`, and `3` is not a power of `2`.
Not labelled Wantzel.** Work in `AdjoinRoot`
(do **not** require a `ℝ` cube-root).

Suggested pin:

```text
-- Level A (not labelled Wantzel):
-- X^3 - 2 irreducible over ℚ via Eisenstein;
-- AdjoinRoot has finrank 3;
-- 3 is not a power of 2.
-- Not labelled Wantzel.

theorem irreducible_X_pow_three_sub_two :
    Irreducible (X ^ 3 - C 2 : ℚ[X])

theorem adjoinRoot_X_pow_three_sub_two_finrank :
    finrank ℚ (AdjoinRoot (X ^ 3 - C 2 : ℚ[X])) = 3

theorem not_pow_two_three : ∀ k : ℕ, 3 ≠ 2 ^ k

-- Level B namesake
-- IsConstructible = iterated quadratic IntermediateField tower.
theorem wantzel {x : ℝ} (h : IsConstructible ℚ x) :
    ∃ k : ℕ, (minpoly ℚ x).natDegree = 2 ^ k
```

`AdjoinRoot` / `ℚ` / Eisenstein are
load-bearing for Level A. Tower degree `≤ 2`
is load-bearing for the namesake.

**Level A may land only** Eisenstein
irreducibility of `X³ − 2` / adjoin `finrank
= 3` / `3 ≠ 2^k`, **not** labelled Wantzel.
Reuse Mathlib `minpoly` / Eisenstein /
`AdjoinRoot` / `finrank` — **do not re-prove**
Eisenstein's criterion, minpoly uniqueness, or
tower multiplicativity.

**Level B** is the namesake: encode
`IsConstructible` as a finite tower of
`IntermediateField`s each of degree `≤ 2`,
and conclude minpoly degree is a power of
`2`. Do not sorry the namesake; honest
partial is allowed (comment residual, not
`sorry`). Angle trisection / full Euclidean
geometry / Galois correspondence are residual.

## Landmines

1. **Do not re-prove** `minpoly` /
   `irreducible_of_eisenstein_criterion` /
   `IntermediateField` / `AdjoinRoot` /
   `finrank_mul_finrank`. Already Mathlib.
   Use them.
2. **This is not** Abel–Ruffini /
   `IsSolvableByRad` / quintic insolvability
   (already-in Mathlib + Archive). Different
   theorem. Do not re-prove. Do not import
   `Archive.*`.
3. **This is not** primitive element / Galois
   correspondence / Noether normalization
   Level B (#106). Field-theory leftover-risk.
4. **This is not** angle trisection (100.yaml
   #8 other half). Residual of *this* id.
5. **This is not** e-irrational (#92) /
   e-transcendental / π-irrational /
   Hermite–Lindemann. Different theorems.
6. **This is not** FTA / rational-root /
   Gauss lemma / Eisenstein as *namesake*
   (Eisenstein is glue).
7. **This is not** `circulant-det` (OPE-1200
   prime) / `det_vandermonde` / pfaffian.
8. **This is not** `lame-euclid` (#130) /
   `schur-product` (#129) Level B.
9. **This is not** krenn-gu / hou-zeng-pfc /
   sun-135 / AES / ostrowski / noether
   Level B / frobenius-real-division Level B.
10. **Do not re-prime** the consumed mill list
    (lame-euclid / schur-product /
    farey-sequence / gale-shapley /
    nash-williams-arboricity /
    birkhoff-von-neumann / hook-length /
    singleton-bound / cauchy-binet /
    bollobas-two-families / schwartz-zippel /
    hadamard-det / ore-hamiltonian /
    bipartite-chromatic-index / ostrowski-q /
    andrasfai-erdos-sos / noether-normalization /
    frobenius-real-division / mason-stothers /
    expander-mixing / zsigmondy /
    erdos-ramsey-lower / e-irrational / descartes /
    n-fold-inclusion-exclusion / wolstenholme /
    lovasz-local-lemma / korselt-carmichael / vosper /
    heron / euclid-euler / bipartite / moore /
    stirling / kst / pentagonal / sunflower / CNS /
    kk / oddtown / cayley / mycielski / friendship /
    havel / menger / greedy / Brooks / Dilworth /
    Eulerian / König / Dirac / EKR / Ramsey
    r33/r35/r333 / frobenius-coin-problem).
11. **No `Archive.*` import.**
12. **Leave OPE-403 alone.**

## Proof sketch (classical)

Level A: `X³ − 2` is Eisenstein at the prime
ideal `(2)` (`irreducible_of_eisenstein_criterion`
USE, not re-proved). `AdjoinRoot` of an
irreducible degree-3 polynomial has `finrank
3`. `3 ≠ 2^k` by unique factorisation / a
one-line induction. **Not** labelled Wantzel.

Level B: encode constructible numbers as
elements of a finite tower of
`IntermediateField`s with each relative
degree `≤ 2`. Tower multiplicativity gives
`[K:ℚ] | 2^k`. Minpoly degree divides the
extension degree, hence is a power of `2`.
Then `³√2` (or any root of `X³ − 2`) is not
constructible. Cap two levels. No angle
trisection. No Abel–Ruffini re-proof. No
Galois correspondence.

## Canonical source (pin in this STATEMENT)

P. Wantzel, *Recherches sur les moyens de
reconnaître si un problème de Géométrie peut
se résoudre avec la règle et le compas*,
J. Math. Pures Appl. 2 (1837) 366–372.
Wiedijk 100 theorems #8 (no Mathlib `decl`
this pin). Compact form: Wikipedia
*Wantzel's theorem* / doubling the cube.
Type pin: `minpoly` / Eisenstein /
`AdjoinRoot` / `IntermediateField` / `ℚ`.
Abel–Ruffini is a **different** already-in
theorem. Angle trisection is the **other
half** of #8 (residual).

## Out of scope

- Angle trisection / triple-angle for cosine
- Full Euclidean plane geometry of constructible
  points
- Galois correspondence / solvability of
  Gal(minpoly)
- Abel–Ruffini quintic
- π / e transcendence
- Prize leftovers (krenn-gu / hou-zeng / sun-135)
- Novelty / external claim
