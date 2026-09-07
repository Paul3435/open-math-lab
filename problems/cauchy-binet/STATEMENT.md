# Cauchy–Binet formula (det of a rectangular product) — formalize-only

**id:** `cauchy-binet`
**ticket:** OPE-1130 Formalist Level A (Scout OPE-1125 RECOMMENDED PRIME; parent OPE-1124; Director OPE-1129; post schwartz-zippel #114 + hadamard-det #115)
**expected:** known-classical (Binet 1812 / Cauchy 1815) — **no novelty claim**

## Why not classical / why formalize-only

Settled linear algebra: for a commutative ring `R` and
finite index types `m, n`, matrices
`A : Matrix m n R` and `B : Matrix n m R`
satisfy

`det(A * B) = ∑_{S ⊆ n, |S| = |m|} det(A_{•,S}) det(B_{S,•})`

where `A_{•,S}` is the square submatrix of columns
indexed by `S` and `B_{S,•}` is the square
submatrix of rows indexed by `S`. Completely
classical (Binet 1812; Cauchy 1815). When
`|m| = |n|` the sum has one term and recovers
`det(A * B) = det A * det B`.

Not an open problem. Not a novelty claim.

**Not** `Matrix.det_mul` (`Determinant/Basic.lean`
L129) — already Mathlib; that is the **square**
multiplicativity. USE it as glue; do **not**
re-prove `det_mul`; do **not** cite it as
Cauchy–Binet. **Not** `Matrix.det_le`
(already-in `n! xⁿ`, AbsoluteValue.lean L36).
**Not** Hadamard determinant inequality
(consumed #115; USE `Matrix.det`; do **not**
re-prove `hadamard_det` / Level A glue; do **not**
revive Hadamard Level B). **Not** Gershgorin /
Levy–Desplanques. **Not** Hadamard product /
three-lines. **Not** Vandermonde det. **Not**
Kirchhoff matrix-tree (Cayley leftover-risk;
needs this formula; residual of *this* id).
**Not** expander-mixing (consumed adjMatrix).

Mathlib v4.10.0 already has the **matrix infra
this theorem needs**:

- `Matrix.det` (`Determinant/Basic.lean` L56 `abbrev`)
- `Matrix.det_mul` (`Determinant/Basic.lean` L129)
- `Matrix.det_apply` / `Perm` Leibniz sum (L59)
- `Matrix.det_isEmpty` (L85) / `det_unique` (L100)
- `Matrix.submatrix` (`Data/Matrix/Basic.lean` L2281)
- `Finset.powersetCard` (`Data/Finset/Powerset.lean` L171)

There is **no** Cauchy–Binet formula, **no**
named `cauchy_binet`, and **no** sum-of-minors
identity for `det(A * B)` anywhere under
`Mathlib/` or `Archive/` (word-regexp
`cauchyBinet` / `CauchyBinet` / `cauchy_binet`
this run → ZERO). Do **not** import `Archive.*`.

OPE-1110 shortlist is **CONSUMED** (#114+#115).
This is a **fresh** catalog-audit id, **not** a
Hadamard leftover continuation, **not** a
Schwartz–Zippel leftover, **not** a Kirchhoff /
Cayley leftover, **not** a prize leftover,
**not** a Formalist Level B revival, **not** a
third slot.

Mill NOW: finite rectangular-det identity after
Hadamard (row-norm bound on `det`) +
Schwartz–Zippel (polynomial zeros). `submatrix`
+ `powersetCard` are waiting the same way
`Matrix.det` waited for Hadamard.
**Not a rubber-stamp of `det_mul`.**

Hadamard STATEMENT named Cauchy–Binet as a
**different** theorem (out of *that* ticket).
This is that different theorem as a new id.

Do **not** describe an attack as discovering
Cauchy–Binet. Do **not** expand into Kirchhoff
matrix-tree / Gram-determinant / compound
matrices as extra namesakes (leftover-risk of
*this* id). Do **not** re-prove `det_mul` /
Hadamard Level B / Schwartz–Zippel Level B.

## Pinned convention (exact)

**v1 is the commutative-ring rectangular form.**
Encoding: Mathlib `Matrix.det` + `Matrix.submatrix`
+ `Finset.powersetCard`.

Suggested pin:

```text
-- Level A (not labelled Cauchy–Binet): |m|=0
-- det_isEmpty both sides 1; |m|=1 the 1×1
-- product is a dot product of a row and a
-- column; |m|=|n| unique full index set,
-- reduces to det_mul. Not labelled Cauchy–Binet.

-- Level B namesake
theorem cauchy_binet
    {R : Type*} [CommRing R]
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m n R) (B : Matrix n m R) :
    det (A * B) =
      ∑ S ∈ (Finset.univ : Finset n).powersetCard
          (Fintype.card m),
        det (A.submatrix id (subtype S)) *
        det (B.submatrix (subtype S) id)
```

`Fintype m` / `Fintype n` are load-bearing.
`CommRing R` is load-bearing (`det_mul` lives
there; no field required). The column-index
`subtype` / reindex `Equiv` is load-bearing
(Formalist may pick any equivalent encoding
that sums square minors of size `|m|` over
subsets of `n`). When `Fintype.card m > Fintype.card n`
the powerset is empty and both sides are `0`
(or `1` if `m` is empty) — load-bearing.

**Level A may land only** `|m|=0` / `|m|=1` /
square `det_mul` glue, **not** labelled
Cauchy–Binet. Reuse Mathlib `det` / `det_mul`
/ `submatrix` — **do not re-prove** `det_mul`.

**Level B** is the namesake: Leibniz expansion
of `det(A * B)` as a sum over `Perm m`, each
factor picking a column of `A` / row of `B`;
group terms by the image subset `S ⊆ n`.
Do not sorry the namesake; honest partial is
allowed (comment residual, not `sorry`).
Kirchhoff is residual.

Optional cheap corollary (not labelled
Cauchy–Binet, not required): Gram
`det(A * Aᵀ)` as a sum of squared minors
over `ℝ`. Do **not** expand into matrix-tree.

## Landmines

1. **Do not re-prove** `Matrix.det` / `det_mul` /
   `det_apply` / `submatrix` / `powersetCard` /
   `det_le` / Gershgorin. Already Mathlib. Use
   `det` and `det_mul`.
2. **This is not** `Matrix.det_mul` (Basic L129).
   Square special case. USE, do not re-prove,
   do not cite as Cauchy–Binet.
3. **This is not** Hadamard (#115). Different
   theorem (`|det| ≤ ∏ row-ℓ²`). USE `det`;
   do **not** revive `hadamard_det`.
4. **This is not** `Matrix.det_le` (`n! xⁿ`).
5. **This is not** Gershgorin / Hadamard product /
   three-lines / Vandermonde det.
6. **This is not** Kirchhoff matrix-tree (Cayley
   leftover-risk; residual of this id). **Not**
   Cayley's formula (#64 leftover).
7. **This is not** Schwartz–Zippel (#114) Level B.
8. **This is not** Ore / `konig_edge_chromatic` /
   AES / ostrowski-q / Hadamard Level B.
9. **This is not** krenn-gu / hou-zeng-pfc /
   sun-135. Do not revive.
10. **Do not re-prime** the consumed mill list
    (schwartz-zippel / hadamard-det /
    ore-hamiltonian / bipartite-chromatic-index /
    ostrowski-q / andrasfai-erdos-sos /
    noether-normalization / frobenius-real-division /
    mason-stothers / expander-mixing / zsigmondy /
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

Level A: empty index `det = 1` on both sides
(`det_isEmpty`). Size `1`: `A * B` is the
scalar `∑_j A i j * B j i`. Square case:
`powersetCard |m|` of `univ n` is a singleton
when `|m| = |n|`, and `submatrix` along the
unique `Equiv` is `det_mul`. **Not** labelled
Cauchy–Binet.

Level B: expand `det(A * B)` by Leibniz
(`det_apply`). Each permutation of the row
index picks, for every row, a column of `A`
and a matching row of `B`. The support of a
nonzero term is an injection `m → n`; group
by the image `S`. On each `S` the inner sum
is `det(A_{•,S}) det(B_{S,•})`. Cap two
levels. No Kirchhoff. No Hadamard re-proof.

## Canonical source (pin in this STATEMENT)

A.-L. Cauchy, *Mémoire sur les fonctions qui
ne peuvent obtenir que deux valeurs égales…*,
J. École Polytechnique 10 (1815). J. Binet,
*Mémoire sur un système de formules analytiques…*,
J. École Polytechnique 9 (1812). Textbook:
Horn–Johnson, *Matrix Analysis*, §0.8.7.
Compact form: Wikipedia *Cauchy–Binet formula*
— **v1 pins `CommRing`, finite `m, n`,
`det(A * B) = ∑_{|S|=|m|} det(A_{•,S}) det(B_{S,•})`.**
Type pin: Mathlib `Matrix.det` / `submatrix` /
`powersetCard`. `det_mul` is a **different**
already-in square identity, not this claim.

## Out of scope

- Kirchhoff matrix-tree / Cayley namesake revival
- Gram / compound-matrix extras as extra namesakes
- `det_mul` / Hadamard Level B / SZ Level B re-proof
- Ore Level B / `konig_edge_chromatic` / AES-B
- Prize leftovers (krenn-gu / hou-zeng / sun-135)
- Novelty / external claim
