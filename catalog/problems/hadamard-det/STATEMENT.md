# Hadamard determinant inequality (row ℓ² product bound) — formalize-only

**id:** `hadamard-det`
**ticket:** OPE-1110 Scout leftover slot #2 (parent OPE-1109; post ore-hamiltonian #111 + bipartite-chromatic-index #112)
**expected:** known-classical (Hadamard 1893) — **no novelty claim**

## Why not classical / why formalize-only

Settled linear algebra: a real `n × n` matrix `A`
satisfies `|det A| ≤ ∏ᵢ ‖rowᵢ(A)‖₂`, where
`‖rowᵢ‖₂ = √(∑ⱼ Aᵢⱼ²)`. Completely classical
(Hadamard, Bull. Sci. Math. 17 (1893)). Equality
when the rows are pairwise orthogonal (or a row
is zero).

Not an open problem. Not a novelty claim.

**Not** `Matrix.det_le` (`AbsoluteValue.lean` L36) —
already Mathlib; that is the **weaker** permutation
bound `|det A| ≤ n! xⁿ` when every entry is bounded
by `x`. USE nothing as a namesake; do **not**
re-prove `det_le`; do **not** cite it as Hadamard.
**Not** Gershgorin / Levy–Desplanques (already
`Gershgorin.lean` `eigenvalue_mem_ball` /
`det_ne_zero_of_sum_row_lt_diag`). **Not** the
Hadamard *product* (`Data/Matrix/Hadamard.lean`).
**Not** Hadamard three-lines
(`Analysis/Complex/Hadamard.lean`). **Not**
Vandermonde det (already `LinearAlgebra/Vandermonde.lean`).
**Not** Cauchy–Binet / Kirchhoff matrix-tree.
**Not** expander-mixing (consumed adjMatrix infra).
Complex conjugate-transpose form **out of v1**.

Mathlib v4.10.0 already has the **matrix infra
this theorem needs**:

- `Matrix.det` (`Determinant/Basic.lean` L56 `abbrev`)
- `Matrix.det_apply` / `detRowAlternating`
  (`Determinant/Basic.lean` L59 / L52)
- Euclidean `Real.sqrt` / `∑ j, A i j ^ 2`

There is **no** Hadamard determinant inequality,
**no** `|det| ≤ ∏ row-ℓ²` bound, and **no** named
`hadamard_det` anywhere under `Mathlib/` or `Archive/`
(word-regexp `hadamard.inequal` / `det_le_prod_norm`
this run → ZERO). Do **not** import `Archive.*`.

OPE-1095 shortlist is **CONSUMED** (#111+#112).
This is a **fresh** catalog-audit id, **not** an
expander-mixing leftover, **not** an Ore leftover,
**not** a König line-colouring leftover, **not** a
prize leftover, **not** a Formalist Level B revival,
**not** a third slot.

Mill NOW: finite linear-algebra inequality leftover
beside Schwartz–Zippel (polynomial zeros). `Matrix.det`
is waiting the same way `totalDegree` waits for SZ.
**Not a rubber-stamp of `det_le`.**

Do **not** describe an attack as discovering
Hadamard. Do **not** expand into complex /
column-norm / volume-of-parallelotope extras as
extra namesakes (leftover-risk of *this* id). Do
**not** re-prove Gershgorin / `det_le` / SZ /
Ore Level B / `konig_edge_chromatic`.

## Pinned convention (exact)

**v1 is the real square Euclidean-row form only.**
Encoding: Mathlib `Matrix.det` + `Real.sqrt` of the
sum of squares of a row.

Suggested pin:

```text
-- Level A (not labelled Hadamard): n empty / 1;
-- n=2 explicit 2×2; pairwise-orthogonal rows
-- ⇒ |det| = product of row norms (Gram diagonal).
-- Not labelled Hadamard.

-- Level B namesake
def rowNorm {n : Type*} [Fintype n]
    (A : Matrix n n ℝ) (i : n) : ℝ :=
  Real.sqrt (∑ j, A i j ^ 2)

theorem hadamard_det
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) :
    |A.det| ≤ ∏ i, rowNorm A i
```

`Fintype n` is load-bearing. Real coefficients are
load-bearing (complex needs conjugate transpose;
out of v1). Euclidean `ℓ²` row norm is load-bearing
(entrywise `n! xⁿ` is the already-in `det_le`, a
**different** theorem).

**Level A may land only** `n=0/1` / `n=2` /
orthogonal-rows equality, **not** labelled Hadamard.
Reuse Mathlib `det` — **do not re-prove** `det_le`
or Gershgorin.

**Level B** is the namesake: Gram matrix
`G = A * Aᵀ` is positive semidefinite,
`(det A)² = det G`, and `det G ≤ ∏ᵢ Gᵢᵢ`
(AM-GM on eigenvalues, or induction / row
operations). Do not sorry the namesake; honest
partial is allowed (comment residual, not `sorry`).
Complex form is residual.

Optional cheap corollary (not labelled Hadamard,
not required): `|det A| ≤ ∏ᵢ ‖colᵢ(A)‖₂` by
`Aᵀ`. Do **not** expand into Fischer / Minkowski
det inequalities.

## Landmines

1. **Do not re-prove** `Matrix.det` / `det_apply` /
   `det_le` / `eigenvalue_mem_ball` /
   `det_ne_zero_of_sum_row_lt_diag`. Already
   Mathlib. Use `det`; ignore the others as
   namesakes.
2. **This is not** `Matrix.det_le` (AbsoluteValue
   L36). Weaker different bound (`n! xⁿ`).
3. **This is not** Gershgorin / Levy–Desplanques
   (already `Gershgorin.lean`).
4. **This is not** the Hadamard *product*. **Not**
   Hadamard three-lines.
5. **This is not** Vandermonde det (already
   Mathlib). **Not** Cauchy–Binet. **Not**
   Kirchhoff matrix-tree (Cayley leftover-risk;
   refused this run).
6. **v1 is real + Euclidean rows.** Complex /
   column-only namesake out of v1.
7. **This is not** expander-mixing (consumed
   adjMatrix infra). **Not** Schwartz–Zippel
   (the prime).
8. **This is not** Ore (#111) / König
   line-colouring (#112) / AES / ostrowski-q
   Level B.
9. **This is not** ostrowski-q Level B /
   andrasfai-erdos-sos Level B /
   frobenius-real-division Level B /
   noether-normalization Level B / krenn-gu /
   hou-zeng-pfc / sun-135. Do not revive.
10. **Do not re-prime** the consumed mill list
    (ore-hamiltonian / bipartite-chromatic-index /
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

Level A: `n=0/1` trivial (`det` of `1×1` is the
entry). `n=2` is an explicit square-root inequality.
If rows are pairwise orthogonal, `A * Aᵀ` is
diagonal with the squared row norms, so
`|det A| = ∏ rowNorm`. **Not** labelled Hadamard.

Level B: Gram `G = A * Aᵀ` is PSD and
`(det A)² = det G`. For a PSD matrix,
`det G ≤ ∏ Gᵢᵢ` (eigenvalue AM-GM, or
induction by bordering). Cap two levels. No
complex. No Gershgorin re-proof.

## Canonical source (pin in this STATEMENT)

J. Hadamard, *Résolution d'une question relative aux
déterminants*, Bull. Sci. Math. 17 (1893) 240–246.
Textbook: Horn–Johnson / Beckenbach–Bellman.
Compact form: Wikipedia *Hadamard inequality* —
**v1 pins real square `A` and
`|det A| ≤ ∏ᵢ ‖rowᵢ‖₂`.** Type pin: Mathlib
`Matrix.det` / Euclidean row norm. `det_le`
(`n! xⁿ`) is a **different** already-in bound,
not this claim.

## Out of scope

- Complex conjugate-transpose Hadamard
- Fischer / Minkowski det inequalities
- Gershgorin / `det_le` re-proof
- Kirchhoff matrix-tree / Cauchy–Binet
- Schwartz–Zippel (the prime)
- Ore Level B / `konig_edge_chromatic` / AES-B
- Prize leftovers (krenn-gu / hou-zeng / sun-135)
- Novelty / external claim
