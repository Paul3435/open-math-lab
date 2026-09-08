# Birkhoff–von Neumann theorem (doubly stochastic matrices) — formalize-only

**id:** `birkhoff-von-neumann`
**ticket:** OPE-1157 Scout RECOMMENDED PRIME (parent OPE-1156; post singleton-bound #120 + hook-length #121)
**expected:** known-classical (Birkhoff 1946 / von Neumann 1953) — **no novelty claim**

## Why not classical / why formalize-only

Settled convex geometry / matrix combinatorics:
a nonnegative real `n × n` matrix with every
row-sum and every column-sum equal to `1`
(a *doubly stochastic* matrix) lies in the
convex hull of the permutation matrices.

Completely classical (Birkhoff 1946; von Neumann
1953 for the polytope). Equality / extreme-point
language is residual of *this* id.

Not an open problem. Not a novelty claim.

**Not** Birkhoff's representation theorem for
distributive lattices (`Order/Birkhoff.lean`
`exists_birkhoff_representation` / `birkhoffSet`)
— already Mathlib; that is a **different
Birkhoff**. Do **not** cite lattice embeddings
as BvN. **Not** Birkhoff averages / mean ergodic
theorem (`Analysis/InnerProductSpace/MeanErgodic.lean`)
— different Birkhoff. **Not** Hall's marriage
theorem (`Combinatorics/Hall/Basic.lean`
`Finset.all_card_le_biUnion_card_iff_exists_injective`
L116) — already Mathlib; USE as glue for the
namesake engine; do **not** re-prove Hall.
**Not** König matching `ν=τ` (consumed #48+#50).
**Not** Cauchy–Binet (#117) / Hadamard (#115) /
`Matrix.det`. **Not** LDL / Cholesky
(`LDL.lower_conj_diag` already-in). **Not**
Gale–Ryser / transportation polytopes
(residual of this id).

Mathlib v4.10.0 already has the **matrix /
convex / matching infra this theorem needs**:

- `Matrix` / `Matrix.one` / `stdBasisMatrix`
  (`Data/Matrix/Basis.lean` L30)
- `convexHull` (`Analysis/Convex/Hull.lean` L42)
- `Equiv.Perm`
- Hall SDR (Hall/Basic.lean L116)
- `Finset.sum` / `Fintype`

There is **no** Birkhoff–von Neumann theorem,
**no** named `birkhoffVonNeumann` /
`isDoublyStochastic` / `doublyStochastic` /
`permMatrix` / `permutationMatrix` anywhere
under `Mathlib/` or `Archive/` (word-regexp
this run → ZERO). Do **not** import
`Archive.*`.

OPE-1142 shortlist is **CONSUMED** (#120+#121).
This is a **fresh** catalog-audit id, **not**
a Singleton leftover continuation, **not** a
hook-length leftover, **not** a Cauchy–Binet
leftover, **not** a König leftover revival,
**not** a prize leftover, **not** a Formalist
Level B revival, **not** a third slot.

Mill NOW: finite convex-matrix theorem after
Singleton (coding puncture) + hook-length
(tableau count). `stdBasisMatrix` + `convexHull`
are waiting the same way `hammingDist` waited
for Singleton. **Not a rubber-stamp of Hall.**

Do **not** describe an attack as discovering
BvN. Do **not** expand into Gale–Ryser /
unimodular transportation / Birkhoff polytope
volume as extra namesakes (leftover-risk of
*this* id).

## Pinned convention (exact)

**v1 is the combinatorial BvN inclusion only.**
Encoding: `Matrix (Fin n) (Fin n) ℝ`. Count /
convex combination in `ℝ`.

Suggested pin:

```text
-- Level A (not labelled Birkhoff / von Neumann):
-- n = 0 empty; n = 1 unique [1]; every
-- permutation matrix is doubly stochastic;
-- convex combinations of doubly stochastic
-- matrices are doubly stochastic (hence
-- conv(perm) ⊆ DS); n = 2 explicit
-- [[a, 1-a], [1-a, a]] = a • I + (1-a) • σ.
-- Not labelled Birkhoff.

def permMatrix {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if σ j = i then 1 else 0

def IsDoublyStochastic {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i j, 0 ≤ A i j) ∧
  (∀ i, ∑ j, A i j = 1) ∧
  (∀ j, ∑ i, A i j = 1)

-- Level B namesake
theorem birkhoff_von_neumann {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : IsDoublyStochastic A) :
    A ∈ convexHull ℝ
      (Set.range (permMatrix (n := n)))
```

Finite `Fin n` is load-bearing. Nonnegativity
and both marginals are load-bearing (a
nonnegative matrix with only row-sums 1 is
*row-stochastic*, a different theorem).
Peeling a permutation via Hall on the
positive support is the namesake engine,
not a second theorem.

**Level A may land only** empty / `n = 1` /
permutation matrices are DS / `conv(perm) ⊆ DS`
/ `n = 2` convex combination of `I` and the
transposition, **not** labelled Birkhoff.
Reuse Mathlib `stdBasisMatrix` / `convexHull` /
Hall — **do not re-prove** Hall or lattice
Birkhoff.

**Level B** is the namesake: `DS ⊆ conv(perm)`.
Do not sorry the namesake; honest partial is
allowed (comment residual, not `sorry`).
Gale–Ryser / Birkhoff-polytope volume are
residual.

## Landmines

1. **Do not re-prove** `stdBasisMatrix` /
   `convexHull` / Hall / `Matrix.one` /
   `Equiv.Perm`. Already Mathlib. Use them.
2. **This is not** Birkhoff lattice
   representation (`Order/Birkhoff.lean`).
   Different theorem. Different Birkhoff.
3. **This is not** Birkhoff averages / mean
   ergodic theorem.
4. **This is not** Hall's marriage theorem.
   USE as glue; do not cite Hall as BvN.
5. **This is not** König matching `ν=τ`
   (consumed). Do not revive König Level B.
6. **This is not** Cauchy–Binet (#117) /
   Hadamard (#115) / `Matrix.det` /
   Vandermonde (already `det_vandermonde`) /
   LDL (`LDL.lower_conj_diag` already-in).
7. **This is not** Gale–Ryser / transportation
   polytope / unimodular decomposition.
   Residual of this id.
8. **This is not** Singleton (#120) /
   Hamming-bound / Plotkin / hook-length (#121) /
   Catalan / RSK / `cauchy_binet` / `bollobas` /
   Ore / `konig_edge_chromatic` / AES /
   ostrowski / krenn-gu / hou-zeng-pfc /
   sun-135. Do not revive.
9. **Do not re-prime** the consumed mill list
   (hook-length / singleton-bound / cauchy-binet /
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
10. **No `Archive.*` import.**
11. **Leave OPE-403 alone.**

## Proof sketch (classical)

Level A: `n = 0` empty matrix. `n = 1` the
entry is `1`. A permutation matrix has a
single `1` in each row and column, hence is
DS. Convex combinations preserve
nonnegativity and both marginals, so
`conv(perm) ⊆ DS`. For `n = 2`, every DS
matrix is `[[a,1-a],[1-a,a]]` with
`0 ≤ a ≤ 1`, equal to `a • I + (1-a) • σ`.
**Not** labelled Birkhoff.

Level B: the positive support of a DS matrix
has a perfect matching (Hall); subtract a
scaled permutation matrix; induct on the
number of positive entries. Cap two levels.
No Gale–Ryser. No König re-proof.

## Canonical source (pin in this STATEMENT)

G. Birkhoff, *Three observations on linear
algebra*, Univ. Nac. Tucumán Rev. Ser. A 5
(1946) 147–151. J. von Neumann,
*A certain zero-sum two-person game
equivalent to the optimal assignment
problem*, Contributions to the theory of
games II (1953) 5–12. Textbook: Bhatia,
*Matrix Analysis*, or Brualdi–Ryser,
*Combinatorial Matrix Theory*. Compact form:
Wikipedia *Birkhoff–von Neumann theorem*.
Type pin: `Matrix` / `stdBasisMatrix` /
`convexHull`. Hall is a **different**
already-in theorem, used as glue.
Lattice Birkhoff is a **different**
already-in theorem.

## Out of scope

- Gale–Ryser / transportation polytopes as extra namesakes
- Birkhoff polytope volume / relative interior
- Permanent / van der Waerden conjecture (already different)
- Cauchy–Binet (#117) / Hadamard (#115) / LDL
- König matching / `konig_edge_chromatic` Level B
- Singleton (#120) / hook-length (#121) Level B
- Prize leftovers (krenn-gu / hou-zeng / sun-135)
- Novelty / external claim
