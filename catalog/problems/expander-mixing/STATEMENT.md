# Expander mixing lemma (formalize-only)

**id:** `expander-mixing`
**ticket:** OPE-870 Scout leftover slot #2 (Director OPE-869; post erdos-ramsey-lower #94 + zsigmondy-theorem #95)
**expected:** known-classical (Alon–Chung 1988 / folklore expander mixing; Alon–Spencer) — **no novelty claim**

## Why not classical / why formalize-only

Settled spectral graph theory: if `G` is a finite `d`-regular
simple graph on `n` vertices and `λ` is the largest
absolute value of an adjacency eigenvalue other than `d`,
then for all vertex-sets `S, T`

`|e(S,T) − (d/n) |S| |T|| ≤ λ √(|S| |T|)`.

Completely classical (Alon–Chung 1988; textbook Alon–Spencer
/ Hoory–Linial–Wigderson). Not an open problem. Not a
novelty claim.

**Not** Erdős first-moment Ramsey (consumed #94 namesake —
counting / union bound, a **different** theorem). **Not**
infinite Ramsey / `R(4,6)` / `ramseyUpper_add` existence
wrap. **Not** LLL-B / lopsided / Shearer / Moser–Tardos /
Azuma (consumed #85 leftover class). **Not** Friendship
windmill (consumed #40; Archive friendship uses adjMatrix
powers as a **different** theorem). **Not** Moore
degree–girth (consumed #76). **Not** Kirchhoff matrix-tree
(Cayley leftover; `lapMatrix` is the Laplacian, **not**
this adjacency mixing identity — never invent Kirchhoff
from this id). **Not** Wilf `χ ≤ 1+λ_max` (Cassini-class
given consumed greedy `χ ≤ Δ+1` plus Gershgorin
`λ_max ≤ Δ`, already Mathlib). **Not** Hoffman–Singleton
uniqueness / cages (Moore leftover class).

Mathlib v4.10.0 already has the **spectrum this theorem
needs**:

- `SimpleGraph.adjMatrix` / `isSymm_adjMatrix` /
  `IsRegularOfDegree` /
  `(adjMatrix *ᵥ const a) v = d * a` for `d`-regular
  (`Combinatorics/SimpleGraph/{AdjMatrix,Finite}.lean`)
- `Matrix.IsHermitian` / `IsHermitian.eigenvalues` /
  `eigenvectorBasis` / `spectral_theorem`
  (`LinearAlgebra/Matrix/Spectrum.lean`) — **already
  upstream. USE. Never cite as this gap.**
- Gershgorin / Rayleigh / `PosDef` — **already upstream.
  Different theorems.**
- Turán `isTuranMaximal_iff_nonempty_iso_turanGraph` —
  **negative control. Already upstream.**

There is **no** expander mixing lemma, **no** Alon–Chung
discrepancy bound, and **no** named
`|e(S,T) − (d/n)|S||T|| ≤ λ √(|S||T|)` anywhere under
`Mathlib/` or `Archive/` (word-regexp `expander` in
`Mathlib/Combinatorics` + `Archive` this run → ZERO
theorems; `mixing lemma` / `expanderMixing` → ZERO).
Do **not** import `Archive.*`.

OPE-853 considered-not-slotted did **not** slot this id.
Erdős–Ramsey #94 + Zsigmondy #95 are now **CONSUMED**.
This is a **fresh** spectral-graph leftover after an
algebra prime (`mason-stothers`), **not** a Ramsey
leftover, **not** a Friendship leftover, **not** a
Kirchhoff leftover, **not** a third slot.

Mill NOW: spectral graph theory leftover after a
polynomial-algebra prime (Mason–Stothers). `adjMatrix` +
`spectral_theorem` are waiting the same way
`exp_eq_tsum_div` waited for e-irrational after Descartes.
**Not a second combinatorics counting leftover after
Erdős–Ramsey.**

Do **not** describe an attack as discovering expanders.
Do **not** expand into Alon–Boppana / Cheeger /
Ramanujan graphs / LPS / Kirchhoff / matrix-tree.

## Pinned convention (exact)

**v1 is the d-regular undirected form.** Encoding: Mathlib
`SimpleGraph.adjMatrix ℝ` (Hermitian via `isSymm_adjMatrix`)
and `IsHermitian.eigenvalues`. `λ` is
`sup {|μ| : μ eigenvalue, μ ≠ d}` (the nontrivial
spectrum). `e(S,T)` counts ordered pairs `(s,t) ∈ S × T`
with `G.Adj s t` (so loops are absent; `s=t` never
contributes).

Suggested pin:

```text
-- Level A (not labelled expander): adjMatrix ℝ of a
-- d-regular graph is Hermitian; d is an eigenvalue on
-- the all-ones vector. Glue already upstream:
-- isSymm_adjMatrix, adjMatrix_mulVec for IsRegularOfDegree.
-- Remaining glue: the orthogonal complement of all-ones
-- is A-invariant, and λ bounds |⟨A x, y⟩| there.

-- Level B namesake
theorem expander_mixing {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
    (hreg : G.IsRegularOfDegree d)
    (hA : (G.adjMatrix ℝ).IsHermitian := by
      simpa using (isSymm_adjMatrix (G := G) (α := ℝ)))
    (λ : ℝ)
    (hλ : ∀ i, hA.eigenvalues i ≠ (d : ℝ) →
        |hA.eigenvalues i| ≤ λ)
    (S T : Finset V) :
    |(∑ s ∈ S, ∑ t ∈ T, (G.adjMatrix ℝ) s t)
        - (d * S.card * T.card : ℝ) / Fintype.card V|
      ≤ λ * Real.sqrt (S.card * T.card)
```

Empty `V` excluded by `d`-regular on a graph that has an
all-ones eigenvector (`n ≥ 1`). `n = Fintype.card V` in
the denominator is load-bearing. Non-regular graphs /
normalized Laplacian / directed expanders are **out of v1**.

**Level A may land only** Hermitian + eigenvalue `d` on
all-ones + `1^⊥` invariant, **not** labelled expander.
Use `spectral_theorem` / `adjMatrix_mulVec` — **do not
re-prove them**. **Level B** is the namesake mixing bound
via Cauchy–Schwarz on the spectral expansion of `1_S`.
Honest partial is allowed (comment residual, not `sorry`).

## Landmines

1. **Do not re-prove** `adjMatrix` / `isSymm_adjMatrix` /
   `IsRegularOfDegree` / `adjMatrix_mulVec` /
   `spectral_theorem` / `IsHermitian.eigenvalues` /
   Gershgorin / Rayleigh. Already Mathlib. Use them.
2. **This is not** Erdős–Ramsey lower (consumed #94).
   Counting first-moment ≠ spectral mixing.
3. **This is not** Friendship / Moore / Mycielski / KST /
   greedy / Brooks. Consumed, different theorems.
4. **This is not** Kirchhoff matrix-tree / Cayley `n^{n-2}`
   / Cauchy–Binet spanning-tree wrap. `lapMatrix` is
   **different** (Laplacian). Banned leftover class.
5. **This is not** Wilf `χ ≤ 1+λ_max` (Cassini-class:
   greedy + Gershgorin). Not Hoffman–Singleton / cages.
6. **This is not** LLL / Chernoff / Azuma / expander
   Chernoff. Probabilistic leftover class of consumed LLL.
7. **This is not** `mason-stothers` (the prime). Do **not**
   assign first unless Director swaps.
8. **Do not re-prime** the consumed mill list
   (erdos-ramsey-lower / zsigmondy-theorem /
   descartes-rule-of-signs / e-irrational /
   n-fold-inclusion-exclusion / wolstenholme-theorem /
   lovasz-local-lemma / korselt-carmichael / vosper /
   heron / euclid-euler / bipartite / moore / stirling /
   kst / pentagonal / sunflower / CNS / kk / oddtown /
   cayley / mycielski / friendship / havel / menger /
   greedy / Brooks / Dilworth / Eulerian / König / Dirac /
   EKR).
9. **No `Archive.*` import.**
10. **Leave OPE-403 alone.**

## Proof sketch (classical, d-regular)

Level A: `adjMatrix ℝ` is real symmetric hence Hermitian;
`IsRegularOfDegree d` gives `A 1 = d • 1` (upstream
`adjMatrix_mulVec`). The orthogonal complement of `1` is
invariant. **Not** labelled expander.

Level B: write `1_S = (|S|/n) 1 + f` with `f ⊥ 1`. Then
`e(S,T) = ⟨A 1_S, 1_T⟩ = (d/n)|S||T| + ⟨A f, g⟩` and
`|⟨A f, g⟩| ≤ λ ‖f‖ ‖g‖` by the spectral theorem on `1^⊥`.
Cauchy–Schwarz: `‖f‖ ≤ √|S|`. Cap two levels. No Cheeger.
No Kirchhoff.

## Canonical source (pin in this STATEMENT)

N. Alon, F. R. K. Chung, *Explicit construction of linear
sized tolerant networks*, Discrete Math. 72 (1988)
15–19. Compact textbook form: Alon–Spencer, *The
Probabilistic Method*, expander mixing lemma; Hoory–
Linial–Wigderson, Bull. AMS 43 (2006) §2. **v1 pins
d-regular undirected `|e(S,T)−(d/n)|S||T|| ≤ λ √(|S||T|)`,
λ = nontrivial spectral radius of `adjMatrix ℝ`.** Type
pin: `SimpleGraph.adjMatrix` + `IsHermitian.eigenvalues`.
`spectral_theorem` / Friendship / Moore / Kirchhoff /
Erdős–Ramsey are **different** statements, not this claim.

## Out of scope

- Non-regular / normalized Laplacian mixing
- Alon–Boppana / Ramanujan / LPS constructions
- Cheeger inequality
- Kirchhoff matrix-tree / Cauchy–Binet spanning trees
- Wilf / Hoffman chromatic bounds
- Friendship / Moore-C / cages / HS uniqueness
- LLL-B / Azuma / expander Chernoff
- Re-primes listed above
- Novelty / external claim
