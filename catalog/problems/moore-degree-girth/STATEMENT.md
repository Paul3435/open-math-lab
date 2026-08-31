# Moore degree–girth bound (formalize-only)

**id:** `moore-degree-girth`
**ticket:** OPE-754 Scout RECOMMENDED PRIME (support OPE-753; post KST #73 + pentagonal #74)
**expected:** known-classical (Moore / Hoffman–Singleton counting, 1960) — **no novelty claim**

## Why not classical / why formalize-only

Settled degree–girth counting bound: a finite graph with minimum
degree at least `k ≥ 2` and odd girth at least `2t+1` (equivalently
`2t+1 ≤ G.egirth`) satisfies

```text
n ≥ 1 + k · Σ_{i=0}^{t−1} (k − 1)^i.
```

Not an open problem. Cage numbers (the *minimum* `n` for given
`(k,g)`) and the existence of a 57-regular diameter-2 Moore graph
are **open / out of v1** — do not attack them; do not describe this
id as solving the cage problem or classifying Moore graphs.

Mathlib v4.10.0 already has the **graph this theorem needs**:

- `SimpleGraph.egirth` / `girth` (`Girth.lean`) — length of a shortest
  cycle, or `⊤` / `0` if acyclic
- `SimpleGraph.minDegree` / `maxDegree` / `degree` (`Finite.lean`)
- `SimpleGraph.dist` / `edist` (`Metric.lean`)
- `Walk.IsCycle` (`Walk.lean` / `Path.lean`)
- `neighborFinset` (`Finite.lean`)

There is **no** Moore-bound / cage / degree–girth extremal ident
anywhere under `Mathlib/` or `Archive/` (word-regexp this run →
ZERO files). ProofLab has Mycielski (triangle-free unbounded `χ`,
and a concrete `C5`), Friendship/windmill (unique common neighbour),
Kővári–Sós–Turán (bipartite `K_{s,t}`-free counting), greedy / Brooks
(chromatic vs `Δ`) — **different** theorems. This is **not** a
re-prime of those ids, **not** a Turán / Mantel leftover (clique-free
extremal is already upstream), **not** Hoffman–Singleton
classification.

Do **not** describe an attack as discovering the Moore bound.
Do **not** expand into even girth `g = 2t`, the degree–diameter
*upper* bound, cage tables, or uniqueness of Petersen / Hoffman–Singleton.

## Pinned convention (exact)

**Degree pin:** `k ≤ G.minDegree` with **`2 ≤ k` load-bearing** so
`k − 1` is the predecessor in `ℕ` and every vertex has at least two
neighbours (finite graphs with min-degree ≥ 2 are not trees).

**Girth pin:** use **`egirth`** (`ℕ∞`), not `girth` (junk `0` on
acyclic graphs). Hypothesis `2 * t + 1 ≤ G.egirth` with **`1 ≤ t`**.
v1 is **odd girth** only. Even girth `g = 2t` is a different unfolding
(two-sided tree) — stretch **out of v1**, not a leftover re-prime.

**v1 is the integer lower bound.** Equality cases (cycles `C_{2t+1}`,
Petersen, Hoffman–Singleton) are **comments, not theorems**. The
57-regular Moore graph is **open** — out of v1.

```text
theorem moore_bound_odd_girth
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k t : ℕ} (hk : 2 ≤ k) (ht : 1 ≤ t)
    (hδ : k ≤ G.minDegree)
    (hg : 2 * t + 1 ≤ G.egirth) :
    1 + k * ∑ i ∈ Finset.range t, (k - 1) ^ i ≤ Fintype.card V
```

**`2 ≤ k` is load-bearing** so `k - 1` is a predecessor in `ℕ`.
**`1 ≤ t` is load-bearing** so the sum is the interesting geometric
sum (`t = 0` is vacuous `n ≥ 1`).

## Landmines

1. **This is not Turán / Mantel.** Turán is already in
   `SimpleGraph/Turan.lean`. Never cite it as this gap (OPE-25
   negative control). Moore is degree–girth counting, not
   `K_{r+1}`-free max-edges.
2. **This is not the cage problem.** Exact cage numbers `n(k,g)`
   are open for most parameters. Formalizing the classical lower
   bound is not a novelty claim and not a “near-miss” at cages.
3. **This is not Hoffman–Singleton classification** (cycles,
   Petersen, HS, maybe 57-regular). The 57-regular existence
   question is **open**. Out of v1.
4. **This is not Friendship / windmill** (`ProofLab/Friendship.lean`,
   PR #40). Friendship is “every two vertices have a unique common
   neighbour.” Moore is a BFS size bound from `minDegree` + `egirth`.
5. **This is not Mycielski** (`ProofLab/Mycielski.lean`, PR #65).
   Mycielski is unbounded `χ` with `CliqueFree 3`. `C5` may be reused
   as a *tightness comment* for `k = 2, t = 2` (`n ≥ 5`), **not**
   labelled Moore.
6. **This is not Kővári–Sós–Turán** (consumed PR #73). KST is
   bipartite forbidden `K_{s,t}`. Girth ≥ 5 forbids `C3` and `C4`
   globally — different statement.
7. **This is not the degree–diameter upper bound**
   `n ≤ 1 + Δ Σ (Δ−1)^i`. Dual counting; out of v1 this id.
8. **Even girth `g = 2t` is out of v1.** Do not invent
   moore-C / even-girth / cages as a leftover.
9. **Do not re-prime** kovari-sos-turan / pentagonal-number-theorem /
   sunflower-erdos-rado / combinatorial-nullstellensatz /
   kruskal-katona / oddtown / cayley-trees / mycielski-triangle-free /
   friendship-windmill / havel-hakimi / menger-vertex / greedy /
   Brooks A/B / Dilworth / Eulerian / König / Dirac.
10. **No `Archive.*` import.**
11. **Leave OPE-403 alone.**

## Proof sketch (classical, BFS / Moore)

Level A: `t = 1` (girth ≥ 3) gives `n ≥ 1 + k`, which is the star
bound `card V ≥ 1 + minDegree` (glue, **not** labelled Moore).
`k = 2, t = 2` (min-degree ≥ 2, girth ≥ 5) gives `n ≥ 5`; `C5`
saturates (ProofLab Mycielski already has `C5`, **not** labelled
Moore). `k = 3, t = 2` gives `n ≥ 10` (Petersen tightness is a
**comment**, not a uniqueness theorem). Empty / edgeless landmines:
`minDegree = 0` is excluded by `2 ≤ k`.

Level B: namesake `moore_bound_odd_girth`. Fix a vertex `u`. Walks
of length `≤ t` starting at `u` cannot close or collide
(any collision yields a cycle of length `≤ 2t < 2t+1 ≤ egirth`).
Branching at least `k` at `u` and at least `k−1` thereafter, the
closed ball of radius `t` therefore has at least
`1 + k Σ_{i<t} (k−1)^i` vertices.

Cap two levels. No even girth, no diameter upper bound, no cage
tables, no Hoffman–Singleton uniqueness.

## Canonical source (pin in this STATEMENT)

A. J. Hoffman and R. R. Singleton, *On Moore graphs with diameters 2
and 3*, IBM Journal of Research and Development **4** (1960) 497–504
(diameter-2 counting; equality classification is **not** v1).
Elementary degree–girth form: N. L. Biggs, *Algebraic Graph Theory*
(2nd ed., Cambridge 1993), §23; Diestel, *Graph Theory*, the standard
BFS unfolding. Type pin: `SimpleGraph` + `minDegree` + `egirth`.
Cages / Hoffman–Singleton uniqueness / 57-regular existence / even
girth / Turán / Friendship / Mycielski / KST are different
statements, not this claim.

## Out of scope

- Exact cages `n(k,g)` and `(k,g)`-cage uniqueness
- 57-regular Moore graph (open)
- Even girth; degree–diameter upper bound
- Turán / Mantel / Erdős–Stone / KST / Friendship / Mycielski
- Planar / five-colour / Vizing / 4CT
- Re-primes listed above
- Novelty / external claim
