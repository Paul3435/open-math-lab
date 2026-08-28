# Dirac's theorem (min-degree Hamiltonian cycle) — formalize-only

**id:** `dirac-hamiltonian`
**ticket:** OPE-553 Scout shortlist #2 (support OPE-552)
**expected:** known-classical (Dirac 1952) — **no novelty claim**

## Why not classical / why formalize-only

Settled 1952 sufficient condition for Hamiltonian cycles, not an open
problem. Mathlib v4.10.0 already has `SimpleGraph.Walk.IsHamiltonian`,
`Walk.IsHamiltonianCycle`, and `SimpleGraph.IsHamiltonian` (a graph that
**contains** a Hamiltonian cycle; singleton convention in the def) but
**no** degree sufficient-condition theorem (no Dirac, no Ore). Graph
`dirac` hits in the pin are Dirac **measures** / analysis, not this
theorem. Do not describe an attack as discovering Dirac's theorem.

## Pinned convention (exact)

Let `G : SimpleGraph V` with `[Fintype V] [DecidableEq V] [DecidableRel G.Adj]`.
Write `n := Fintype.card V` and `δ G := min degree` (Mathlib
`SimpleGraph.minDegree` if present, else `Finset.univ.inf' … G.degree`).

**Hypotheses:** `3 ≤ n` and `n ≤ 2 * G.minDegree` (i.e. `δ(G) ≥ n/2` in
integers: `G.minDegree * 2 ≥ n`).

**Claim (Dirac):**

```text
G.IsHamiltonian
```

using Mathlib's existing `SimpleGraph.IsHamiltonian`
(exists a Hamiltonian cycle, with the library's n=1 convention unused
because we assume `n ≥ 3`).

**Encoding pin:** Mathlib `SimpleGraph` + `Walk`. Do not roll a custom
adjacency-matrix Hamiltonian checker except as an optional tiny `n=3`
sanity lemma.

**v1-b (stretch, same heartbeat only if cheap):** Ore's theorem
(`∀ {u v}, ¬ Adj u v → degree u + degree v ≥ n` ⇒ Hamiltonian). Dirac
is the corollary `δ ≥ n/2`. Ore is **not** required for v1.

## Landmines

1. **`n ≥ 3` is load-bearing.** `K_2` has `δ = 1 ≥ 2/2` and is not
   Hamiltonian (no cycle). Do not state Dirac without `n ≥ 3`.
2. Mathlib `IsHamiltonian` treats the **singleton** as Hamiltonian by
   convention (`card ≠ 1 → ∃ cycle`). That clause is irrelevant under
   `n ≥ 3`; do not “prove Dirac” by dispatching n=1.
3. **Cycle, not path.** Dirac's theorem as pinned is Hamiltonian
   *cycle*. A longest-path lemma is an internal tool, not the claim.
   Directed Dirac / Ore for digraphs are out of scope.
4. **Simple undirected.** No loops/multiedges; `SimpleGraph` already.
5. Completeness `⊤` is the trivial case (`δ = n-1 ≥ n/2` for `n ≥ 2`);
   prove it as a lemma, not as the theorem.
6. `minDegree` vs average degree vs `n/2` rounding: pin the inequality
   `2 * minDegree ≥ n` (integer; equivalent to `δ ≥ n/2` for even n and
   the usual ceiling-free form).

## Proof sketch (classical)

Longest-path / longest-cycle argument:

- `δ ≥ n/2` and `n ≥ 3` ⇒ G connected (a component of size `≤ n/2`
  cannot meet the degree bound).
- Let `P` be a longest path, endpoints `u,v`. Then `N(u), N(v) ⊆ V(P)`,
  and non-edges `u—v` would extend, so the neighbourhoods on `P` force
  an index where `u` meets `x_{i+1}` and `v` meets `x_i`, closing a
  cycle through `V(P)`.
- That cycle is spanning: a vertex off the cycle adjacent to it would
  yield a longer path.

Partial: Level A `n=3` + complete graphs + connectedness from `δ`.
Level B longest-path closing.

## Lean gate (when attacked)

- Target module: `proofs/lean-project/ProofLab/Dirac.lean`
- Zero `sorry`; `lake env lean` exit 0
- Default **no claim**

## Canonical source

G. A. Dirac, *Some theorems on abstract graphs*, Proc. London Math.
Soc. (3) **2** (1952) 69–81. Textbook pin: Bondy–Murty / Diestel,
standard longest-path proof of Dirac's theorem.
