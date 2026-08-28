# Friendship theorem (Erdős–Rényi–Sós) — formalize-only

**id:** `friendship-windmill`
**ticket:** OPE-533 Scout shortlist #2 (support OPE-475)
**expected:** known-classical (Erdős–Rényi–Sós 1966) — **no novelty claim**

## Why not classical / why formalize-only

Settled **1966** theorem about **finite** graphs. Informal slogan: if every
pair of people has exactly one common friend, then someone is friends with
everybody. Infinite graphs can fail the conclusion — we pin `Fintype`.
Mathlib v4.10.0 has `commonNeighbors` and `IsSRGWith` but **no** friendship
theorem. Do not describe an attack as discovering it.

## Pinned convention (exact)

Let `G : SimpleGraph V` with `[Fintype V] [DecidableEq V] [DecidableRel G.Adj]`
and `V` nonempty.

**Hypothesis (`IsFriendship G`):**

```text
∀ {v w : V}, v ≠ w → Fintype.card (G.commonNeighbors v w) = 1
```

Uses Mathlib `SimpleGraph.commonNeighbors` (intersection of neighbour sets).

**v1 claim (`exists_universal_friend`):**

```text
∃ u : V, G.degree u = Fintype.card V - 1
```

**v1-b (same heartbeat if cheap):** `G` is a Dutch windmill: the universal
vertex `u` plus `k` triangles that meet only at `u`.

**Encoding pin:** Mathlib `SimpleGraph`; do not roll a custom adjacency matrix
encoding unless using existing `AdjMatrix` lemmas.

## Landmines

1. **Finite only.** Infinite friendship graphs need not be windmills.
2. The `= 1` condition is for **every** distinct pair, adjacent or not.
3. `|V| ≤ 2` and empty-neighbour pathologies: dispatch at the statement edge,
   do not let them block the main argument.
4. Not Ramsey, not Turán, not a general SRG classification.
5. Prefer combinatorial counting (Huneke) over eigenvalues if either works.

## Proof sketch (classical)

- Windmill ⇒ hypothesis: each pair of leaves in the same triangle has the
  hub as unique common neighbour; leaves in different triangles have no
  shared edge-neighbour except the hub, etc.
- If some `u` has degree `n-1`, remaining edges form a matching on `V \ {u}`
  (each leaf has unique common neighbour with the hub = its triangle partner).
- If no universal vertex: one shows `G` is regular of degree `k ≥ 2`, hence
  `IsSRGWith n k 1 1`, hence `n = k^2 - k + 1`, then a counting/eigenvalue
  contradiction. Combinatorial Huneke avoids the spectrum.

## Lean gate (when attacked)

- Target module: `proofs/lean-project/ProofLab/Friendship.lean`
- Zero `sorry`; `lake env lean` exit 0
- Default **no claim**

## Canonical source

P. Erdős, A. Rényi, V. T. Sós, *On a problem of graph theory*,
Studia Sci. Math. Hungar. **1** (1966) 215–235.
C. Huneke, *The friendship theorem*, Amer. Math. Monthly **109** (2002) 192–194.
