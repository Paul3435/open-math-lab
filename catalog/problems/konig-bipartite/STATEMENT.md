# Kőnig's theorem — bipartite matching number = vertex-cover number — formalize-only

**id:** `konig-bipartite`
**ticket:** OPE-574 Scout shortlist #2; OPE-580 Formalist Level A MERGED (PR #48); **OPE-591 Scout independently re-scored Level B as RECOMMENDED PRIME** (support OPE-590)
**expected:** known-classical (Kőnig 1931) — **no novelty claim**

## Why not classical / why formalize-only

Settled 1931 min-max theorem for bipartite graphs, not an open
problem. Mathlib v4.10.0 `Combinatorics/SimpleGraph/Matching.lean`
defines `Subgraph.IsMatching` / `IsPerfectMatching` and TODOs Tutte
and Hall (Hall already lives as set-family SDR in
`Combinatorics/Hall/`). It has **no** vertex-cover predicate and **no**
matching-number / cover-number equality. `Coloring.lean` has
`Colorable 2` and complete-bipartite bicoloring, which is the
bipartite pin. Hall's marriage theorem is a *different* statement
(systems of distinct representatives on `ι → Finset α`), already
upstream — this bet is the graph form `ν(G) = τ(G)` on `SimpleGraph`
matchings. Do not describe an attack as discovering Kőnig's theorem.

This is the **atomic** matching min-max. Finite Dilworth (chain
partition = width) was considered and not slotted: it still needs
this layer. Do not rubber-stamp Dilworth.

## Pinned convention (exact)

Let `G : SimpleGraph V` with `[Fintype V] [DecidableEq V] [DecidableRel G.Adj]`.

**Bipartite pin:** `G.Colorable 2` (Mathlib: nonempty `G.Coloring (Fin 2)`).

**Vertex cover (to be defined in ProofLab, not upstream):**

```text
def IsVertexCover (C : Finset V) : Prop :=
  ∀ ⦃u v⦄, G.Adj u v → u ∈ C ∨ v ∈ C
```

**Matching number / cover number:**

```text
def matchingNumber : ℕ :=
  sSup { M.edgeFinset.card | M : Subgraph G, M.IsMatching }

def vertexCoverNumber : ℕ :=
  sInf { C.card | C : Finset V, IsVertexCover C }
```

(Implementation may use `Finset.sup`/`inf` over a `Fintype` of
subgraphs, or an `∃ M, IsMatching ∧ ∀ C, IsVertexCover C → M.edgeFinset.card ≤ C.card`
plus a matching that meets some cover — avoid `sSup` on unbounded
`ℕ` if Lean infinities get in the way. The **claim** is the equality
of those two numbers.)

**Claim (Kőnig):**

```text
G.Colorable 2 → matchingNumber = vertexCoverNumber
```

equivalently: there exist a matching `M` and a vertex cover `C` with
`M.edgeFinset.card = C.card` (then max-matching ≤ min-cover is the
easy inequality for *every* graph).

**Encoding pin:** Mathlib `SimpleGraph.Subgraph.IsMatching` +
`Colorable 2`. Do not roll a custom bipartite-adjacency-matrix
matcher except as an optional tiny `K_{1,n}` sanity lemma.

**v1-b (stretch, same heartbeat only if cheap):** the easy inequality
`matchingNumber ≤ vertexCoverNumber` for *all* finite graphs (not
just bipartite). Not required for v1 if the bipartite equality lands.

## Landmines

1. **Bipartite is load-bearing.** `K_3`: matching number 1, vertex-cover
   number 2. Do not state `ν = τ` without `Colorable 2`.
2. **This is not Hall.** `Combinatorics/Hall/` is SDR for set families
   (`hall_hard_inductive`). A Formalist *may* reduce König to Hall via
   neighbourhoods; that is an allowed proof, not a reason to skip the
   graph statement. Do not cite `hall_hard_inductive` as König.
3. **This is not Kőnig's other theorem.** Edge-chromatic number of a
   bipartite graph equals `Δ` (also Kőnig) is **out of scope**. No
   `chromaticIndex` exists upstream anyway.
4. **This is not König's lemma** (infinite finitely branching trees).
   Finite graphs only.
5. **Matching number = number of *edges* in a maximum matching**, not
   `|M.verts|` (that is twice the matching number, already
   `IsMatching.even_card`). Vertex cover is a set of *vertices*.
6. **Empty graph / no edges:** both numbers 0; empty cover, empty
   matching. Isolated vertices do not change either number.
7. **Tutte** (perfect matchings, general graphs) is a Matching.lean
   TODO and **out of scope** — harder, not bipartite.
8. **Dilworth** is a poset corollary via comparability / split
   construction. Do **not** expand v1 into Dilworth.

## Proof sketch (classical)

Easy inequality (all graphs): every edge of a matching hits a cover
in a distinct vertex, so `ν ≤ τ`.

Hard inequality (bipartite): from a maximum matching, build a
minimum cover via alternating paths from unsaturated left vertices
(Berge / König construction), or reduce to Hall on the unmatched
neighbourhood. Either is human-scale.

Partial: **Level A LANDED** (OPE-580 / PR #48 MERGED, do not re-prime):
`IsVertexCover` + easy `ν ≤ τ` for all finite `G` + `konig_bot` /
`konig_completeBipartite` / `konig_star` + `complete_three_ne`
(`K_3`: `ν=1`, `τ=2`). **Level B remaining (OPE-591 RECOMMENDED
PRIME):** full `Colorable 2 → ν = τ` via alternating paths or Hall
reduction — a new proof layer, not a re-warm of the special cases.
Dilworth stays out of v1.

## Lean gate (when attacked)

- Target module: `proofs/lean-project/ProofLab/Konig.lean`
- Zero `sorry`; `lake env lean` exit 0
- Default **no claim**

## Canonical source

D. Kőnig, *Gráfok és mátrixok*, Matematikai és Fizikai Lapok **38**
(1931) 116–119. Textbook pin: Diestel / Bondy–Murty, König's theorem
(matching number = vertex-cover number in bipartite graphs). Type
pin: Mathlib `Subgraph.IsMatching` + `Colorable 2`.
