# Menger — vertex form (finite simple graphs) — formalize-only

**id:** `menger-vertex`
**ticket:** OPE-666 Scout shortlist #2 (support OPE-665; post greedy #57 + Brooks A #58 + Brooks B #59)
**expected:** known-classical (Menger 1927) — **no novelty claim**

## Why not classical / why formalize-only

Settled 1927 min-max: in a finite graph the minimum number of vertices
separating `A` from `B` equals the maximum number of pairwise
vertex-disjoint `A`–`B` paths. Not an open problem. Mathlib v4.10.0
already has `Walk`, `Walk.support`, `Reachable`, `Connected`, and
`IsPath`. There is **no** Menger theorem, **no** `IsSeparator` /
`vertexCut` / `internallyDisjoint` predicate anywhere under
`Mathlib/` or `Archive/` (word-regexp `Menger` / `menger` this run →
ZERO; `IsSeparator` hits are category-theory detectors, not graphs).

This is **not** a re-prime of König (`ν=τ` for matchings), Dilworth
(chain partitions), greedy, Brooks, Eulerian, or Dirac. It is a **new
proof layer**: connectivity min-max. Independent re-score of the
OPE-640 considered-not-slotted Menger line — last Scout benched it
because the slot cap was used by colouring defs that already existed;
greedy + Brooks A/B are now **consumed** on merged main. Gap still
holds. Named human-scale proof: Diestel induction on `|E|`. König
reduction on a split graph is an *optional engine*, not the claim, and
**not** a König leftover rubber-stamp.

Do **not** assign this id before `havel-hakimi` unless Director swaps.
Do **not** prove edge-Menger / max-flow / infinite Erdős–Menger.

## Pinned convention (exact)

Let `V` be a finite type with `[Fintype V] [DecidableEq V]` and
`G : SimpleGraph V` with `[DecidableRel G.Adj]`. Let `A B : Set V`.

**A–B path (Diestel):** a path whose first vertex lies in `A`, last
vertex lies in `B`, and no *internal* vertex lies in `A ∪ B`.

**Vertex-disjoint:** pairwise no common vertices (including ends).
Trivial one-vertex paths from `A ∩ B` are allowed and are pairwise
disjoint when they use distinct vertices of `A ∩ B`.

**Separator:** `S ⊆ V` *separates* `A` from `B` when every `A`–`B`
path meets `S`. (In particular `A ∩ B ⊆ S` for every separator.)

**Claim (Menger, vertex, finite):**

```text
theorem menger_vertex (A B : Set V) :
    s G A B = p G A B
```

where `s G A B` is the minimum cardinality of an `A`–`B` separator
and `p G A B` is the maximum number of pairwise vertex-disjoint
`A`–`B` paths (both `ℕ`; finite graph ⇒ finite).

**v1 is this global A–B form** (Diestel 3.3.1 flavour). The local
form “non-adjacent `u,v`: local connectivity `κ(u,v)` equals the max
number of internally vertex-disjoint `u`–`v` paths” is the same
heartbeat if cheap (set `A = N(u)`, `B = N(v)` or the usual
reduction), not a second theorem and **not** required.

**Encoding pin:** Mathlib `Walk` / `IsPath` / `Walk.support` /
`Reachable`. Define ProofLab `IsABSeparator` and `IsABPath`; do **not**
claim a missing Mathlib constructor as the gap. Do **not** import
`Archive.*`.

## Landmines

1. **Finite is load-bearing.** Infinite Menger / Erdős's conjecture
   is out of scope (and is a different, harder theorem).
2. **`A ∩ B` is load-bearing.** Vertices in the intersection lie on
   every separator and give trivial paths. Dropping them falsifies
   the equality.
3. **Disjoint vs internally disjoint.** For the *local* `u`–`v` form
   the paths share `u` and `v` and must be internally disjoint. For
   the *global* `A`–`B` form the paths are fully vertex-disjoint.
   Mixing the two is the classic off-by-ends bug. **v1 is global.**
4. **This is not König `ν=τ`.** Matchings are not `A`–`B` paths.
   ProofLab `konig_bipartite` may be used as an *engine* on an
   auxiliary graph; do not cite it as Menger and do not re-prime
   `konig-bipartite`.
5. **This is not edge-Menger, not max-flow min-cut, not Menger for
   digraphs.** No flow API in the pin. Edge-separators are a stretch
   only if cheap after vertex-Menger lands.
6. **This is not Tutte, not Whitney `κ ≤ λ ≤ δ`, not 4CT/5CT.**
7. **Walk-induction is the budget sink.** Name Diestel's `|E|`
   induction (or a König reduction) in the first Formalist heartbeat
   or stop. Do not brute-force path sets.
8. **Do not re-prime greedy / Brooks A/B / Dilworth / Eulerian /
   Dirac / König.** Do not invent namesake Kempe as a leftover.

## Proof sketch (classical, Menger 1927 / Diestel)

Easy inequality: `p ≤ s` because a separator meets every path.
Reverse: induct on `card G.edgeFinset`. If some separator of size
`s` is not `A` or `B`, split `G` along that separator and apply IH
to the two sides; glue. If every minimum separator is `A` or `B`,
an edge between the `A`-side and the `B`-side can be deleted and
the IH plus a last-edge extension recovers `s` disjoint paths.

Partial: **Level A** `A ∩ B` nonempty (trivial paths); `A`, `B`
singletons joined by an edge; empty / disconnected (`p = s = 0`
when no `A`–`B` path and `A ∩ B = ∅`); plus the easy `p ≤ s`.
**Level B** namesake `menger_vertex`. Cap two levels. No
edge-Menger / no flows / no infinite.

## Lean gate (when attacked)

- Target module: `proofs/lean-project/ProofLab/Menger.lean`
- Reuse Mathlib `Walk`, `IsPath`, `Reachable`, `Connected`. Optional
  engine: `ProofLab.Konig.konig_bipartite` on an auxiliary bipartite
  graph — do **not** re-prove König. Do **not** re-prove Dilworth /
  greedy / Brooks.
- Zero `sorry`; `lake env lean` exit 0
- Default **no claim**
- Do not import `Archive.*`

## Canonical source

K. Menger, *Zur allgemeinen Kurventheorie*, Fundamenta Mathematicae
**10** (1927) 96–115. Textbook pin: Reinhard Diestel, *Graph Theory*,
Menger's theorem (global form: min vertices separating `A` from `B`
equals max number of pairwise disjoint `A`–`B` paths). Type pin:
Mathlib `SimpleGraph.Walk` / `IsPath` / `Walk.support`. Edge-Menger
and max-flow min-cut are **different** theorems, not this claim.
