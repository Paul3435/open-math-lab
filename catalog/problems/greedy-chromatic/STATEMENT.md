# Greedy colouring — χ ≤ Δ+1 (finite simple graphs) — formalize-only

**id:** `greedy-chromatic`
**ticket:** OPE-640 Scout recommended prime (support OPE-639; post Dilworth #53+#54 + Eulerian trail #55)
**expected:** known-classical (folklore / Diestel; greedy algorithm) — **no novelty claim**

## Why not classical / why formalize-only

Settled undergraduate bound: every finite simple graph is
(Δ+1)-colourable. Not an open problem. Mathlib v4.10.0 already has
`SimpleGraph.Colorable`, `Coloring`, `chromaticNumber`, and
`maxDegree`. There is **no** `chromaticNumber ≤ maxDegree + 1`, **no**
`Colorable (maxDegree + 1)`, **no** greedy colouring construction, and
**no** Brooks theorem (word-regexp `brooks` → ZERO Mathlib+Archive this
run). Coloring.lean's TODO is trees / planar / chromatic polynomials /
partial colourings — not this bound.

This is **not** a re-prime of König (`Colorable 2` is a bipartite
hypothesis, not a degree bound), Dirac (Hamiltonian), Eulerian, or
Dilworth. It is a **new proof layer**: the first degree-chromatic
inequality on infra that already exists. Do not describe an attack as
discovering the greedy bound.

Brooks (`χ ≤ Δ` except complete graphs and odd cycles) is a
**different named theorem** (shortlist #2 `brooks-coloring`). Do **not**
prove Brooks in this id. Do **not** call greedy "Brooks".

## Pinned convention (exact)

Let `V` be a finite type with `[Fintype V] [DecidableEq V]` and
`G : SimpleGraph V` with `[DecidableRel G.Adj]`.

**Claim (greedy / Δ+1 bound):**

```text
theorem greedy_colorable :
    G.Colorable (G.maxDegree + 1)
```

equivalently (follows from `Colorable.chromaticNumber_le`):

```text
G.chromaticNumber ≤ G.maxDegree + 1
```

**v1 is the `Colorable` form.** The `chromaticNumber` form is the same
heartbeat if cheap (one-liner), not a second theorem.

**Encoding pin:** Mathlib `SimpleGraph.Coloring` / `Colorable` /
`maxDegree`. Construct a colouring with `Coloring.mk` (or
`Colorable.toColoring`) on `Fin (G.maxDegree + 1)`. Do **not** roll a
custom colour type. Do **not** import `Archive.*`.

**v1-b (stretch, same heartbeat only if cheap):** the bound is tight on
`⊤` (`chromaticNumber_top` already gives χ = |V| = Δ+1 for complete
graphs). Not required. **Brooks is out of this id.**

## Landmines

1. **Finite is load-bearing.** `maxDegree` needs `Fintype V`. Infinite
   colouring theory is out of scope.
2. **`DecidableRel G.Adj` is required** for `degree` / `maxDegree`.
3. **This is not Brooks.** Brooks is `χ ≤ Δ` with complete / odd-cycle
   exceptions. Greedy always uses Δ+1 colours; equality holds on `K_n`
   and odd cycles. Swapping them is the classic off-by-one bug.
4. **This is not Vizing.** Vizing is *edge*-chromatic `χ' ≤ Δ+1`.
   Mathlib has no edge-colouring API. Do not invent one.
5. **This is not four-colour / five-colour.** Those need planarity.
   Coloring.lean lists planar graphs as a TODO; there is no planarity
   predicate. Out of scope.
6. **`chromaticNumber` is `ℕ∞`.** State `Colorable (maxDegree + 1)`
   first; only then cast. Empty graph: `maxDegree = 0`, `Colorable 1`
   (also `Colorable 0` via `colorable_of_isEmpty` — both OK; do not
   claim `Colorable 0` for nonempty graphs).
7. **Vertex order is arbitrary.** Welsh–Powell (degree-descending) is
   a heuristic refinement, not the theorem. Any order works for Δ+1.
8. **Do not expand v1 into Brooks, greedy list-colouring, or
   choice-number bounds.**

## Proof sketch (classical, greedy / induction)

Induct on `Fintype.card V`. Delete a vertex `v`. The induced subgraph
on the remainder has `maxDegree ≤ G.maxDegree`, so by IH it is
`(G.maxDegree + 1)`-colourable. Vertex `v` has `degree v ≤ maxDegree`
neighbours, which use at most `maxDegree` colours, so one colour in
`Fin (maxDegree + 1)` remains. Reassemble with `Coloring.mk`.

Partial: **Level A** empty / edgeless (`maxDegree = 0`) / complete
(`⊤`, reuse `chromaticNumber_top`) / `card = 1` specials, plus the
easy `degree_le_maxDegree` glue. **Level B** namesake
`greedy_colorable` by induction (or explicit greedy along a list of
vertices). Cap two levels. No Brooks.

## Lean gate (when attacked)

- Target module: `proofs/lean-project/ProofLab/GreedyChromatic.lean`
- Reuse Mathlib `Colorable`, `Coloring.valid`, `maxDegree`,
  `degree_le_maxDegree`, `chromaticNumber_top`. Do **not** re-prove
  König / Dirac / Eulerian / Dilworth.
- Zero `sorry`; `lake env lean` exit 0
- Default **no claim**
- Do not import `Archive.*`

## Canonical source

Textbook pin: Reinhard Diestel, *Graph Theory*, GTM (any recent ed.),
the corollary that every graph is (Δ+1)-colourable (stated immediately
before Brooks). Constructive pin: greedy colouring along an arbitrary
vertex order. Degree-order refinement (not required): D. J. A. Welsh
and M. B. Powell, *An upper bound for the chromatic number of a graph
and its application to timetabling problems*, Comput. J. **10** (1967)
85–86. Type pin: Mathlib `SimpleGraph.Colorable` + `maxDegree`.
Brooks 1941 is the **next** theorem, catalog id `brooks-coloring`, not
this claim.
