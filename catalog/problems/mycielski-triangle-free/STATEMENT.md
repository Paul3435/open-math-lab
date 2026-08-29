# Mycielski — triangle-free graphs of arbitrarily high χ (formalize-only)

**id:** `mycielski-triangle-free`
**ticket:** OPE-683 Scout shortlist #2 (support OPE-682; post havel-hakimi #61 + menger-vertex #62)
**expected:** known-classical (Mycielski 1955) — **no novelty claim**

## Why not classical / why formalize-only

Settled existence: there are triangle-free finite simple graphs of
arbitrarily large chromatic number. Not an open problem. Mathlib v4.10.0
already has `CliqueFree`, `Colorable`, `chromaticNumber`, and
`Walk.three_le_chromaticNumber_of_odd_loop` (odd closed walks force
`χ ≥ 3`). There is **no** `Mycielski` construction and **no** theorem
that triangle-free graphs have unbounded chromatic number anywhere under
`Mathlib/` or `Archive/` (word-regexp this run → ZERO).

This is **not** a re-prime of greedy-chromatic, Brooks A/B (including
namesake Kempe / list-colouring / Level C), havel-hakimi, menger-vertex,
Dilworth, Eulerian, König, or Dirac. It is a **new proof layer**:
`χ` versus clique number (`ω ≤ 2`), on colouring predicates that already
exist. Brooks is `χ` versus `Δ`. Different theorem.

Fresh id — never previously shortlisted. Do **not** describe an attack as
discovering Mycielski. Do **not** expand into Grötzsch (triangle-free
planar `χ ≤ 3`), Hajós, Kneser, Vizing, or 4CT/5CT.

## Pinned convention (exact)

**Triangle-free pin:** `G.CliqueFree 3` (no `IsNClique 3`).

**Unbounded chromatic number, finite, labelled `Fin n`:**

```text
theorem mycielski_unbounded (k : ℕ) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
      G.CliqueFree 3 ∧ ¬ G.Colorable k
```

Equivalently (same heartbeat, not a second theorem): `k ≤ G.chromaticNumber`
in `ℕ∞`, but the `¬ Colorable k` form is the Lean-native pin.

**Mycielski graph (Level B engine):** given finite `G : SimpleGraph V`,
the Mycielski graph `μ(G)` has vertex set `V ⊕ V ⊕ Unit` (a copy of `V`,
a shadow copy, and one extra vertex `u`):

- keep all edges of `G` on the first copy;
- join each shadow `v'` to the neighbours of `v` in the first copy
  (not to `v` itself);
- join `u` to every shadow vertex.

**Named facts (classical, Mycielski 1955):** if `G` is triangle-free then
so is `μ(G)`; if `G` is not `k`-colourable then `μ(G)` is not
`(k+1)`-colourable. Iterate from `K_2` (or from `C5 = μ(K_2)`).

**v1 is the existence theorem.** The construction is the engine, not a
separate id. Do not require a bundled `MycielskiGraph` API beyond what
the proof needs.

## Landmines

1. **`CliqueFree 3`, not `CliqueFree 2`.** `CliqueFree 2` is edgeless.
   Triangles are 3-cliques.
2. **This is not Brooks.** Brooks is `χ ≤ Δ` except `⊤` / odd cycles.
   Mycielski graphs have `Δ` growing with `χ`; they are not a Brooks
   leftover and must not be labelled as one.
3. **This is not greedy `χ ≤ Δ+1`.** Reuse of `Colorable` is fine; do
   not cite `greedy_colorable` as Mycielski.
4. **This is not Grötzsch** (triangle-free *planar* `χ ≤ 3`). No planar
   defs in the pin. Out of v1.
5. **This is not Hajós construction, not Kneser `χ(KG_{n,k}) = n-2k+2`,
   not Vizing, not 4CT/5CT, not list-colouring Brooks.**
6. **Odd-cycle glue is already upstream.**
   `Walk.three_le_chromaticNumber_of_odd_loop` gives `C5` / odd cycles
   `χ ≥ 3`. Level A may *use* that; do not re-prove it and do not call
   it Mycielski.
7. **Finite only.** Infinite Mycielski / shift graphs out of scope.
8. **Vertex-set encoding is load-bearing.** `V ⊕ V ⊕ Unit` (or an
   isomorphic `Fin` copy) — do not silently identify the two copies.
9. **Do not re-prime greedy / Brooks A/B / havel-hakimi / menger-vertex /
   Dilworth / Eulerian / König / Dirac.**
10. **No `Archive.*` import.**

## Proof sketch (classical, Mycielski 1955)

Level A: the 5-cycle is triangle-free and not 2-colourable (odd closed
walk; Mathlib `three_le_chromaticNumber_of_odd_loop`). This gives `k ≤ 2`.

Level B: starting from `K_2` (or from that `C5`), iterate `μ`. Triangle-
freeness: a triangle cannot use `u` (shadows are independent) and cannot
live in one copy; the remaining cases reduce to a triangle or a loop in
`G`. Chromatic bump: a `(k+1)`-colouring of `μ(G)` restricts, after
recolouring the extra vertex's class, to a `k`-colouring of `G`.

Partial: **Level A** `C5` (or odd cycle) triangle-free + `¬ Colorable 2`,
zero sorry, reusing the odd-loop lemma not labelled Mycielski.
**Level B** namesake `mycielski_unbounded` by iterating `μ`. Cap two
levels. No Grötzsch / Hajós / Kneser / Vizing / 4CT.

## Lean gate (when attacked)

- Target module: `proofs/lean-project/ProofLab/Mycielski.lean`
- Reuse Mathlib `CliqueFree`, `Colorable`, `chromaticNumber`,
  `Walk.three_le_chromaticNumber_of_odd_loop`. Do **not** re-prove
  greedy / Brooks / Havel / Menger / König / Dirac / Eulerian / Dilworth.
- Zero `sorry`; `lake env lean` exit 0
- Default **no claim**
- Do not import `Archive.*`

## Canonical source

J. Mycielski, *Sur le coloriage des graphes*, Colloquium Mathematicum **3**
(1955) 161–162. Textbook pin: Diestel, *Graph Theory*, Mycielski
construction / triangle-free graphs of large chromatic number; or Bondy–
Murty, *Graph Theory*, §14.2. Type pin: Mathlib `CliqueFree 3` +
`Colorable`. Grötzsch, Hajós, Kneser, Vizing, and 4CT are **different**
theorems, not this claim.
