# Bipartite ⇔ no odd closed walk (formalize-only)

**id:** `bipartite-odd-cycle`
**ticket:** OPE-770 Scout RECOMMENDED PRIME (support OPE-769; post Moore #76 + Stirling #77)
**expected:** known-classical (König 1916 / Diestel Prop. 1.6.1) — **no novelty claim**

## Why not classical / why formalize-only

Settled graph-theory characterization: a finite simple graph is
2-colourable if and only if it has no closed walk of odd length
(equivalently: no odd cycle). Not an open problem.

Mathlib v4.10.0 already has the **graph this theorem needs**:

- `SimpleGraph.Colorable` / `chromaticNumber` (`Coloring.lean`)
- `Walk` / `Reachable` / `Preconnected` (`Walk.lean` / `Path.lean`)
- `Walk.three_le_chromaticNumber_of_odd_loop` (`ConcreteColorings.lean`)
  — odd closed walk ⇒ `3 ≤ χ` (one direction as glue, **not**
  labelled the namesake)
- `Coloring.odd_length_iff_not_congr` — parity of walk length vs
  Bool-colours
- `completeBipartiteGraph.chromaticNumber = 2` and
  `pathGraph.bicoloring` — **special cases**, already upstream,
  **not** this theorem
- `dist` / `edist` (`Metric.lean`) — optional engine for the
  hard direction (BFS parity)

There is **no** `IsBipartite` predicate, **no**
`colorable_two_iff_no_odd_walk`, and **no** general 2-colouring
construction from the odd-walk obstruction anywhere under
`Mathlib/` or `Archive/` (word-regexp this run → ZERO files).
ProofLab has greedy `χ ≤ Δ+1`, Brooks `Δ ≤ 2` family (2-regular
odd-order `IsOddCycle` exception), König `Colorable 2 → ν = τ`,
Mycielski unbounded-`χ` (and a concrete `C5` odd-loop glue) —
**different** theorems. This is **not** a re-prime of those ids,
**not** Brooks-C / Kempe, **not** list-colouring, **not** Vizing,
**not** 4CT / five-colour / planar, **not** König `ν = τ`.

Do **not** describe an attack as discovering bipartite graphs.
Do **not** expand into list-colouring, Brooks namesake, planar
5-colour, or König edge-chromatic `χ' = Δ`.

## Pinned convention (exact)

**v1 is finite graphs only.** Infinite 2-colourability needs
choice / compactness — out of v1.

**Walk pin, not a separate `IsCycle` pin.** Match Mathlib glue
`three_le_chromaticNumber_of_odd_loop`, which takes an odd-length
*closed `Walk`*. In simple graphs a closed odd walk contains an
odd cycle; do not prove that equivalence as a second namesake.

**Bipartite encoding is `Colorable 2`**, not a new `IsBipartite`
structure. This matches ProofLab König (`Colorable 2 → ν = τ`)
and Mathlib complete-bipartite bicoloring.

```text
theorem colorable_two_iff_no_odd_walk
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.Colorable 2 ↔ ∀ ⦃u : V⦄ (p : G.Walk u u), ¬ Odd p.length
```

Components are independent: the namesake is **global** (every
component 2-coloured). Level A may assume `Preconnected` and
lift.

## Landmines

1. **This is not König `ν = τ`.** Consumed PRs **#48 / #50**
   (`ProofLab/Konig.lean`). König *assumes* `Colorable 2`. This
   theorem *characterizes* `Colorable 2`. Different statement.
2. **This is not Brooks.** Consumed PRs **#58 / #59**. Brooks
   `Δ ≤ 2` uses `IsOddCycle` as a 2-regular odd-order exception.
   This theorem has **no** `Δ` bound and applies to trees,
   grids, `K_{n,n}`, etc. Do **not** invent namesake Kempe /
   Brooks-C / list-colouring Brooks.
3. **This is not greedy `χ ≤ Δ+1`.** Consumed PR **#57**.
4. **This is not Mycielski.** Consumed PR **#65**. `C5` may be
   reused as a *landmine comment* (`¬ Colorable 2` via odd loop),
   **not** labelled this namesake.
5. **This is not the already-upstream special cases.**
   `completeBipartiteGraph.chromaticNumber = 2` and
   `pathGraph.bicoloring` are Mathlib. Glue, not labelled
   namesake. Never cite them as this gap.
6. **This is not Vizing / 4CT / five-colour / planar.** ZERO
   `chromaticIndex` / planar defs. Coloring.lean TODOs stay
   benched. Do **not** invent König `χ' = Δ`.
7. **`K_3` is the load-bearing negative.** Odd closed walk of
   length 3 ⇒ `¬ Colorable 2` (König already uses `K_3` as the
   matching landmine — same graph, different theorem).
8. **Do not re-prime** moore-degree-girth / stirling-second-kind /
   kovari-sos-turan / pentagonal-number-theorem / sunflower /
   combinatorial-nullstellensatz / kruskal-katona / oddtown /
   cayley-trees / mycielski-triangle-free / friendship-windmill /
   havel-hakimi / menger-vertex / greedy / Brooks A/B / Dilworth /
   Eulerian / König / Dirac / EKR.
9. **No `Archive.*` import.**
10. **Leave OPE-403 alone.**

## Proof sketch (classical, Diestel 1.6.1)

Level A: easy direction `Colorable 2 → no odd closed walk` via
contrapositive of `three_le_chromaticNumber_of_odd_loop` (**not**
labelled namesake). Empty / edgeless are `Colorable 2`. `K_2`
and even cycle `C_4` are `Colorable 2`. `K_3` landmine. **Not**
labelled the namesake.

Level B: namesake `colorable_two_iff_no_odd_walk`. Hard
direction: on each connected component pick a root; colour `v`
by the parity of `dist root v` (or of any `Walk`). Well-defined
because two walks of different parity would concatenate to an
odd closed walk. Adjacent vertices have opposite parity
(otherwise a length-1 edge plus two even/odd walks yields an
odd closed walk). Cap two levels. No list-colouring, no Brooks
namesake, no planar, no edge-colouring.

## Canonical source (pin in this STATEMENT)

Dénes König, *Über Graphen und ihre Anwendung auf
Determinantentheorie und Mengenlehre*, Math. Ann. **77** (1916)
453–465 (early bipartite / 2-colour form). Textbook pin:
Reinhard Diestel, *Graph Theory*, 5th ed., Springer GTM 173,
2017, Proposition 1.6.1 (a graph is bipartite iff it contains
no odd cycle). Type pin: finite `SimpleGraph` + `Colorable 2` +
odd-length closed `Walk`. König `ν = τ`, Brooks, greedy,
Mycielski, Vizing, 4CT, and complete-bipartite / path special
cases are different statements, not this claim.

## Out of scope

- Infinite graphs / compactness 2-colourability
- List-colouring / choice number
- Brooks namesake (Kempe / Lovász) / Brooks-C
- Vizing / König `χ' = Δ` / 4CT / five-colour / planar
- König matching `ν = τ` (consumed)
- Re-primes listed above
- Novelty / external claim
