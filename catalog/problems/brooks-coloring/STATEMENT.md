# Brooks' theorem — χ ≤ Δ except complete graphs and odd cycles — formalize-only

**id:** `brooks-coloring`
**ticket:** OPE-640 Scout shortlist #2 (support OPE-639; post Dilworth #53+#54 + Eulerian trail #55)
**expected:** known-classical (Brooks 1941) — **no novelty claim**

## Why not classical / why formalize-only

Settled 1941: a connected finite simple graph that is not complete and
not an odd cycle satisfies χ ≤ Δ. Not an open problem. Mathlib v4.10.0
has `Colorable` / `chromaticNumber` / `maxDegree` / `chromaticNumber_top`
(complete graphs) and `Walk.three_le_chromaticNumber_of_odd_loop`. There
is **no** Brooks theorem (word-regexp `brooks` → ZERO Mathlib+Archive),
**no** `Colorable G.maxDegree` under a not-complete / not-odd-cycle
hypothesis, and **no** `cycleGraph` helper (odd-cycle exception must be
pinned without one). Coloring.lean's TODO is trees / planar / chromatic
polynomials — not Brooks.

This is **not** a re-prime of shortlist prime `greedy-chromatic`
(χ ≤ Δ+1 always). Greedy is the cheap lemma; Brooks is the namesake
with exceptions. Do not describe an attack as discovering Brooks.
Do not assign this id before greedy unless Director explicitly swaps.

## Pinned convention (exact)

Let `V` be a finite type with `[Fintype V] [DecidableEq V]` and
`G : SimpleGraph V` with `[DecidableRel G.Adj]`.

**Odd cycle (no `cycleGraph` in the pin):** `G` is an odd cycle when
`G.Connected`, `Odd (Fintype.card V)`, and `∀ v, G.degree v = 2`
(equivalently: there is a Hamiltonian cycle that uses every edge, of
odd length). Do **not** invent `cycleGraph` as a Mathlib-gap claim;
define a ProofLab predicate.

**Complete:** `G = ⊤` (Mathlib `chromaticNumber_top`).

**Claim (Brooks, connected):**

```text
theorem brooks_colorable
    (hConn : G.Connected)
    (hNotComplete : G ≠ ⊤)
    (hNotOddCycle : ¬ IsOddCycle G) :
    G.Colorable G.maxDegree
```

for a pinned `IsOddCycle` as above. Equivalent `chromaticNumber ≤
maxDegree` form is the same heartbeat if cheap.

**Disconnected stretch (not v1):** apply the connected statement
componentwise; χ(G) = max_χ(components). Only if cheap. v1 is
connected.

**Encoding pin:** Mathlib `Colorable` + `maxDegree` + `Connected` +
`⊤`. Greedy `ProofLab.GreedyChromatic.greedy_colorable` is an allowed
lemma once that id lands; do **not** re-prove Δ+1 as Brooks.

## Landmines

1. **Exceptions are load-bearing.** Complete graphs have χ = Δ+1.
   Odd cycles have χ = 3 = Δ+1. Dropping either is a false theorem.
2. **No `cycleGraph` in Mathlib v4.10.0.** Pin 2-regular connected +
   odd order (or Hamiltonian cycle = edge set). Do not wait for a
   Mathlib cycle constructor.
3. **Connected is the v1 pin.** The usual statement is connected;
   disconnected needs a componentwise restatement.
4. **`maxDegree = 0` / `= 1`.** Edgeless / matching graphs: greedy
   already gives χ ≤ 1 or 2. Brooks with `Colorable 0` is only for
   empty. Pin `maxDegree` as-is; do not special-case unless empty.
5. **This is not greedy.** Greedy always uses Δ+1. Brooks saves one
   colour except on the two families. Proving only greedy and labelling
   it Brooks is a review block.
6. **This is not Vizing, not 4CT/5CT, not König Colourable-2, not
   chromatic polynomials.** No planarity. No edge-colouring.
7. **Critical-graph / Kempe-chain proofs are the budget sink.**
   Prefer a published human-scale proof (Lovász contraction, or
   removing a vertex of degree Δ and extending) over a computer
   search. If the Formalist cannot name the proof in STATEMENT, stop;
   do not brute-force.
8. **Do not expand v1 into list-colouring Brooks, Borodin–Kostochka,
   or overfull-conjecture adjacent claims.**

## Proof sketch (classical, Brooks 1941 / textbook)

Greedy already gives χ ≤ Δ+1. For Brooks: take a connected G that is
not `⊤` and not an odd cycle, pick a vertex v of degree Δ whose
neighbours do not include all of V and are not a clique covering the
rest (such a v exists unless G is complete or a cycle). Colour G−v
with Δ colours by IH / greedy, then extend: the neighbours of v do not
use all Δ colours, or a Kempe swap frees one.

Partial: **Level A** exception families (`⊤` via `chromaticNumber_top`;
odd cycle χ = 3 via `three_le_chromaticNumber_of_odd_loop` + a
2-regular colouring) and the greedy lemma (prefer depending on
`greedy-chromatic` if already merged). **Level B** namesake
`brooks_colorable` for connected G. Cap two levels.

## Lean gate (when attacked)

- Target module: `proofs/lean-project/ProofLab/Brooks.lean`
- Reuse Mathlib `Colorable` / `maxDegree` / `chromaticNumber_top` /
  `Walk.three_le_chromaticNumber_of_odd_loop`. Reuse
  `ProofLab.GreedyChromatic` if present. Do **not** re-prove greedy as
  Brooks.
- Zero `sorry`; `lake env lean` exit 0
- Default **no claim**
- Do not import `Archive.*`

## Canonical source

R. L. Brooks, *On colouring the nodes of a network*, Proceedings of
the Cambridge Philosophical Society **37** (1941) 194–197. Textbook
pin: Diestel, *Graph Theory*, Brooks' theorem (the statement
immediately after the Δ+1 corollary). Type pin: Mathlib
`SimpleGraph.Colorable` + `maxDegree` + `⊤`. Odd-cycle pin: 2-regular
connected + odd `card V` (no `cycleGraph` in the v4.10.0 snapshot).
