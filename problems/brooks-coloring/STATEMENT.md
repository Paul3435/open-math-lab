# Brooks' theorem — χ ≤ Δ except K_n and odd cycles — formalize-only

Authoritative pin: `catalog/problems/brooks-coloring/STATEMENT.md`.

**expected:** known-classical (Brooks 1941). No novelty claim.

Connected finite simple graph, not complete, not an odd cycle:
`G.Colorable G.maxDegree`. Odd-cycle pin: 2-regular connected + odd
`card V` (no `cycleGraph` in Mathlib v4.10.0). Greedy Δ+1 is a
different theorem (`greedy-chromatic`).

**OPE-640 shortlist #2, not the prime.** Do not assign before greedy
unless Director swaps. Do not re-prime Dilworth / Eulerian / König /
Dirac. Do not label greedy as Brooks.
