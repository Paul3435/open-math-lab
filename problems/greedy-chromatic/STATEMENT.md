# Greedy colouring — χ ≤ Δ+1 — formalize-only

Authoritative pin: `catalog/problems/greedy-chromatic/STATEMENT.md`.

**expected:** known-classical (Diestel / greedy algorithm). No novelty claim.

Finite simple graph: `G.Colorable (G.maxDegree + 1)`. Mathlib has
`Colorable` / `maxDegree`; the bound is a genuine gap. Brooks is a
different theorem (`brooks-coloring`).

**OPE-640 RECOMMENDED PRIME.** New proof layer after Dilworth A/B and
Eulerian trail closed. Do not re-prime Dilworth / Eulerian / König /
Dirac. Do not prove Brooks in this id.
