# Euler's theorem — existence of Eulerian trails (Hierholzer) — formalize-only

Authoritative pin: `catalog/problems/eulerian-hierholzer/STATEMENT.md`.

**expected:** known-classical (Euler 1736 / Hierholzer 1873). No novelty claim.

Finite connected `G` with 0 odd-degree vertices has an Eulerian circuit;
with 2 odd-degree vertices, an Eulerian trail between them.
Proof pin: Hierholzer circuit-merging. Mathlib already has `IsEulerian`
and the necessary `card_odd_degree`; existence is the Trails.lean TODO.

**Level A (OPE-579 / PR #47 MERGED):** `K_1` / `C_n` / `K_2` special
cases, zero-sorry. Do not re-prime.
**Level B (OPE-591 shortlist #2):** ∀G circuit-merging. New proof layer.
