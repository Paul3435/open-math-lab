# Euler's theorem — existence of Eulerian trails (Hierholzer) — formalize-only

Authoritative pin: `catalog/problems/eulerian-hierholzer/STATEMENT.md`.

**expected:** known-classical (Euler 1736 / Hierholzer 1873). No novelty claim.

Finite connected `G` with 0 odd-degree vertices has an Eulerian circuit;
with 2 odd-degree vertices, an Eulerian trail between them.
Proof pin: Hierholzer circuit-merging. Mathlib already has `IsEulerian`
and the necessary `card_odd_degree`; existence is the Trails.lean TODO.

**Level A (OPE-579 / PR #47 MERGED):** `K_1` / `C_n` / `K_2` special
cases, zero-sorry. Do not re-prime.
**Level B (OPE-597 / PR #51 MERGED):** honest partial —
`eulerian_hierholzer_circuit` + `eulerian_complete_odd`. Do not
re-prime circuit / complete-odd.
**Trail residual (OPE-613 shortlist #2; OPE-633 / PR #55 MERGED):** `card oddDeg = 2` ∀G.
LANDED as `eulerian_hierholzer_trail`. Encoding pin: start-at-odd longest trail; **no
dummy-edge**. Do not re-prime.
