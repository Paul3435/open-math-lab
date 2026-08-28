# Kőnig's theorem — bipartite matching number = vertex-cover number — formalize-only

Authoritative pin: `catalog/problems/konig-bipartite/STATEMENT.md`.

**expected:** known-classical (Kőnig 1931). No novelty claim.

Finite `G.Colorable 2` ⇒ matching number = vertex-cover number.
Hall SDR is a different upstream theorem. Dilworth is out of v1 scope.

**Level A (OPE-580 / PR #48 MERGED):** `IsVertexCover`, easy `ν≤τ`,
`K_{m,n}` / star / bot, `K_3` landmine, zero-sorry. Do not re-prime.
**Level B (OPE-591 RECOMMENDED PRIME):** full `Colorable 2 → ν=τ`.
New proof layer (alternating paths / Hall reduction).
