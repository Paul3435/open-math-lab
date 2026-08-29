# Havel–Hakimi — graphic sequences — formalize-only

Authoritative pin: `catalog/problems/havel-hakimi/STATEMENT.md`.

**expected:** known-classical (Havel 1955 / Hakimi 1962). No novelty claim.

Finite simple graph on `Fin n`: a nonincreasing `d : Fin n → ℕ` is
graphic (`∃ G, ∀ i, G.degree i = d i`) iff the Havel–Hakimi
reduction is graphic. Mathlib has `degree` / handshaking; ZERO
`IsGraphic` / `Havel` / `Hakimi`.

**OPE-666 RECOMMENDED PRIME.** New proof layer after greedy #57 and
Brooks A/B #58/#59 closed. Do not re-prime greedy / Brooks / Dilworth
/ Eulerian / König / Dirac. Do not prove Erdős–Gállai, Gale–Ryser,
or Tutte in this id.
