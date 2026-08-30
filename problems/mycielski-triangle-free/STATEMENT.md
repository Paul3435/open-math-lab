# Mycielski — triangle-free unbounded χ — formalize-only

Authoritative pin: `catalog/problems/mycielski-triangle-free/STATEMENT.md`.

**expected:** known-classical (Mycielski 1955). No novelty claim.

Finite simple graphs: `∀ k, ∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧ ¬ G.Colorable k`. Mathlib has `CliqueFree` / `Colorable` / odd-loop `χ ≥ 3`; ZERO Mycielski.

**OPE-683 shortlist #2, not the prime.** Fresh id after Havel #61 and Menger #62 consumed. Not a Brooks leftover. Do not assign before `cayley-trees` unless Director swaps. Do not re-prime greedy / Brooks / havel-hakimi / menger-vertex / Dilworth / Eulerian / König / Dirac. Do not prove Grötzsch / Hajós / Kneser / Vizing / 4CT/5CT.
