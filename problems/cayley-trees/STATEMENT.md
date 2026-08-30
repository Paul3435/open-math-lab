# Cayley — labelled trees `n^{n-2}` — formalize-only

Authoritative pin: `catalog/problems/cayley-trees/STATEMENT.md`.

**expected:** known-classical (Cayley 1889 / Prüfer 1918). No novelty claim.

Finite labelled simple graphs: `Fintype.card {s : Finset (Sym2 (Fin n)) // (fromEdgeSet ↑s).IsTree} = n^{n-2}` for `n ≥ 1`. Mathlib has `IsTree` / `fromEdgeSet` / `card_edgeFinset`; ZERO Prüfer / labelled-tree count.

**OPE-683 RECOMMENDED PRIME.** Independent re-score after Havel #61 and Menger #62 consumed; encoding now pinned (edge-Finsets, not `{G // G.IsTree}`). Not a rubber-stamp leftover. Do not re-prime havel-hakimi / menger-vertex / greedy / Brooks / Dilworth / Eulerian / König / Dirac. Do not prove Kirchhoff / Tutte / unlabelled A000055. Not group Cayley, not Cayley–Hamilton.
