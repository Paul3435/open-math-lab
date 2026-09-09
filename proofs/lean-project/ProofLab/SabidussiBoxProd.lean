/-
Sabidussi box-product chromatic number — Level A only (empty Fin 0 /
K₁ □ K₁ / K₂ □ K₂ = C₄ Colorable). **Not labelled Sabidussi / Brooks /
Hedetniemi.**

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 pin `a719ba5c3115` has `boxProd` / notation `□` /
`Colorable` / `chromaticNumber` / `completeGraph` /
`Colorable.of_embedding` / `colorable_of_isEmpty` as **infra**. ZERO
named Sabidussi / `boxProd_colorable` / `colorable_boxProd` /
`chromaticNumber_boxProd` under `Mathlib/` or `Archive/` or
`ProofLab/`. Prod.lean ends L219 with connectedness + degree, file
TODO other products, ZERO colouring. Completing the Level A empty /
K₁ □ K₁ / K₂ □ K₂ glue is the gap this ticket lands. The Level B
namesake `sabidussi_boxprod` (every finite G, H satisfy
`χ(G □ H) = max(χ(G), χ(H))`) is **out of this ticket** and is
**not** sorry-ed. Hedetniemi / other products / Vizing domination
extras are residual of this id.

Pin: `catalog/problems/sabidussi-boxprod/STATEMENT.md`
(OPE-1243; Scout OPE-1233 leftover; Director OPE-1242). Encoding:
Mathlib `boxProd` / `Colorable` / `completeGraph` on
`Fin 0 × Fin 0` / `Fin 1 × Fin 1` / `Fin 2 × Fin 2`. Zero `sorry`.
Do not import `Archive.*`.

This is **not** `boxProd` / `□` (`Prod.lean` L39 / L46) — already
Mathlib. **USE, do not re-prove; do not cite as Sabidussi.**
This is **not** `Colorable` / `chromaticNumber` (`Coloring.lean`
L127 / L149) — already Mathlib. **USE, do not re-prove.**
This is **not** Brooks / greedy (`ProofLab/Brooks.lean` /
`ProofLab/GreedyChromatic.lean`) — consumed `χ ≤ Δ+1`; USE
`Colorable`; do **not** re-prove; do **not** cite as Sabidussi.
This is **not** AES / König `χ'` / bipartite-odd-cycle / Mycielski
(consumed colouring mills; different theorems).
This is **not** Hedetniemi (categorical product; **false**;
Prod.lean TODO other products — residual of this id; do **not**
sorry Hedetniemi).
This is **not** Kraft / McMillan / Huffman / Shannon
(`ProofLab/KraftInequality.lean`, PR #138).
This is **not** Petersen 1-factor (`ProofLab/PetersenOneFactor.lean`,
PR #135) / Tutte.
This is **not** Lagrange CF (`ProofLab/LagrangeQuadraticCf.lean`,
PR #136) / Pell.
Do not re-prime the consumed mill. Leave OPE-403 alone.
Leave OPE-1195 alone.

v1 is `Colorable` on finite named box products: empty `⊥ □ ⊥` on
`Fin 0 × Fin 0`, `K₁ □ K₁ = completeGraph (Fin 1) □ completeGraph
(Fin 1)`, and `K₂ □ K₂` (the 4-cycle), **not labelled Sabidussi**.
`Colorable n` not `chromaticNumber` on Level A. Finite `Fin 0` /
`Fin 1` / `Fin 2` products are load-bearing. `Colorable` is
load-bearing. Box product `□` is load-bearing.

Level A: empty `Fin 0 × Fin 0` is `IsEmpty`, so colorable
(`Colorable 0` via `colorable_of_isEmpty`). `K₁ □ K₁` is a single
vertex, `Colorable 1`. `K₂ □ K₂` is the 4-cycle C₄; colour by
coordinate-sum in `Fin 2`, `Colorable 2`. **Not** labelled
Sabidussi.

Transcribed classical argument (G. Sabidussi, *Graphs with given
group and given graph-theoretical properties*, Canad. J. Math. 9
(1957); Vizing also). Compact form: Wikipedia *Cartesian product
of graphs* (chromatic number). Type pin: `boxProd` / `Colorable` /
`completeGraph`. Brooks is a different consumed theorem.
Hedetniemi is a different false statement. No novelty claim.
Default no claim.
-/
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Tactic

set_option linter.unusedVariables false

open SimpleGraph

namespace ProofLab.SabidussiBoxProd

/-! ## Level A: empty Fin 0 / K₁ □ K₁ / K₂ □ K₂ = C₄
(not labelled Sabidussi / Brooks / Hedetniemi) -/

/-- Empty `⊥ □ ⊥` on `Fin 0 × Fin 0` is `IsEmpty`, so `Colorable 0`.
Uses Mathlib `colorable_of_isEmpty`; does **not** re-prove empty
colouring. Glue; **not** labelled Sabidussi. -/
theorem colorable_boxProd_bot_fin_zero :
    (⊥ □ ⊥ : SimpleGraph (Fin 0 × Fin 0)).Colorable 0 :=
  colorable_of_isEmpty _ 0

/-- `K₁ □ K₁` is a single vertex, so `Colorable 1`. Uses Mathlib
`colorable_of_fintype` / `Fintype.card_prod` / `Fintype.card_fin`;
does **not** re-prove them. Glue; **not** labelled Sabidussi. -/
theorem colorable_boxProd_complete_fin_one :
    (completeGraph (Fin 1) □ completeGraph (Fin 1)).Colorable 1 := by
  have h := colorable_of_fintype
    (completeGraph (Fin 1) □ completeGraph (Fin 1))
  simpa [Fintype.card_prod, Fintype.card_fin] using h

/-- Coordinate-sum colouring of `K₂ □ K₂`. Adjacent vertices of a
box product differ in exactly one coordinate; on `Fin 2` that
flips the sum. Encoding; **not** labelled Sabidussi / Brooks. -/
def boxProdCompleteFinTwoColoring :
    (completeGraph (Fin 2) □ completeGraph (Fin 2)).Coloring (Fin 2) :=
  Coloring.mk (fun v => v.1 + v.2) fun {v w} hvw => by
    change v.1 + v.2 ≠ w.1 + w.2
    rcases (boxProd_adj.mp hvw) with ⟨hG, hEq⟩ | ⟨hH, hEq⟩
    · rw [hEq]
      exact fun hcol => hG (add_right_cancel hcol)
    · rw [hEq]
      exact fun hcol => hH (add_left_cancel hcol)

/-- `K₂ □ K₂` is the 4-cycle C₄, bipartite, `Colorable 2`. Glue;
**not** labelled Sabidussi / Brooks / Hedetniemi. Does **not**
re-prove bipartite-odd-cycle. -/
theorem colorable_boxProd_complete_fin_two :
    (completeGraph (Fin 2) □ completeGraph (Fin 2)).Colorable 2 :=
  ⟨boxProdCompleteFinTwoColoring⟩

/- Residual of this id (comment, **not** `sorry`):
Level B namesake `sabidussi_boxprod` — every finite `G, H` satisfy
`χ(G □ H) = max(χ(G), χ(H))`. Hedetniemi categorical-product
(false) / lexicographic / strong / tensor products / Vizing
domination / list colouring of products are residual, not extra
namesakes. Out of this ticket. Do **not** prove Hedetniemi /
Brooks / greedy / AES / König χ' / bipartite-odd-cycle /
Mycielski / kraft-inequality / McMillan / Huffman / Shannon /
petersen-1-factor / Tutte / lagrange-quadratic-cf / Pell. -/

end ProofLab.SabidussiBoxProd

