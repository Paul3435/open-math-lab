# Sabidussi box-product chromatic number — formalize-only

**id:** `sabidussi-boxprod`
**ticket:** OPE-1243 Formalist Level A (Scout OPE-1233 leftover; Director OPE-1242)
**expected:** known-classical (Sabidussi 1957:
χ(G □ H) = max(χ(G), χ(H))) — **no novelty claim**

## Why not classical / why formalize-only

Settled product-graph colouring: the
Cartesian (box) product satisfies
`χ(G □ H) = max(χ(G), χ(H))`. Completely
classical (Sabidussi 1957; Vizing also).

Not an open problem. Not a novelty claim.

**Not** Brooks / greedy chromatic
(consumed; `Colorable` is Coloring.lean
L127 — USE encoding, do **not** re-prove
`brooks` / `greedy`). **Not** AES
(consumed #108; degree ⇒ 2-colourable,
different theorem). **Not** König
line-colouring `χ' = Δ` (consumed #112;
edge colouring, different). **Not**
bipartite-odd-cycle (consumed; `χ = 2`
iff no odd walk — a special case of
products of bipartite graphs is **not**
the namesake). **Not** Ore / Dirac
Hamiltonian (consumed). **Not** Mycielski
(consumed). **Not** Hedetniemi (categorical
product; **false**; Prod.lean TODO other
products — residual of *this* id).

Mathlib v4.10.0 already has the **box-product
/ colouring infra this theorem needs**:

- `SimpleGraph.boxProd` / notation `□`
  (`Prod.lean` L39 / L46)
- `boxProd_adj` L49 / `boxProdLeft` L83 /
  `boxProdRight` L90 / `boxProd_connected` L189 /
  `boxProd_degree` L213 — **not** namesake
- `Colorable` (`Coloring.lean` L127)
- `chromaticNumber` L149
- `Colorable.mono` L204 / `Colorable.of_embedding` L219
- `completeGraph` (`Basic.lean` L144)

There is **no** named Sabidussi / box-product
chromatic theorem, **no** `sabidussi` /
`boxProd_colorable` / `colorable_boxProd` /
`chromaticNumber_boxProd` anywhere under
`Mathlib/` or `Archive/` or `ProofLab/`
(this run → ZERO on those names). Prod.lean
ends L219 with connectedness + degree, file
TODO "Define all other graph products!",
**no colouring**. Do **not** import
`Archive.*`.

OPE-1216 shortlist is **CONSUMED**
(#135+#136). This is a **fresh**
catalog-audit leftover id, **not** a
Petersen leftover continuation, **not**
a Lagrange leftover, **not** a Brooks /
greedy / AES / König-χ' revival, **not**
a prize leftover, **not** a Formalist
Level B revival, **not** a third slot.

Mill NOW: finite box-product colouring
leftover beside Kraft (prefix-free codes).
`boxProd` + `Colorable` are waiting the
same way `IsMatching` waited for Petersen.
**Not a rubber-stamp of Brooks.** **Not
a rubber-stamp of König χ'.**

Do **not** describe an attack as discovering
Sabidussi's formula. Do **not** expand into
Hedetniemi / lexicographic product / Vizing
domination-conjecture as extra namesakes
(leftover-risk of *this* id).

## Pinned convention (exact)

**v1 Level A is `Colorable` on finite named
box products: empty `⊥ □ ⊥` on
`Fin 0 × Fin 0`, `K₁ □ K₁ =
completeGraph (Fin 1) □ completeGraph (Fin 1)`,
and `K₂ □ K₂` (the 4-cycle), not labelled
Sabidussi.** `Colorable n` not
`chromaticNumber` on Level A.

Suggested pin:

```text
-- Level A (not labelled Sabidussi / Brooks):
-- empty Fin 0; K1□K1; K2□K2 = C4.
-- Not labelled Sabidussi.

theorem colorable_boxProd_bot_fin_zero :
    (⊥ □ ⊥ : SimpleGraph (Fin 0 × Fin 0)).Colorable 0

theorem colorable_boxProd_complete_fin_one :
    (completeGraph (Fin 1) □ completeGraph (Fin 1)).Colorable 1

theorem colorable_boxProd_complete_fin_two :
    (completeGraph (Fin 2) □ completeGraph (Fin 2)).Colorable 2

-- Level B namesake (all finite; residual OK)
theorem sabidussi_boxprod {α β}
    [Fintype α] [Fintype β]
    (G : SimpleGraph α) (H : SimpleGraph β) :
    (G □ H).chromaticNumber =
      max G.chromaticNumber H.chromaticNumber
```

Finite `Fin 0` / `Fin 1` / `Fin 2` products
are load-bearing. `Colorable` is
load-bearing. Box product `□` is
load-bearing.

**Level A may land only** empty / `K₁ □ K₁`
/ `K₂ □ K₂` (optional extra: `Colorable 0`
uninhabited on empty → `Colorable 1` is
an allowed encoding tweak, **not** labelled
Sabidussi), **not** labelled Sabidussi.
Reuse Mathlib `boxProd` / `Colorable` /
`completeGraph` / `Colorable.of_embedding`
— **do not re-prove** Brooks, greedy, or
bipartite-odd-cycle.

**Level B** is the namesake: every finite
`G, H` satisfy `χ(G □ H) = max(χ(G), χ(H))`.
Do not sorry the namesake; honest partial
is allowed (comment residual, not `sorry`).
Hedetniemi / other products / Vizing
domination are residual.

## Landmines

1. **Do not re-prove** `boxProd` /
   `Colorable` / `chromaticNumber` /
   `completeGraph` / `Colorable.of_embedding`
   / Brooks / greedy. Already Mathlib or
   consumed. Use them.
2. **This is not** Brooks / greedy
   (consumed). Different theorem
   (`χ ≤ Δ+1`). Do not revive.
3. **This is not** AES / Mycielski /
   König `χ' = Δ` / bipartite-odd-cycle
   (consumed). Different colouring theorems.
4. **This is not** Hedetniemi (categorical
   product; false). Residual of this id.
   Prod.lean TODO other products — do not
   sorry them.
5. **This is not** `petersen-1-factor`
   (#135) / Tutte / Hall / 1-factorization.
6. **This is not** `lagrange-quadratic-cf`
   (#136) / Pell / `terminates_iff_rat`.
7. **This is not** Kraft / Huffman /
   Shannon (OPE-1233 prime; different
   domain). Do not prove Kraft here.
8. **This is not** Vizing edge-colouring
   (`konig_edge_chromatic` leftover).
9. **Do not** re-prime the consumed mill
   list.
10. **Leave OPE-403 alone.** Leave OPE-1195
    leftover status alone.
11. **Do not import `Archive.*`.**
12. Default no claim. No novelty claim.

## Out of v1

- Hedetniemi categorical-product conjecture (false)
- Lexicographic / strong / tensor products (Prod.lean TODO)
- Vizing domination conjecture on products
- List colouring of products
- Brooks / greedy / AES / König χ' revival
- Prize claims / Millennium / Beal
