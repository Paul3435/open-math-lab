# Petersen 1-factor theorem — formalize-only

**id:** `petersen-1-factor`
**ticket:** OPE-1223 Formalist Level A (Scout OPE-1216 prime; Director OPE-1222; parent OPE-1215)
**expected:** known-classical (Petersen 1891 cubic bridgeless 1-factor) — **no novelty claim**

## Why not classical / why formalize-only

Settled graph theory: every cubic
bridgeless graph has a 1-factor (perfect
matching). Completely classical
(Petersen 1891).

Not an open problem. Not a novelty claim.

**Not** the Petersen *graph* (Moore equality
case / Hoffman–Singleton comment residual of
consumed `moore`). Different object. Do
**not** classify cages. Do **not** prove
uniqueness of the Petersen graph.
**Not** Tutte's theorem (Matching.lean TODO;
not one-wave; residual of *this* id). Do
**not** sorry Tutte; do **not** take Tutte as
namesake. **Not** König matching `ν=τ`
(consumed). **Not** Hall SDR (already
`all_card_le_biUnion_card_iff_exists_injective`
Hall/Basic.lean L116; USE nothing as namesake;
do **not** re-prove). **Not** Gale–Shapley
(consumed #126; stable matching, different).
**Not** Vizing / `konig_edge_chromatic`
(König *line-colouring* leftover). **Not**
Ore / Dirac Hamiltonian (consumed). **Not**
Nash–Williams arboricity (consumed).

Mathlib v4.10.0 already has the **matching /
regular / bridge infra this theorem needs**:

- `Subgraph.IsMatching` (`Matching.lean` L50)
- `Subgraph.IsPerfectMatching` (L139;
  `isPerfectMatching_iff` L161)
- `IsRegularOfDegree` (`Finite.lean` L261)
- `IsBridge` (`Path.lean` L997;
  `isBridge_iff` L1001)
- `completeGraph` (`Basic.lean` L144) /
  `completeBipartiteGraph` (L153)
- `IsAcyclic` / `IsTree` — **not** namesake
  (Nash–Williams leftover)

There is **no** named Petersen 1-factor
theorem, **no** `petersen_one_factor` /
`Petersen` / `IsBridgeless` / `cubic_bridgeless`
/ `oneFactor` anywhere under `Mathlib/` or
`Archive/` or `ProofLab/` except Moore-bound
*comments* naming the Petersen graph
(`ProofLab/MooreDegreeGirth.lean` — consumed
`moore`, different theorem). Matching.lean
ends with Tutte/Hall TODOs, no 1-factor
existence. Do **not** import `Archive.*`.

OPE-1200 shortlist is **CONSUMED** (#132+#133).
This is a **fresh** catalog-audit id, **not**
a Wantzel leftover continuation, **not** a
circulant-det leftover, **not** a Tutte
revival, **not** a Moore/Petersen-graph
revival, **not** a prize leftover, **not** a
Formalist Level B revival, **not** a third
slot.

Mill NOW: finite cubic-bridgeless 1-factor
theorem after circulant-det (matrix DFT) +
Wantzel (Eisenstein degree). `IsPerfectMatching`
+ `IsBridge` + `IsRegularOfDegree` are waiting
the same way `Matrix.circulant` waited for the
circulant determinant. **Not a rubber-stamp of
Tutte.** **Not a rubber-stamp of the Petersen
graph.**

Do **not** describe an attack as discovering
Petersen's 1-factor theorem. Do **not** expand
into Tutte / Tait colouring / snarks / 4-colour
/ Vizing as extra namesakes (leftover-risk of
*this* id).

## Pinned convention (exact)

**v1 Level A is cubic + bridgeless + perfect
matching on finite named graphs: empty `Fin 0`
(vacuous), `K₄ = completeGraph (Fin 4)`, and
`K_{3,3} = completeBipartiteGraph (Fin 3) (Fin 3)`,
not labelled Petersen.** Count in `ℕ`.

Suggested pin:

```text
-- Level A (not labelled Petersen / Tutte):
-- empty Fin 0 vacuous; K4; K_{3,3}.
-- Not labelled Petersen.

def IsBridgeless {V} (G : SimpleGraph V) : Prop :=
  ∀ e, e ∈ G.edgeSet → ¬ G.IsBridge e

theorem isRegularOfDegree_bot_fin_zero :
    (⊥ : SimpleGraph (Fin 0)).IsRegularOfDegree 3

theorem isBridgeless_bot_fin_zero :
    IsBridgeless (⊥ : SimpleGraph (Fin 0))

theorem exists_perfectMatching_bot_fin_zero :
    ∃ M : (⊥ : SimpleGraph (Fin 0)).Subgraph, M.IsPerfectMatching

theorem completeGraph_fin_four_regular_three :
    (completeGraph (Fin 4)).IsRegularOfDegree 3

theorem completeGraph_fin_four_bridgeless :
    IsBridgeless (completeGraph (Fin 4))

theorem completeGraph_fin_four_exists_perfectMatching :
    ∃ M : (completeGraph (Fin 4)).Subgraph, M.IsPerfectMatching

theorem completeBipartite_fin_three_regular_three :
    (completeBipartiteGraph (Fin 3) (Fin 3)).IsRegularOfDegree 3

theorem completeBipartite_fin_three_bridgeless :
    IsBridgeless (completeBipartiteGraph (Fin 3) (Fin 3))

theorem completeBipartite_fin_three_exists_perfectMatching :
    ∃ M : (completeBipartiteGraph (Fin 3) (Fin 3)).Subgraph,
      M.IsPerfectMatching

-- Level B namesake (all cubic bridgeless; residual OK)
theorem petersen_one_factor {V} [Fintype V]
    (G : SimpleGraph V)
    (hreg : G.IsRegularOfDegree 3)
    (hbr : IsBridgeless G) :
    ∃ M : G.Subgraph, M.IsPerfectMatching
```

Finite `Fin n` / `Fin 3 ⊕ Fin 3` is
load-bearing. Cubic `IsRegularOfDegree 3` is
load-bearing. Bridgeless (`¬ IsBridge`) is
load-bearing. `IsPerfectMatching` is
load-bearing.

**Level A may land only** empty / `K₄ =
completeGraph (Fin 4)` / `K_{3,3}` (optional
extra: utility encoding is `K_{3,3}`), **not**
labelled Petersen.
Reuse Mathlib `IsMatching` / `IsPerfectMatching`
/ `IsRegularOfDegree` / `IsBridge` /
`completeGraph` / `completeBipartiteGraph` —
**do not re-prove** matching, degree, or
bridge definitions.

**Level B** is the namesake: every finite
cubic bridgeless graph has a 1-factor. Do not
sorry the namesake; honest partial is allowed
(comment residual, not `sorry`). Tutte /
Tait / snarks / Petersen-graph uniqueness
are residual.

## Landmines

1. **Do not re-prove** `IsMatching` /
   `IsPerfectMatching` / `IsRegularOfDegree` /
   `IsBridge` / `completeGraph` /
   `completeBipartiteGraph` / Hall SDR.
   Already Mathlib. Use them.
2. **This is not** Tutte (Matching.lean TODO).
   Not one-wave. Residual of this id. Do not
   sorry Tutte. Do not take Tutte as namesake.
3. **This is not** the Petersen graph / Moore
   cage / Hoffman–Singleton (consumed `moore`
   comment residual). Different theorem.
4. **This is not** König matching (consumed) /
   Hall (already-in) / Gale–Shapley (#126) /
   Vizing / `konig_edge_chromatic`.
5. **This is not** `circulant-det` (#132) /
   `det_circulant` / DFT / Fourier / pfaffian.
6. **This is not** `wantzel-constructible` (#133)
   / `IsConstructible` / angle trisection.
7. **This is not** `lame-euclid` / `schur-product`
   / `gale-shapley` / `farey-sequence` /
   Nash–Williams / BvN / Ore / Dirac.
8. **Do not** prove Kirchhoff / Cayley trees
   as namesake (consumed leftovers).
9. **Do not** re-prime the consumed mill list.
10. **Leave OPE-403 alone.** Leave OPE-1195
    leftover status alone.
11. **Do not import `Archive.*`.**
12. Default no claim. No novelty claim.

## Out of v1

- Tutte 1-factor criterion
- Tait colouring / snarks / 4-colour
- Petersen-graph uniqueness / Moore cages
- Vizing / class-1/class-2
- Barnette / Grünbaum
- Prize claims / Millennium / Beal
