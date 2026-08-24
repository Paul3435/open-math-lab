# Attack log — ramsey-r33

| when | agent | strategy | result |
|------|-------|----------|--------|
| 2026-08-08 14:40 | Attack Lead | R(3,3) via certified exhaustive enumeration (`native_decide` over Fin 15 edge-boolean colourings of K6); lower bound via 5-cycle witness | R(3,3) ≤ 6 PROVED zero-sorry (ProofLab/Ramsey.lean `ramsey33_le_6`); R(3,3) > 5 PROVED (`not_ramsey33_5`, `ramsey33_gt_5`). `lake build ProofLab.Ramsey` green, `lake env lean ProofLab.lean` exit 0. |
| 2026-08-08 15:40 | Attack Lead | Certified lower-bound witnesses via `native_decide` on concrete graph colourings; complement symmetry lemma | R(3,4) > 8 PROVED (`ramsey34_gt_8`, 8-vertex witness, 10 red edges, no red K3 / no blue K4). R(4,4) > 17 PROVED (`ramsey44_gt_17`, Paley-17 self-complementary colouring, 68 red edges, no K4 in either colour). `ramseyUpper_swap` proves `RamseyUpper k l n ↔ RamseyUpper l k n` (⇒ `R(3,4)=R(4,3)`). `lake build ProofLab` green, zero sorries. |
| 2026-08-08 16:55 | Attack Lead | Hand pigeonhole R(3,3)≤6 for all graphs on Fin 6 | `ramsey33_fin6` zero-sorry (extract3 + clique3_of_adj); reusable primitive for R(3,4). |
| 2026-08-24 | Attack Lead | Degree-parity hand proof R(3,4)≤9 + classical recurrence R(4,4)≤R(3,4)+R(4,3) | **CLOSED.** `ramsey34_le_9` / `ramsey34_eq_9`: red-deg ≤3 (4 red nbrs → red K3 or blue K4), blue-deg ≤5 (6 blue nbrs + R(3,3) on finset → red K3 or blue K4 with apex), force blue-deg=5 on Fin 9 → handshake parity contradiction (`not_five_regular_fin9`). `ramsey44_le_18` / `ramsey44_eq_18` via `ramseyUpper_add` with a=b=9. Transfer lemmas: `ramsey33_clique_inside_finset`, `ramseyUpper_clique_inside_finset`, `comap_compl_eq_of_injective`, `hasClique_of_hasClique_comap`. `lake build ProofLab` **green**, `lake env lean ProofLab/Ramsey.lean` exit 0, **zero** sorry/admit/axiom. formalize-only; **no claim**. |

## Status — acceptance checklist

1. **Ramsey predicate** — `HasClique`, `RamseyUpper k l n` over `SimpleGraph (Fin n)` red/blue (red=G, blue=Gᶜ), Mathlib `IsNClique`/`Clique`. DONE.
2. **R(3,3)=6** — `ramsey33_eq_6` = (`ramsey33_gt_5`, `ramsey33_fin6`); also exhaustive `ramsey33_le_6`. Zero sorry. DONE.
3. **R(3,4)=9** — `ramsey34_eq_9` = (`ramsey34_gt_8`, `ramsey34_le_9`). Zero sorry. DONE.
4. **R(4,4)=18** — `ramsey44_eq_18` = (`ramsey44_gt_17` Paley-17, `ramsey44_le_18` via recurrence). Zero sorry. DONE (stretch closed).
5. **`lake build ProofLab` green**; no sorry/admit/axiom in `ProofLab/Ramsey.lean`. DONE.
6. ATTACK_LOG + ledger updated on close. DONE this entry.

## Residual risks (board-facing, no claim)

- **Formalize-only / known-classical.** Greenwood–Gleason 1955 etc. Value is the Mathlib-gap formalization, not novelty. Default **no claim**; board gates external communication.
- **API shape is lab-local** (`ProofLab.Ramsey.RamseyUpper`), not upstream Mathlib PR-ready packaging (naming, generality over arbitrary `Fintype`, docs). Upstreaming would need a separate board-approved contribution ticket.
- **DecidableRel via classical** in hand proofs (`Classical.decRel`) — fine for Prop theorems; not a computational certificate path for the upper bounds (those are pure hand arguments).
- **Recurrence needs `0 < a+b`** as an explicit hypothesis on `ramseyUpper_add` (satisfied by a=b=9).
- Pre-existing Windows lake link error 206 has **not** been observed this run: full `lake build ProofLab` completed successfully.
