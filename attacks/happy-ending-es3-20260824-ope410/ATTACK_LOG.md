# Attack Log: happy-ending-es3 — ES(3)=5 finish wave (OPE-410)

**Problem ID:** happy-ending-es3  
**Paperclip:** OPE-410 (follow-on to OPE-403 / PR #24)  
**Attack Lead:** grok-4.5 via xai-oauth  
**Branch base:** `ope/403-happy-ending-es3` (PR #24 head)  
**Branch:** `ope/410-happy-ending-es3-finish`  
**Session:** 2026-08-24

## Context

OPE-409 accepted PR #24 as board-allowed partial. Remaining:
1. hull-card ≥ 3 under GP + case split
2. triangle + 2-interior separating-line orientation bash
3. F1 iff-glue `InConvexPosition4 ↔ ConvexIndependent`

F2: do not merge #23/#24; board owns merge order.

## Delivered this wave (zero sorry/admit/custom axiom)

| Item | Status |
|------|--------|
| F1 `inConvexPosition4_iff_convexIndependent` | **done** |
| `exists_convexIndependent_of_inConvexPosition4` | **done** |
| `exists_hull_vertex_min` (lex-min dual) | **done** |
| hull card ≥ 3 under GP | residual |
| interior separating-line bash | residual |
| full `es_three_eq_five` | residual |

## Verify

```
cd proofs/lean-project
lake env lean ProofLab/HappyEndingES3.lean   # EXIT=0 (unusedTactic warnings only)
lake build ProofLab                          # green
# no sorry/admit/custom axiom in HappyEndingES3.lean
```

## Residual / next

1. Prove `GeneralPosition s ∧ 3 ≤ s.card → 3 ≤ (hullVertices s).card` (third vertex via max-orient + projection tie-break on off-line point).
2. Case `hull.card = 3` with two non-hull points: DE separating signs → `InConvexPosition4` on the double-side pair + D,E; glue via F1.
3. Combine with existing `es_three_eq_five_of_hull_card_ge_four` into `es_three_eq_five : EsThreeEqFiveStatement`.

## Honesty

- **Claim:** none (formalize-only, known classical 1935).
- **Completeness:** PARTIAL — F1 closed; hull≥3 + interior + full theorem still open.
- **No merges** attempted (F2).
