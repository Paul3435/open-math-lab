# RESULTS — R(3,5)=14 formalize-only (OPE-393)

## Outcome

**Closed.** Classical `R(3,5)=14` formalized zero-sorry in `ProofLab/Ramsey.lean`.

| Bound | Theorem | Method |
|-------|---------|--------|
| R(3,5) > 13 | `ramsey35_gt_13` | Circulant `C₁₃({±1,±5})` on `Fin 13`; `native_decide` no red K3 / no blue K5 |
| R(3,5) ≤ 14 | `ramsey35_le_14` | `R(2,5)+R(3,4)=5+9` via `ramsey_two_right` + `ramsey34_le_9` + `ramseyUpper_add` |
| equality | `ramsey35_eq_14` | pair of bounds |

## Honesty

- Known classical (Greenwood–Gleason 1955). **formalize-only; no novelty claim.**
- Does not classify all critical colourings; existence witness only for the lower bound.

## Verify

```bash
cd proofs/lean-project
lake env lean ProofLab/Ramsey.lean
lake build ProofLab
```
