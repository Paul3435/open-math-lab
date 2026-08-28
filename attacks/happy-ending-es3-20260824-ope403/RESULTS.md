# RESULTS — happy-ending-es3 (OPE-403)

## Verdict

**PARTIAL formalize-only** (board-accepted path). Zero `sorry`/`admit`/custom `axiom`.

## What is proved

- Orientation / barycentric / point-in-triangle / hull-vertex Mathlib plumbing for ℝ².
- If a 5-point set has ≥ 4 hull vertices, a convex 4-subset exists
  (`es_three_eq_five_of_hull_card_ge_four`).
- Statement predicates match `problems/happy-ending-es3/STATEMENT.md`.

## What remains

- Hull = triangle with two interior points: separating line through interior pair +
  orientation sign case bash → full `EsThreeEqFiveStatement`.

## Verify

```bash
cd proofs/lean-project
lake env lean ProofLab/HappyEndingES3.lean   # EXIT=0
lake build ProofLab                          # Build completed successfully
```

## Claim

**None.** Known classical (1935). Default no claim.
