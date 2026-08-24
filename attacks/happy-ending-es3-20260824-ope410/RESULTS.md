# RESULTS — happy-ending-es3 (OPE-410)

## Verdict

**PARTIAL formalize-only** finish wave. Zero `sorry`/`admit`/custom `axiom`.

## What is proved

- **F1** InConvexPosition4 ↔ ConvexIndependent on 4-point sets
- Lex-min hull vertex dual
- **hullVertices.card ≥ 2** (always for card≥2)
- **hullVertices.card ≥ 3 under GP** (card≥3) via max-orient + proj third vertex
- Prior OPE-403 plumbing + hull≥4 partial main

## What remains

- Triangle + 2-interior separating-line orientation bash
- Full `es_three_eq_five` discharging EsThreeEqFiveStatement (case split 3 vs ≥4)

## Verify

```bash
cd proofs/lean-project
lake env lean ProofLab/HappyEndingES3.lean   # EXIT=0
lake build ProofLab                          # green
```

## Claim

**None.** Known classical (1935). Default no claim.
