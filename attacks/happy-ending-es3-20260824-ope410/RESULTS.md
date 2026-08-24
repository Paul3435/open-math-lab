# RESULTS — happy-ending-es3 (OPE-410)

## Verdict

**PARTIAL formalize-only** finish wave. Zero `sorry`/`admit`/custom `axiom`.

## What is proved (this PR)

- **F1** `InConvexPosition4 a b c d ↔ ConvexIndependent` on the 4-point finset
  (`inConvexPosition4_iff_convexIndependent`), plus convenience exporter.
- Lex-min hull vertex dual: `exists_hull_vertex_min`.
- Prior OPE-403 plumbing retained (orient, bary, hull≥4 partial main).

## What remains

- GP + card≥3 ⇒ hullVertices.card ≥ 3
- Triangle + 2-interior separating-line orientation bash
- Full `es_three_eq_five` discharging `EsThreeEqFiveStatement`

## Verify

```bash
cd proofs/lean-project
lake env lean ProofLab/HappyEndingES3.lean   # EXIT=0
lake build ProofLab                          # Build completed successfully
```

## Claim

**None.** Known classical (1935). Default no claim.
