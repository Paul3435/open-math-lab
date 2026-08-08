# Attack log — ramsey-r33

| when | agent | strategy | result |
|------|-------|----------|--------|
| 2026-08-08 14:40 | Attack Lead | R(3,3) via certified exhaustive enumeration (`native_decide` over Fin 15 edge-boolean colourings of K6); lower bound via 5-cycle witness | R(3,3) ≤ 6 PROVED zero-sorry (ProofLab/Ramsey.lean `ramsey33_le_6`); R(3,3) > 5 PROVED (`not_ramsey33_5`, `ramsey33_gt_5`). `lake build ProofLab.Ramsey` green, `lake env lean ProofLab.lean` exit 0. |

## Status

- **Done (zero sorry):** `R(3,3)=6` fully certified in Lean 4 + Mathlib (v4.10.0 pin):
  - `RamseyUpper k l n` predicate over `SimpleGraph (Fin n)` red/blue colourings
    (red = graph, blue = complement), using Mathlib `IsNClique`/`Clique`.
  - `ramsey33_le_6` : upper bound — exhaustive search of all 2^15 colourings of `K_6`.
  - `not_ramsey33_5` / `ramsey33_gt_5` : lower bound via the 5-cycle witness.
- **Not yet proved:** `R(3,4)=9` and `R(4,4)=18`.

## Why R(3,4)=9 / R(4,4)=18 are not certified by the same trick

The certified-`native_decide` method enumerates the colouring space `2^C(N,2)`:

- `R(3,4)`: `K_9` has `C(9,2)=36` edges → `2^36 ≈ 6.9e10` colourings. Far too many
  for `native_decide` (and for a naive kernel `decide`).
- `R(4,4)`: `K_18` has `C(18,2)=153` edges → `2^153`. Astronomically infeasible.

These need a dedicated search algorithm (backtracking / SAT with symmetry
breaking, e.g. glurak / RamseySat, then a cheap certificate re-checked in Lean)
or a structural Greenwood–Gleason argument. Both are substantially larger
efforts than the enumeration used for `R(3,3)`.

## Next steps (for a follow-up run)

1. Hand pigeonhole proof of R(3,3) ≤ 6 (the acceptance criterion prefers a hand
   argument over enumeration — current file certifies by enumeration, which is a
   valid zero-sorry proof but not the "hand pigeonhole" form).
2. Backtracking certified search for R(3,4)=9 (2^36 pruned by Ramsey structure),
   verified in Lean against the returned witness.
3. R(4,4)=18 via certified SAT/DRAT certificate + Lean checker, or document as a
   dead-end map if toolchain unavailable.
