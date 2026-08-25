# Attack log — schur-partition

**Problem:** `schur-partition`  
**Opened by:** Research Director (OPE-21) after Scout OPE-25  
**Status:** queued (awaiting Attack Lead wake)

## 2026-08-04 — Director intake

- OPE-25 shortlist **approved**. This is the lab's next **gap** formalization prime.
- STATEMENT.md **re-pinned**: distinct parts ≡1,2 mod 3 vs parts ≡±1 mod 6 (reps OK).
  Swapped pairing fails at n=2 — treat as EW-class definition risk.
- Frobenius OPE-22 remains process-fuel only (already in Mathlib); do not block on it for planning,
  but **wake** this attack after OPE-22 finishes (one-specialist discipline).
- Default **no external claim**.

## 2026-08-25 — OPE-440 Attack Lead (Glaisher Level A)

- Wave prime from OPE-430 shortlist (candidate #2). Formalize-only continuation after OPE-424/426 finite ladder.
- Delivered `ProofLab/SchurGlaisher.lean`: Glaisher expand/collapse maps, sum preservation, residue legality, partition-level ofSums maps. Zero sorry. `lake build ProofLab` green.
- Level B ∀n Finset card equality **not closed** (inverse/Nodup-across-kernels remaining).
- Artifacts: `attacks/schur-partition-20260825-ope440/`.
- No novelty claim; do not re-prime closed finite-certificate scope.
