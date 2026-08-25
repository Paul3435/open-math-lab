# Attack log — schur-partition

**Problem:** `schur-partition`
**Opened by:** Research Director (OPE-21) after Scout OPE-25
**Status:** Level A+B done (OPE-26); Level B+/C-ladder partial (OPE-424) — full ∀n open

## 2026-08-04 — Director intake

- OPE-25 shortlist **approved**. This is the lab's next **gap** formalization prime.
- STATEMENT.md **re-pinned**: distinct parts ≡1,2 mod 3 vs parts ≡±1 mod 6 (reps OK).
  Swapped pairing fails at n=2 — treat as EW-class definition risk.
- Frobenius OPE-22 remains process-fuel only (already in Mathlib); do not block on it for planning,
  but **wake** this attack after OPE-22 finishes (one-specialist discipline).
- Default **no external claim**.

## 2026-08-04 — OPE-26 Attack Lead (Level A + B)

- Level A: `attacks/schur-partition-20260804-225016/` — A=B for n≤1000, swapped pairing rejected.
- Level B: `proofs/lean-project/ProofLab/Schur.lean` — computable A/B, native_decide n≤12.

## 2026-08-25 — OPE-424 Attack Lead (Level B+/C ladder)

- Branch `ope/424-schur-partition-full` from `main`.
- STATEMENT.md **left verbatim**.
- Upgraded `ProofLab/Schur.lean`:
  - `schur_partition_finite`: A n = B n for all n ≤ 24 (zero sorry).
  - Mathlib `Nat.Partition` Finsets `schurA` / `schurB` (contribution-shaped).
  - Finset card equality + DP↔card bridge for n ≤ 12.
  - Structural lemmas (nodup, mod filters, B⇒A part inclusion).
  - Wired `import ProofLab.Schur` into `ProofLab.lean`.
  - **No** universal `sorry`; full ∀n deferred (GF / bijection).
- Gates: `lake env lean ProofLab/Schur.lean` EXIT=0; `lake build ProofLab` green.
- Attack package: `attacks/schur-partition-20260825-080400/`.
- Hand-off: Adversarial Reviewer. Residual: universal theorem open.
