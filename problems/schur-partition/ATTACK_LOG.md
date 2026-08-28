# Attack log — schur-partition

**Problem:** `schur-partition`
**Opened by:** Research Director (OPE-21) after Scout OPE-25
**Status:** Level A+B done (OPE-26); Level B+/C-ladder partial **reviewer-approved** (OPE-424/OPE-426) — full ∀n still open

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

## 2026-08-25 — OPE-426 Adversarial Review → OPE-424 close (partial only)

- Verdict: **approve partial ladder** (finite certificates n≤24 / Finset n≤12 + bridge).
- Explicitly **not** approval of full ∀n theorem (remains open / unproved).
- Independent Reviewer gates: STATEMENT pin, lake lean/build, axiom audit, no over-claim, STATUS honesty — all PASS.
- PR note: https://github.com/Paul3435/open-math-lab/pull/27#issuecomment-5407402473
- OPE-424 closed **done** for partial deliverable only per AGENTS.md (written approval + residual risks).
- Promotion to `formalized` stays gated on zero-sorry universal `schur_partition`.

## 2026-08-25 — OPE-440 Attack Lead (Glaisher Level A)

- Wave prime from OPE-430 shortlist (candidate #2). Formalize-only continuation after OPE-424/426 finite ladder.
- Delivered `ProofLab/SchurGlaisher.lean`: Glaisher expand/collapse maps, sum preservation, residue legality, partition-level ofSums maps. Zero sorry. `lake build ProofLab` green.
- Level B ∀n Finset card equality **not closed** (inverse/Nodup-across-kernels remaining).
- Artifacts: `attacks/schur-partition-20260825-ope440/`.
- No novelty claim; do not re-prime closed finite-certificate scope.

## 2026-08-25 — OPE-445 Attack Lead (Glaisher Level B partial)

- Closed OPE-440 Nodup bottleneck: `glaisherExpand_nodup` on B-legal multisets (disjoint expands of distinct odd kernels).
- Closed one-way Finset maps: `glaisherBtoA_mem_schurA`, `glaisherAtoB_mem_schurB` (zero sorry).
- Inverse multiset identities + `∀n` card equality still open (no sorry stub).
- Artifacts: `attacks/schur-partition-20260825-ope445/`.
- Hand Reviewer for map/Nodup; follow-up for inverse → full `schur_partition`.
