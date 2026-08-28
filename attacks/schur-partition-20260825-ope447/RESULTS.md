# RESULTS — Schur partition Level C Glaisher inverses + ∀n card (OPE-447)

**Issue:** OPE-447 · **Date:** 2026-08-25 · **Role:** Attack Lead
**Prior:** OPE-445 Level B maps/Nodup · OPE-440 Level A infra
**Target:** `schur-partition` · **Claim:** none (formalize-only / known-classical Schur 1926)

## Theorem pin (STATEMENT.md 2026-08-04 — unchanged)

For every n ≥ 0: **A(n) = B(n)** where
- **A(n)** = # partitions of n into **distinct** parts ≡ 1 or 2 (mod 3)
- **B(n)** = # partitions of n into parts ≡ 1 or 5 (mod 6) (**reps OK**)

## Scope delivered this run

### Level C — zero sorry

Extended `proofs/lean-project/ProofLab/SchurGlaisher.lean`:

| Artifact | Content |
|----------|---------|
| `bind_collapse_expandPart_pow` / `bind_collapse_expandPart` | collapse∘expand on one odd kernel recovers multiplicities |
| `dedup_bind_replicate_count` | multiset rebuild from counts |
| **`glaisherCollapse_glaisherExpand`** | B-legal: collapse∘expand = id |
| `mem_bitIndices_iff_testBit` / `testBit_sum_two_pow_finset` | bit support of ∑ 2^i |
| `kernelExponents` + count/testBit formulas | collapse multiplicity bits |
| `mem_glaisherExpand_iff_bit` | expand membership via oddPart/val2 bits |
| **`glaisherExpand_glaisherCollapse`** | Nodup A-legal: expand∘collapse = id |
| `glaisherAtoB_parts_eq` / `glaisherBtoA_parts_eq` | ofSums parts equality |
| **`glaisherBtoA_AtoB_eq` / `glaisherAtoB_BtoA_eq`** | partition-level inverses |
| **`schur_partition`** | `∀ n, (schurA n).card = (schurB n).card` via `Finset.card_bij'` |

### Prior retained (OPE-445 / OPE-440)

Nodup expand, one-way Finset maps, sum preservation, oddPart/val2/expandPart infrastructure.

## Lean gates (this run)

```
lake env lean ProofLab/SchurGlaisher.lean  → EXIT=0
lake build ProofLab                        → Build completed successfully
```

Sorry audit: no `sorry` / `admit` / custom `axiom` in Schur.lean or SchurGlaisher.lean
(comment mentions only).

## Residual risks

1. formalize-only / known classical — no novelty; default no external claim.
2. Pairing pin must stay STATEMENT.md 2026-08-04 (do not swap A/B constraints).
3. Finite certificates (n≤24/12) in Schur.lean remain independent computational ladder.
4. Reviewer should spot-check inverse hypotheses (B-legal / Nodup A-legal) match Finset filters.

## Verify

```bash
cd proofs/lean-project
export PATH="$HOME/.elan/bin:$PATH"
lake env lean ProofLab/Schur.lean
lake env lean ProofLab/SchurGlaisher.lean
lake build ProofLab
```

## Disposition

**Done:** Level C inverses + `schur_partition` closed zero-sorry; lake build green.
Hand to Adversarial Reviewer for map/inverse review; no claim packet.
