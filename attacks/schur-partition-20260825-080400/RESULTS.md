# RESULTS — Schur partition theorem FULL statement (formalize-only)

**Issue:** OPE-424 · **Date:** 2026-08-25 · **Role:** Attack Lead
**Prior:** OPE-26 Level A/B seed · Scout gap re-check OPE-423 · Director prime via OPE-422
**Target:** `schur-partition` · **Claim:** none (default no claim; known-classical formalize-only)

## Theorem (STATEMENT.md pin — unchanged)

For every n ≥ 0: **A(n) = B(n)** where

- **A(n)** = # partitions of n into **distinct** parts ≡ 1 or 2 (mod 3)
- **B(n)** = # partitions of n into parts ≡ 1 or 5 (mod 6) (**reps allowed**)

Hard pins: A(0)=B(0)=1; distinct = multiplicity ≤ 1; **do not swap** pairing (fails at n=2).

## What this attack delivered

### Level A (prior, re-verified) ✅
`attacks/schur-partition-20260804-225016/verify_schur.py --N 150` → **PASS**
- A(n)=B(n) for 0..150; brute cross-check 0..24 PASS; swapped pairing rejected at n=2.

### Level B → B+ (this run) ✅
`proofs/lean-project/ProofLab/Schur.lean` (wired into `ProofLab.lean`)

| Artifact | Content | Gate |
|----------|---------|------|
| Computable `A`/`B` | structural DP counters | unchanged shape from OPE-26 |
| `schur_partition_finite` | `∀ n ≤ 24, A n = B n` | `native_decide`, zero sorry |
| Mathlib Finset defs | `schurA` / `schurB` on `Nat.Partition` | mirrors `odds`/`distincts` style |
| `schur_partition_finset_finite` | `∀ n ≤ 12, (schurA n).card = (schurB n).card` | `native_decide` |
| Bridge | `A n = (schurA n).card` and `B`↔`schurB` for n ≤ 12 | `native_decide` |
| Structural lemmas | nodup/mod filters, B⇒A part shadow, empty mem | sorry-free, all n |
| Full ∀n theorem | **not proved** (no `sorry` stub planted) | residual |

### Lean gate evidence (this run)
```
lake env lean ProofLab/Schur.lean     → EXIT=0
lake build ProofLab                   → "Build completed successfully" (rc=0)
```

### Axiom audit (`#print axioms`, key theorems)
```
schur_partition_finite          : propext, Lean.ofReduceBool
schur_partition_finset_finite   : propext, Classical.choice, Lean.ofReduceBool, Quot.sound
A_eq_schurA_card_le_12          : propext, Classical.choice, Lean.ofReduceBool, Quot.sound
partAllowedB_implies_partAllowedA : propext, Quot.sound
schurA_nodup                    : propext, Classical.choice, Quot.sound
```
No custom axioms. `Lean.ofReduceBool` is the expected `native_decide` kernel certificate.
`Classical.choice` enters via Mathlib `Fintype (Partition n)` / Finset filters.

### Sorry audit
No `sorry` / `admit` / custom `axiom` keywords as code in `Schur.lean` (comment mentions only).

## Level C status — honest

**Full theorem `∀ n, (schurA n).card = (schurB n).card` is NOT closed.**

Deferred routes (Andrews / Schur 1926):
1. Generating-function identity as formal power series over ℤ.
2. Bijective / Glaisher-style map on partitions.
3. Recurrence + uniqueness of partition GFs.

Deliberately **no `sorry` placeholder** for the universal statement (avoids zero-sorry gate failure and over-claim).

## Residual risks
1. Finite Lean certificates only (n≤24 computable / n≤12 Finset) — not a proof for all n.
2. Finset `native_decide` bound capped by composition Fintype (`2^(n-1)`); raising past ~12 is expensive.
3. No bijective/GF proof formalized.
4. Full default `lake build` exe link may still hit Windows cmdline-length (pre-existing); **library target green**.
5. No external claim (board-only).

## Verify commands
```bash
# Level A
python attacks/schur-partition-20260804-225016/verify_schur.py --N 150

# Level B+
cd proofs/lean-project
lake env lean ProofLab/Schur.lean     # expect EXIT=0
lake build ProofLab                    # expect Build completed successfully
```

## Disposition
Partial-progress ladder complete for OPE-424 budget.
**OPE-426 Adversarial Review (2026-08-25): WRITTEN APPROVAL of partial ladder only.**
Parent OPE-424 closed **done** for the finite-certificate deliverable (not the full theorem).
Promote to `formalized` only when universal `schur_partition` lands zero-sorry.
