# RESULTS — Schur partition FULL via Glaisher (OPE-440)

**Issue:** OPE-440 · **Date:** 2026-08-25 · **Role:** Attack Lead
**Prior:** OPE-26 seed · OPE-424/426 finite ladder (Adversarial-approved) · Scout OPE-430 prime
**Target:** `schur-partition` · **Claim:** none (formalize-only / known-classical Schur 1926)

## Theorem pin (STATEMENT.md 2026-08-04 — unchanged)

For every n ≥ 0: **A(n) = B(n)** where
- **A(n)** = # partitions of n into **distinct** parts ≡ 1 or 2 (mod 3)
- **B(n)** = # partitions of n into parts ≡ 1 or 5 (mod 6) (**reps OK**)

Hard pins: A(0)=B(0)=1; never swap pairing (fails at n=2).

## Scope delivered this run

### Level A (Glaisher infrastructure) ✅ — zero sorry

New module: `proofs/lean-project/ProofLab/SchurGlaisher.lean` (wired into `ProofLab.lean`)

| Artifact | Content |
|----------|---------|
| `oddPart` / `val2` | recursive 2-adic peel; `oddPart_mul_pow`, oddness, B-kernel residue |
| `expandPart m c` | binary Glaisher expand of multiplicity c at kernel m |
| `collapsePart p` | reverse: `2^val2 p` copies of `oddPart p` |
| `sum_expandPart` / `sum_collapsePart` | sum preservation (induction) |
| `expandPart_nodup_of_pos` | Nodup when m > 0 |
| `expandPart_mem_mod3` / `collapsePart_mem_B` | residue legality |
| `glaisherExpand` / `glaisherCollapse` | Multiset-level maps |
| `sum_glaisherExpand` / `sum_glaisherCollapse` | sum preservation |
| `glaisherBtoA_parts` / `glaisherAtoB_parts` | `Nat.Partition` sum-preserving maps via `ofSums` |

Python oracle (this run): Glaisher bijection verified for n=0..30 against full enumeration of A/B.

### Level B (∀n card equality) ❌ — not closed

**Missing for full `schur_partition`:**
1. Prove `glaisherExpand` is Nodup on B-legal multisets (unique odd factorization across kernels).
2. Prove `glaisherBtoA_parts p ∈ schurA n` when `p ∈ schurB n` (and reverse).
3. Prove the two partition maps are inverses on the Finset subtypes.
4. Conclude `(schurA n).card = (schurB n).card` via `Finset.card_congr` / `Equiv`.

No `sorry` stub planted for the universal theorem (same discipline as OPE-424).

### Prior ladder retained (OPE-424 content landed on branch)

`ProofLab/Schur.lean` from OPE-424: computable A/B through n≤24; Finset cards n≤12 + bridge; structural lemmas.

## Lean gates (this run)

```
lake env lean ProofLab/Schur.lean          → EXIT=0
lake env lean ProofLab/SchurGlaisher.lean  → EXIT=0
lake build ProofLab                         → Build completed successfully (rc=0)
```

Sorry audit: no `sorry` / `admit` / custom `axiom` in Schur.lean or SchurGlaisher.lean.

## Residual risks

1. Full ∀n identity still open — Glaisher maps are sum-preserving and residue-correct but not yet shown bijective on Finset subtypes.
2. Multiset.bind Nodup across distinct odd kernels is the main remaining Lean bottleneck.
3. Finite certificates only (n≤24/12) for card equality remain the closed OPE-424 scope — do not re-prime as full theorem.
4. No external claim.

## Verify

```bash
python attacks/schur-partition-20260804-225016/verify_schur.py --N 150
cd proofs/lean-project
export PATH="$HOME/.elan/bin:$PATH"
lake env lean ProofLab/Schur.lean
lake env lean ProofLab/SchurGlaisher.lean
lake build ProofLab
```

## Disposition

**Partial progress:** Level A Glaisher infrastructure landed zero-sorry; Level B open.
Hand to Adversarial Reviewer for infrastructure review; follow-up attack for inverse/card.
