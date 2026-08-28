# RESULTS — Schur partition Level B Glaisher maps (OPE-445)

**Issue:** OPE-445 · **Date:** 2026-08-25 · **Role:** Attack Lead
**Prior:** OPE-440 Level A Glaisher infra · OPE-424/426 finite ladder
**Target:** `schur-partition` · **Claim:** none (formalize-only / known-classical Schur 1926)

## Theorem pin (STATEMENT.md 2026-08-04 — unchanged)

For every n ≥ 0: **A(n) = B(n)** where
- **A(n)** = # partitions of n into **distinct** parts ≡ 1 or 2 (mod 3)
- **B(n)** = # partitions of n into parts ≡ 1 or 5 (mod 6) (**reps OK**)

## Scope delivered this run

### Level B (partial) — zero sorry

Extended `proofs/lean-project/ProofLab/SchurGlaisher.lean` (OPE-440 base retained):

| Artifact | Content |
|----------|---------|
| `B_part_odd/pos/mod3` | B-kernels are odd, positive, ≡1 or 2 mod 3 |
| `expandPart_pos` / `oddPart_expand` | expand parts positive; odd kernel recovered |
| `count_expandPart_pow` | bit-count of expandPart at `m*2^i` |
| `count_collapsePart` | collapse multiplicity formula |
| `expandPart_disjoint_of_ne_odd` | distinct odd kernels → disjoint expands |
| **`glaisherExpand_nodup`** | B-legal multisets expand to **Nodup** (main OPE-440 bottleneck) |
| `glaisherExpand_pos` / `ofSums_parts_eq_of_pos` | ofSums drops no parts on positive multisets |
| **`glaisherBtoA_mem_schurA`** | `p ∈ schurB n → glaisherBtoA_parts p ∈ schurA n` |
| **`glaisherAtoB_mem_schurB`** | `p ∈ schurA n → glaisherAtoB_parts p ∈ schurB n` |

### Still open for full `∀n` card equality

1. `glaisherCollapse ∘ glaisherExpand = id` on B-legal multisets (binary reconstruction of multiplicities).
2. `glaisherExpand ∘ glaisherCollapse = id` on Nodup A-legal multisets.
3. `Finset.card_bij'` / `schur_partition : ∀ n, (schurA n).card = (schurB n).card`.

No `sorry` stub planted for the universal theorem.

Python oracle (prior OPE-440): Glaisher bijection verified n=0..30; Level A DP certificate N≤150 still green.

## Lean gates (this run)

```
lake env lean ProofLab/SchurGlaisher.lean  → EXIT=0
lake build ProofLab                        → Build completed successfully
```

Sorry audit: no `sorry` / `admit` / custom `axiom` in Schur.lean or SchurGlaisher.lean.

## Residual risks

1. Full ∀n identity still open — maps land in the correct Finsets and B→A is Nodup, but inverses not proved.
2. Binary bit-sum inverse is the remaining Lean bottleneck (not the cross-kernel Nodup issue from OPE-440).
3. Finite certificates (n≤24/12) remain closed OPE-424 scope — do not re-prime as full theorem.
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

**Partial progress:** Level B one-way Finset maps + Nodup closed zero-sorry; inverse/card open.
Hand to Adversarial Reviewer for map/Nodup review; follow-up attack for inverse → `schur_partition`.
