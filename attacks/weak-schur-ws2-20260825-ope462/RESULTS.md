# RESULTS — Weak Schur WS(2)=8 formalize-only (OPE-462)

**Issue:** OPE-462 · **Date:** 2026-08-25 · **Role:** Attack Lead  
**Prior:** Scout OPE-458 #2; Director OPE-460 secondary formalize  
**Target:** `weak-schur-ws2` · **Claim:** none (formalize-only / known-classical)

## Theorem pin (STATEMENT.md)

- `WS(2)` = largest `n` s.t. `{1,…,n}` admits a 2-colouring with no mono
  `x+y=z` under **`x ≠ y`** (weak Schur / weakly sum-free).
- Classical value **8** (Abbott–Wang / Exoo).
- Lean encoding: `f : Fin n → Fin 2`; position `i` ↔ integer `i.val+1`.
- Distinctness pin: `x ≠ y` only; `z=x+y` auto-differs since `x,y≥1`.
- Not strong Schur `S(k)` and not `schur-partition`.

## Scope delivered — FULL single-level close

| Half | Status | Artifact |
|------|--------|----------|
| **Lower `WS(2) ≥ 8`** | **Proved, zero sorry** | `ws2_gt_7` |
| **Upper `WS(2) ≤ 8`** | **Proved, zero sorry** | `ws2_le_8` (`2^9=512` enum) |
| **Equality `WS(2) = 8`** | **Proved, zero sorry** | `ws2_eq_8` |

### What is proved

In `proofs/lean-project/ProofLab/WeakSchur.lean`:

- `HasMonoWeakSchur` — decidable monochromatic weak-Schur predicate
  (`x ≠ y`, Fin-offset sum `x.val+y.val+1`).
- `witnessWS2` — classes `{1,2,4,8}` / `{3,5,6,7}` (bitstring `00101110`).
- **`ws2_gt_7`**, **`ws2_le_8`**, **`ws2_eq_8`** via `native_decide` /
  conjunction; no heuristic search.

### Offline boundary check (pre-Lean)

Exhaustive Python scan: `[1..n]` 2-colourable under weak predicate iff
`n ≤ 8`. Exactly two complementary valid colourings of length 8:
`00101110`, `11010001`. Script notes in `LOG.md`.

## Lean gates (this run)

```
lake env lean ProofLab/WeakSchur.lean  → EXIT=0
lake build ProofLab                    → Build completed successfully
```

### `#print axioms` audit

```
ws2_gt_7 : propext, Lean.ofReduceBool, Quot.sound
ws2_le_8 : propext, Classical.choice, Lean.ofReduceBool, Quot.sound
ws2_eq_8 : propext, Classical.choice, Lean.ofReduceBool, Quot.sound
```

No `sorry` / `admit` / custom axioms.

## Residual risks

- Indexing convention must stay pinned (`{1..n}` via Fin+1). Flipping to
  0-based equations silently changes the number.
- Strong-Schur `HasMonoSchur` (x=y allowed) is a **different** predicate;
  do not cite `ws2_*` as S(2) results.
- No novelty / external claim. Default `mathforge claim prepare` → no claim.

## Hygiene

- STATEMENT: `problems/weak-schur-ws2/STATEMENT.md`
- Lean: `proofs/lean-project/ProofLab/WeakSchur.lean` (+ `ProofLab.lean` import)
- Catalog/ledger: status → `in_progress` then formalize close on PR merge
- PR: one PR base `main`; board merges
