# RESULTS — Van der Waerden W(2,4)=35 formalize-only (OPE-455)

**Issue:** OPE-455 · **Date:** 2026-08-25 · **Role:** Attack Lead  
**Prior:** Scout OPE-430 bench; Director OPE-454 ratify  
**Target:** `van-der-waerden-w24` · **Claim:** none (formalize-only / known-classical)

## Theorem pin (STATEMENT.md)

- `W(2,4)` = least `N` s.t. every 2-colouring of `{1,…,N}` has a monochromatic 4-AP.
- Classical value 35 (Chvátal 1979, computer-assisted upper bound).
- Lean encoding: `f : Fin n → Bool`; 4-AP = `a,a+d,a+2d,a+3d` with `d>0`.

## Scope delivered — PARTIAL ladder

| Half | Status | Artifact |
|------|--------|----------|
| **Lower bound `W(2,4) > 34`** | **Proved, zero sorry** | `vdw24_gt_34` |
| **Upper bound `W(2,4) ≤ 35`** | **Not proved** (timebox / hard stop) | — |

Honest label: **partial** — only the certified lower-bound witness half of `W(2,4)=35`.

### What is proved

In `proofs/lean-project/ProofLab/VanDerWaerden.lean`:

- `HasMono4` — decidable monochromatic 4-AP predicate (carry-over of `HasMono3`).
- `witness34` / `witness34Mask = 14783751620` — 2-colouring of `Fin 34` with string
  `0010001110100100011101001000111011` (bit `i` = colour of position `i`).
- **`vdw24_gt_34 : ¬ HasMono4 witness34`** via `native_decide` on the **single** fixed
  colouring (not an enumeration of `2^34` colourings).

Retained closed W(2,3)=9 results: `vdw_le_9`, `vdw_gt_8`.

### What is NOT proved

- `∀ f : Fin 35 → Bool, HasMono4 f` (`W(2,4) ≤ 35`).
- Literature upper bound is computer-assisted; `native_decide` cannot scale to `2^35`.
- Hand case-analysis / SAT-certificate import deferred (budget hard stop).
- Exact equality `W(2,4) = 35` therefore remains open in Lean.

### Offline witness search

Pruned backtrack (Python) found the length-34 colouring in <1s; full AP scan verified
before Lean import. Script: `attacks/van-der-waerden-w24-20260825-ope455/search_witness34.py`.

## Lean gates (this run)

```
lake env lean ProofLab/VanDerWaerden.lean  → EXIT=0
lake build ProofLab                        → Build completed successfully
```

### `#print axioms` audit

```
vdw_le_9      : propext, Classical.choice, Lean.ofReduceBool, Quot.sound
vdw_gt_8      : propext, Lean.ofReduceBool, Quot.sound
vdw24_gt_34   : propext, Lean.ofReduceBool, Quot.sound
```

No `sorry` / `admit` / custom axioms in `VanDerWaerden.lean` (comment mentions only).

## Residual risks

1. formalize-only / known classical — **no novelty**; default no external claim.
2. Upper half still open — do not market as full `W(2,4)=35` Lean close.
3. Witness is one of many classical free colourings; mask must stay bit-aligned with STATEMENT string.
4. Concurrent lab branches (e.g. Schur Glaisher OPE-447) may touch `ProofLab.lean` imports — merge carefully.

## Verify

```bash
cd proofs/lean-project
export PATH="$HOME/.elan/bin:$PATH"
lake env lean ProofLab/VanDerWaerden.lean
lake build ProofLab
```

## Disposition

**Partial done:** lower bound `W(2,4) > 34` zero-sorry; STATEMENT pinned; lake build green.  
Upper bound left for a follow-up if Director budgets hand/certificate work.  
Hand to Adversarial Reviewer for witness/predicate review; **no claim packet**.
