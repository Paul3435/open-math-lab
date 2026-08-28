# Attack log — ramsey-r35

| when | agent | strategy | result |
|------|-------|----------|--------|
| 2026-08-24 | Attack Lead (OPE-393) | Pin STATEMENT.md; lower = circulant C₁₃({±1,±5}) certified by `native_decide`; upper = classical recurrence R(3,5)≤R(2,5)+R(3,4)=5+9 via new `ramsey_two_right` + existing `ramsey34_le_9` / `ramseyUpper_add` | **CLOSED.** `ramsey35_eq_14` = (`ramsey35_gt_13`, `ramsey35_le_14`). `not_ramsey35_13` zero-sorry on Fin 13 witness (no red K3 / no blue K5). `lake env lean ProofLab/Ramsey.lean` exit 0; `lake build ProofLab` green. formalize-only; **no claim**. |

## Status — acceptance checklist

1. **STATEMENT.md pinned** before Lean close — `problems/ramsey-r35/STATEMENT.md` (+ catalog mirror). DONE.
2. **Reuse `ProofLab/Ramsey.lean` vocabulary** (`HasClique`, `RamseyUpper`) — no fork. DONE.
3. **R(3,5)>13** — `not_ramsey35_13` / `ramsey35_gt_13` via circulant witness. Zero sorry. DONE.
4. **R(3,5)≤14** — `ramsey35_le_14` via `ramsey_two_right 5` + `ramsey34_le_9` + `ramseyUpper_add`. Zero sorry. DONE.
5. **Equality package** — `ramsey35_eq_14`. DONE.
6. **`lake build ProofLab` green**; no sorry/admit/axiom in the new block. DONE.
7. ATTACK_LOG + ledger + catalog + PR. DONE this entry.

## Residual risks (board-facing, no claim)

- **Formalize-only / known-classical** (Greenwood–Gleason 1955). Value is the Lean certificate, not novelty. Default **no claim**.
- **API remains lab-local** (`ProofLab.Ramsey`); not packaged as an upstream Mathlib PR.
- **Upper bound is the classical recurrence**, not a fresh hand degree-count on K₁₄. Logically equivalent to the Scout note (degree/recurrence family); if board wants an independent degree-only writeup that is optional docs, not a math gap.
- **Witness uniqueness / classification** of the critical 13-vertex colouring is **not** proved — only existence of one valid colouring.
- Pre-existing linter warnings in older R(3,3)/transfer blocks are unchanged.
