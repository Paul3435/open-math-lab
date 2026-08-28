# Attack log — erdos-szekeres-monotone

| when | agent | strategy | result |
|------|-------|----------|--------|
| 2026-08-25 | Attack Lead (OPE-433) | Classic (a_i,b_i) length-labelling + pigeonhole; weak mono via List.Sorted; Finset ending-sets + Fintype.card_le_of_injective | **CLOSED.** `erdosSzekeres_monotone` + `erdosSzekeres_card_bound` zero-sorry in `ProofLab/ErdosSzekeres.lean`. `lake env lean ProofLab/ErdosSzekeres.lean` EXIT=0; wired into `ProofLab.lean`. formalize-only; **no claim**. |
| 2026-08-25 | Attack Lead (OPE-437) | Duplicate commission of same Scout prime; no re-proof | **CLOSED as duplicate of OPE-433.** Re-verified `lake env lean` EXIT=0 + `lake build ProofLab` green + zero sorry. PR #29 still open. Spawned **OPE-438** Adversarial Reviewer handoff. |

## Status — acceptance checklist

1. **STATEMENT.md pin** — weak monotonicity (`≤` / `≥`), List.Sorted subsequences, distinctness not required. DONE.
2. **Lean theorem** — `erdosSzekeres_monotone` over `LinearOrder` + `Fin n`. DONE.
3. **Zero sorry/admit/custom axiom** in `ProofLab/ErdosSzekeres.lean`. DONE.
4. **`lake env lean` EXIT=0** on the module; import from `ProofLab.lean`. DONE (module); full `lake build ProofLab` this run.
5. **Attack log + STATUS + ledger/catalog update**. DONE this close.
6. **No novelty claim**; known-classical formalize-only. DONE.

## Residual risks (board-facing, no claim)

- **Formalize-only / known-classical (1935).** Value is the Mathlib-gap formalization.
- **API is lab-local** (`ProofLab.ErdosSzekeres`), not upstream Mathlib PR packaging.
- **Weak form only** — strict monotone under distinctness not separately stated (follows for free when values are pairwise distinct via `Sorted.lt_of_le` + nodup, but not packaged).
- **Classical noncomputable lengths** via `Finset.sup` over `Finset (Fin n)` (proof-relevant only; no certified search).
- Subsequence witness is a `List α` of values, not an explicit index list in the theorem statement (indices are internal via `valuesOf` / ending sets).

## Handoff

- **Handoff to:** Adversarial Reviewer via **OPE-438** (statement pin + zero-sorry + edge cases).
- **PR:** https://github.com/Paul3435/open-math-lab/pull/29 — branch `ope/433-erdos-szekeres-monotone` (board merges).
