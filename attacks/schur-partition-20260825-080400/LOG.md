# Attack log — OPE-424 Schur partition FULL statement

**Agent:** Attack Lead `65834f64-b136-424f-a6e0-124f9b6da939`
**Run:** `bbf1ffb0-6da6-4527-aec7-4bb5e688edc9`
**Branch:** `ope/424-schur-partition-full` (base `main`)

## Session 2026-08-25

### Intake
- Wake: `issue_assigned` OPE-424, Director-approved prime post-ES(3)=5 (OPE-422 / Scout OPE-423).
- Hard pins from STATEMENT.md re-read; STATEMENT **not** modified.
- Existing assets: Level A Python cert (OPE-26); Level B Schur.lean n≤12 seed; Schur **not** imported in ProofLab.lean on main.

### Plan chosen
Partial-progress ladder (issue allows):
1. Mathlib-aligned Finset statement (`schurA`/`schurB` on `Nat.Partition`).
2. Extend computable A=B certificate n≤12 → n≤24.
3. Bridge DP ↔ Finset.card for n≤12.
4. Structural lemmas; wire import; lake gates; attack package; PR; hand Reviewer.
5. Do **not** plant universal `sorry`.

### Rejected / deferred
- Full GF product identity in Mathlib PowerSeries (multi-session; heavy).
- Explicit bijection (Bressoud/Andrews style) — multi-session.
- Raising Finset native_decide past 12 — composition Fintype cost.

### Execution notes
- Branch cut from `origin/main` (not scout/ope-423 branch).
- First lean pass failed on list-mem restatement + Bool/Prop mismatch on `%` lemmas; fixed.
- `lake env lean ProofLab/Schur.lean` EXIT=0; `lake build ProofLab` green.
- Level A re-run PASS N=150.
- Axiom print: only propext / Classical.choice / Quot.sound / Lean.ofReduceBool.

### Outcomes
- See RESULTS.md + STATUS.json.
- Full ∀n still open Mathlib gap (consistent with OPE-423 grep).
