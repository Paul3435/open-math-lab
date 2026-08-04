# Board notes (Paul)

## 2026-07-30 — Workspace split (critical)

Agents often wrote under Paperclip managed project folder:

`~/.paperclip/instances/default/projects/<company>/<project>/_default`

instead of the git SoT:

`C:\Users\paulb\Documents\VSCode\open-math-lab`

**Policy:** git repo is source of truth. Managed folder is a cache/mirror. Board synced attack/skill/proof/docs into git on 2026-07-30. Project workspace must be `local_path` → open-math-lab. Prefer `--force-fresh-session` after workspace fix.

## 2026-07-30 — OPE-12 Erdős–Woods claim VETO

Attack Lead + Reviewer accepted witness **a=5** under a **wrong definition** (XOR of primes ≤ k distinguishing i from a).

**Standard definition:** k is Erdős–Woods if ∃ a such that every integer in **(a, a+k)** shares a prime factor with **a or a+k** (the endpoints). Canonical first example: **k=16, a=2184**.

OPE-12 “solved” status is **not** a valid mathematical claim for the lab. Treat as failed calibration / definition bug. Correct literature fact remains: 16 is EW with minimal a=2184.

## Sum-free (OPE-14)

Classical Erdős result (every n-set has sum-free subset size ≥ n/3). Computational experiments + partial Lean with `sorry` are process demos, not novel research. Disposition: adversarial review of artifacts as **known theorem / formalize-partial**; do not claim discovery.

## 2026-07-31 — Lean install APPROVED

Board (Paul) approved user-local **elan + Lean 4 + lake** install and first `lake build` of `proofs/lean-project`. Ticket: Formalist OPE install issue. Still no external claims without board.

## 2026-08-04 — OPE-21 next sprint (Director)

- **Problem ledger** added: `docs/PROBLEM_LEDGER.md` (canonical handled-history).
- Catalog README + `catalog/problems.json` corrected (removed stale “EW solved a=5” completion claim from catalog prose).
- **Process breach (board call-out):** Director first picked frobenius from catalog scores without a fresh Scout shortlist. Corrected via **OPE-25** Scout run + portfolio “Scout shortlist gate” docs.
- **OPE-25 Scout result:** frobenius / derangement / catalan already in Mathlib on v4.10.0 pin — demote as gap primes. **Recommended prime: `schur-partition`** (genuine Mathlib gap).
- **Director decision:** Approve OPE-25 shortlist. Frobenius **OPE-22** continues as **process-fuel only**. Schur is the next real formalization attack; STATEMENT pinned (distinct parts ≡1,2 mod 3 vs parts ≡±1 mod 6 — earlier draft had sides wrong).
- OPE-14 sum-free remains classical/informal; graceful caterpillars remain heuristic sanity check.
- Wake discipline unchanged: one specialist at a time (finish OPE-22, then Schur).
