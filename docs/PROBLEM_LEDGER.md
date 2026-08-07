bash.exe: warning: could not find /tmp, please create!
# Problem ledger — Open Math Lab

Source of truth for **which mathematical bets we have touched**, their disposition,
and pointers to artifacts. Update this file whenever a problem changes lifecycle
status. Catalog index: `catalog/problems.json`. Feasibility dossiers live under
`catalog/problems/<id>/` and/or `problems/<id>/`.

**Last updated:** 2026-08-04 (OPE-21 Director: approve OPE-25 shortlist; Schur STATEMENT pin)

## Lifecycle labels

| Label | Meaning |
|-------|---------|
| `seed` | Placeholder / demo only — not a research bet |
| `candidate` | Scouted; not yet under active attack |
| `shortlisted` | Director approved for attack |
| `in_progress` | Attack or formalization running |
| `in_review` | Adversarial review gate |
| `heuristic` | Bounded compute / informal evidence only — **not** a proof |
| `informal` | Correct classical math + process artifacts; Lean incomplete or absent |
| `vetoed` | Claim or definition rejected (keep artifacts as calibration) |
| `formalized` | Lean-checked statement+proof (or certified compute) green |
| `archived` | Superseded, already-in-Mathlib, or intentionally dropped |

## Handled so far (touched by tickets)

| Problem ID | Domain | Tickets | Disposition | Novelty | Primary artifacts |
|------------|--------|---------|-------------|---------|-------------------|
| `erdos-woods` | elem. number theory | OPE-12 attack; OPE-15 hygiene veto | **`vetoed` claim** (wrong def / a=5). Literature fact k=16, a=2184 remains valid **candidate** for *correct* formalization | Known (1980) | `problems/erdos-woods/`, `attacks/erdos-woods-20260730-125506/` (+ BOARD_VETO) |
| `sum-free-subsets` | additive combinatorics | OPE-14 (board may still be open) | **Classical Erdős (1965)** process demo. Compute OK; Lean had sorry + strategy mismatch at review. Status: **`informal` / not claim-ready**. Do not treat as discovery | Known theorem | `problems/sum-free-subsets/`, `attacks/sum-free-subsets-20260730-221216/`, Lean `ProofLab/SumFree.lean` |
| `graceful-tree-conjecture` (bounded caterpillars n≤12) | graph theory | OPE-13 attack; OPE-18 review; OPE-20 re-review | **`heuristic`** bounded verify: 560 distinct non-iso caterpillars, 0 search failures after dedup. Family already known graceful for all n (Rosa/Golomb). **Not** full GTC; **not** Lean-gated | Sanity check, not new math | `problems/graceful-tree-conjecture/`, `attacks/graceful-tree-conjecture-20260731-094627/` |
| `schur-partition` | partitions | OPE-2 seed; OPE-25 shortlist; OPE-21 Director approve | **`shortlisted` prime** — STATEMENT pin 2026-08-04 (distinct parts ≡1,2 mod 3 = parts ≡±1 mod 6). Attack child filed after approval. Formalize-only | Known (1926); **genuine Mathlib gap** (OPE-25 grep) | `problems/schur-partition/` |
| `frobenius-coin-problem` | number theory | OPE-21/22; OPE-25 | **process-fuel** (not gap prime). Mathlib already has `frobeniusNumber_pair`. Level A/B artifacts under attack dir + `ProofLab/Frobenius.lean` | Known textbook; already-in-Mathlib | `problems/frobenius-coin-problem/`, `attacks/frobenius-coin-problem-20260804-222513/` |

## Pipeline / infrastructure (not math bets)

| Work | Tickets | Notes |
|------|---------|-------|
| mathforge scaffold, rubric, catalog, CLI | OPE-1…OPE-11, OPE-9 | Tooling for triage + attack logs |
| Lean 4 + elan + lake build | OPE-17 (board OK) | Toolchain green; claims still board-gated |
| Workspace SoT + GitHub PR workflow | OPE-16, docs | Git SoT: `Documents/VSCode/open-math-lab` |
| Review checklist + claim gates | OPE-10, OPE-5 | `docs/REVIEW_CHECKLIST.md`, `docs/CLAIM_POLICY.md` |

## Untouched / catalog candidates (Scout refreshed — OPE-25)

**OPE-21 process breach corrected by OPE-25.** Only genuine Mathlib-gap scores survive.
`frobenius`, `derangement`, `catalan` were scored on false "Mathlib gap" assumptions and are
already covered upstream; `schur-partition` is the only confirmed gap among prior candidates.

| Problem ID | Status | Domain | Notes |
|------------|--------|--------|-------|
| **`schur-partition`** | **shortlisted — Director APPROVED prime (OPE-21)** | partition theory | OPE-25 recommended; Director approved. STATEMENT pinned (distinct ≡1,2 mod 3 vs parts ≡±1 mod 6). **OPE-26** attack filed (`todo`, blockedBy OPE-22 for wake order). |
| `frobenius-coin-problem` | shortlisted (process-fuel only) / in_progress OPE-22 | number theory | **SUPERSEDED as gap prime** — already in Mathlib. OPE-22 = compute cert + Lean practice only. |
| `derangement-formula` | candidate (demoted) | enum. combinatorics | ALREADY in Mathlib (`numDerangements` + sum/recurrence/asymp). Dossier gap claim false. Lean-practice only. |
| `catalan-recurrence` | candidate (demoted) | enum. combinatorics | ALREADY in Mathlib (`catalan`, recurrence, centralBinom closed form). Lean-practice only. |
| `bertrand-postulate-computational` | candidate (demoted) | computational NT | General theorem already in Mathlib; certificate-only value, low contribution. |

Placeholders: `demo-collatz-bound-toy` (demo only). **Seed placeholders `oeis-finite-check-candidate` and
`mathlib-gap-candidate` REPLACED by Scout 2026-08-07** with two novelty-pre-screened, finitary, decidable,
Mathlib-gap candidates: **`ramsey-r33`** (finite graph Ramsey R(3,3)=6 / R(4,4)=18) and **`schur-number`**
(Schur S(2)/S(3)). Both `expected: known-classical` → **formalize-only** (genuine Mathlib contribution; do NOT
re-fund as novel). Dossiers + feasibility under `catalog/problems/<id>/` and `problems/<id>/`.
`erdos-woods` correct-formalization (k=16,a=2184) remains a valid future candidate.
Previous Scout keep-fresh: **`van-der-waerden-w23`** — finitary Van der Waerden W(2,3)=9, explicit Mathlib TODO
(HalesJewett.lean L50-53), `formalize-only` (overall 5.0).

## Active sprint (from OPE-21)

| Bet | Issue | Owner role | Intent |
|-----|-------|------------|--------|
| `frobenius-coin-problem` | **OPE-22** (child of OPE-21) | Attack Lead | Process-fuel only (OPE-25): Level A/B practice; **no claim**. Close when Attack Lead finishes PR + residual risks; optional Reviewer only if someone proposes claim language (they should not). |
| Scout shortlist / ratify | **OPE-25** (child of OPE-21) | Problem Scout | **DONE** — Mathlib-gap audit; frobenius superseded as gap prime; schur recommended. |
| `schur-partition` | **OPE-26** (child of OPE-21; blockedBy OPE-22 wake-order) | Attack Lead | **Approved prime.** Queue `todo`; wake **after OPE-22** completes (one-specialist discipline) unless board raises concurrency. |
| OPE-21 control | **OPE-21** | Research Director | Approve shortlist, pin STATEMENT, open Schur attack, keep ledger — then **done**. |

**Wake discipline:** one specialist at a time when on shared model limits. Prefer finish **OPE-22** → then wake Attack Lead on **Schur**. Do not pile Scout+Attack+Formalist without board OK.

## Lessons encoded (do not relearn the hard way)

1. **Definition bugs kill sprints** — OPE-12 EW used a non-standard predicate; board veto. Always pin literature definition in STATEMENT.md before “solved.”
2. **Known theorems are process fuel, not discoveries** — sum-free, caterpillar-graceful families: label `informal`/`heuristic`, residual risks mandatory.
3. **Enumeration ≠ isomorphism classes** — OPE-13/18: 2142 representations → 560 distinct after adversarial pressure.
4. **Compute ≠ Lean** — passing Python tests with `sorry` in Lean is blocked at review (OPE-14).
5. **Git SoT** — write under `Documents/VSCode/open-math-lab`, not Paperclip managed `_default` mirror.
6. **Scout shortlist gate** — Director must not pick primes from catalog scores alone. Fresh Scout shortlist (or explicit board-named problem) before new attack issues (`docs/PORTFOLIO_PRINCIPLES.md`).
7. **Verify “Mathlib gap” claims against the local toolchain first** — OPE-25: frobenius (`frobeniusNumber_pair`), derangement (`numDerangements*`), catalan (`catalan*`) were all **already in Mathlib** despite dossier “gap” claims; only schur-partition was a real gap. `grep` the pinned `Mathlib/` snapshot (`.lake/packages/mathlib`) before citing a gap or scoring a candidate.

## How to update this ledger

1. Change status in `catalog/problems.json`.
2. Add/adjust the row in **Handled** or **Untouched**.
3. Link attack dir + Paperclip issue IDs in the table.
4. If a skill pack gained a real tactic/checklist, patch `skills/<pack>/SKILL.md` and note it under lessons or the problem row.
