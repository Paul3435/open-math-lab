# Problem ledger — Open Math Lab

Source of truth for **which mathematical bets we have touched**, their disposition,
and pointers to artifacts. Update this file whenever a problem changes lifecycle
status. Catalog index: `catalog/problems.json`. Feasibility dossiers live under
`catalog/problems/<id>/` and/or `problems/<id>/`.

**Last updated:** 2026-08-04 (OPE-21 director sprint)

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
| `schur-partition` | partitions | Scout seed (OPE-2 era) | **`candidate` / formalize-only** — dossier under `problems/schur-partition/`; no sprint attack yet | Known (1926); Mathlib gap claimed at scout time | `problems/schur-partition/` |

## Pipeline / infrastructure (not math bets)

| Work | Tickets | Notes |
|------|---------|-------|
| mathforge scaffold, rubric, catalog, CLI | OPE-1…OPE-11, OPE-9 | Tooling for triage + attack logs |
| Lean 4 + elan + lake build | OPE-17 (board OK) | Toolchain green; claims still board-gated |
| Workspace SoT + GitHub PR workflow | OPE-16, docs | Git SoT: `Documents/VSCode/open-math-lab` |
| Review checklist + claim gates | OPE-10, OPE-5 | `docs/REVIEW_CHECKLIST.md`, `docs/CLAIM_POLICY.md` |

## Untouched prime candidates (catalog dossiers ready)

None of these had a dedicated attack sprint before OPE-21:

| Problem ID | Score (dossier) | Domain | Suggested first move |
|------------|----------------:|--------|----------------------|
| **`frobenius-coin-problem`** | 90 | number theory | **Selected — OPE-22** — two-coin formula g(a,b)=ab−a−b |
| `derangement-formula` | 89 | enum. combinatorics | Recurrence path before full IE |
| `catalan-recurrence` | 85 | enum. combinatorics | After derangements (binomial infra) |
| `bertrand-postulate-computational` | 84 | computational NT | Bound n≤10^4 first; general thm already Mathlib |

Placeholders still needing Scout replacement: `mathlib-gap-candidate`, `oeis-finite-check-candidate`, `demo-collatz-bound-toy` (demo only).

## Active sprint (from OPE-21)

| Bet | Issue | Owner role | Intent |
|-----|-------|------------|--------|
| `frobenius-coin-problem` | **OPE-22** (child of OPE-21) | Attack Lead `65834f64-b136-424f-a6e0-124f9b6da939` | Computational certificate + Lean statement path for two-coin Frobenius; **no external claim** |
| (optional follow-up) | create after OPE-22 | Formalist | Only if Attack leaves clear Lean TODOs and lake target |
| (gate) | create after OPE-22 | Adversarial Reviewer | After attack artifacts exist |

**Wake discipline:** one specialist at a time. Do not wake Formalist/Reviewer until Attack Lead closes or blocks with artifacts.

## Lessons encoded (do not relearn the hard way)

1. **Definition bugs kill sprints** — OPE-12 EW used a non-standard predicate; board veto. Always pin literature definition in STATEMENT.md before “solved.”
2. **Known theorems are process fuel, not discoveries** — sum-free, caterpillar-graceful families: label `informal`/`heuristic`, residual risks mandatory.
3. **Enumeration ≠ isomorphism classes** — OPE-13/18: 2142 representations → 560 distinct after adversarial pressure.
4. **Compute ≠ Lean** — passing Python tests with `sorry` in Lean is blocked at review (OPE-14).
5. **Git SoT** — write under `Documents/VSCode/open-math-lab`, not Paperclip managed `_default` mirror.

## How to update this ledger

1. Change status in `catalog/problems.json`.
2. Add/adjust the row in **Handled** or **Untouched**.
3. Link attack dir + Paperclip issue IDs in the table.
4. If a skill pack gained a real tactic/checklist, patch `skills/<pack>/SKILL.md` and note it under lessons or the problem row.
