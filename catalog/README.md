# mathforge Problem Catalog

This directory contains curated mathematical problems suitable for formalization
and attack within mathforge constraints.

**Authoritative handled-history:** [`docs/PROBLEM_LEDGER.md`](../docs/PROBLEM_LEDGER.md)  
**Index JSON:** [`problems.json`](problems.json)

## Structure

```
catalog/
├── problems.json          # Index of all problems (+ statuses)
├── README.md              # This file
└── problems/
    ├── <problem-id>/
    │   ├── STATEMENT.md   # Problem statement and formalization target
    │   └── DOSSIER.json   # Feasibility scores and metadata
    └── ...
```

Working attack trees and extra notes also live under repo-root `problems/<id>/`
and `attacks/<id>-<timestamp>/`. Prefer git SoT:
`C:\Users\paulb\Documents\VSCode\open-math-lab`.

## Snapshot (2026-08-04, OPE-21)

### Active / shortlisted

| Problem ID | Title | Domain | Score | Status |
|------------|-------|--------|------:|--------|
| **frobenius-coin-problem** | Frobenius Coin Problem (Two Denominations) | Number Theory | 90 | **shortlisted (OPE-22 attack)** |
| sum-free-subsets | Sum-Free Subsets in Finite Sets | Additive Combinatorics | 90 | informal (OPE-14 process; known thm) |
| derangement-formula | Derangement Counting Formula | Enumerative Combinatorics | 89 | candidate |
| catalan-recurrence | Catalan Numbers - Recurrence and Closed Form | Enumerative Combinatorics | 85 | candidate |
| bertrand-postulate-computational | Bertrand Computational Certificate | Computational NT | 84 | candidate |
| schur-partition | Schur partition theorem | Partitions | — | candidate (formalize-only) |
| erdos-woods | Erdős-Woods k=16 (correct a=2184) | Elem. NT | — | candidate; OPE-12 claim **vetoed** |

### Handled (see ledger for full residual risks)

| Problem ID | Result | Tickets |
|------------|--------|---------|
| graceful-tree-conjecture (caterpillars n≤12) | heuristic verify, 560 classes, 0 failures; family already known graceful ∀n | OPE-13,18,20 |
| erdos-woods (false a=5 path) | definition bug → board veto | OPE-12,15 |
| sum-free-subsets | classical Erdős; compute OK; Lean not claim-ready | OPE-14 |

### Seeds / needs Scout

| ID | Notes |
|----|-------|
| demo-collatz-bound-toy | pipeline demo only |
| ~~mathlib-gap-candidate~~ | **replaced** 2026-08-07 (Scout keep-fresh) → `van-der-Waerden-w23`, then `ramsey-r33`/`schur-number` |
| ~~oeis-finite-check-candidate~~ | **replaced** 2026-08-07 (Scout keep-fresh) → `ramsey-r33` + `schur-number` (formalize-only, Mathlib-gap) |

## Usage

```bash
python bin/mathforge list
python bin/mathforge score <problem-id>
python bin/mathforge shortlist --limit 3
```

## Scoring Methodology

See `docs/FEASIBILITY_RUBRIC.md`. Five dimensions × 0–20 → total 0–100.

| Total | Verdict |
|------:|---------|
| 80–100 | Prime target |
| 60–79 | Feasible |
| 40–59 | Risky (board justification) |
| 20–39 | Long shot |
| 0–19 | Infeasible |

## Problem Lifecycle

1. **Candidate** — Scout curated and scored  
2. **Shortlisted** — Director approved for attack  
3. **In Progress** — Attack Lead working  
4. **In Review** — Adversarial Reviewer  
5. **Claim-Ready** — rare; board escalation only  
6. **Completed / formalized / heuristic / informal / vetoed** — see ledger labels  
7. **Archived** — abandoned or superseded by Mathlib  

## Catalog Curation Policy

**Add** if: well-defined + authoritative source; score ≥ 60 (or justified); not already trivial in Mathlib without extension value; no crackpot triggers.

**Remove / archive** if: already fully in Mathlib with no lab value; score collapses < 40; crankery.

## Novelty tagging (OPE-28)

Every `problems.json` entry must carry an `expected` tag set by Scout during the pre-screen
(before funding an attack), per `docs/roles/problem-scout.md`:

- `known-classical` — already in Mathlib/classic literature → do not re-fund as novel
- `formalize-only` — genuine Mathlib gap, no novelty claim
- `open` — unsolved; eligible for a gate-funded attack

Fuller enum in `problems.json` → `expected_taxonomy`.

## Shortlist (post OPE-21)

1. **Frobenius (two coins)** — OPE-22 in flight  
2. **Derangement formula** — next combinatorics formalization bet  
3. **Catalan recurrence** — after binomial infra from (2)  
**Alternate:** Bertrand computational certificate (smaller bound first).  
**Do not re-open** EW a=5 path. Sum-free only as Lean cleanup, not “discovery.”

## Contributing

Problem Scout owns catalog maintenance:

1. `catalog/problems/<id>/STATEMENT.md` + `DOSSIER.json`  
2. Entry in `problems.json`  
3. Row in `docs/PROBLEM_LEDGER.md` when touched  
4. `python bin/mathforge score <id>`  
5. Director review before attack assignment  

---

**Last updated:** 2026-08-31 (OPE-770 Scout: post Moore #76 + Stirling #77. Fresh shortlist `bipartite-odd-cycle` + `euclid-euler-perfect`.)
