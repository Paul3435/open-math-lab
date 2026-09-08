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

## Prize-money shortlist (OPE-1028, 2026-09-06) — WAVE CONSUMED

Board asked for one *open* problem with *live cash*. Scout did **not** solve and did **not** open Lean.

1. **`krenn-gu` — CONSUMED.** PR **#101** Level A + PR **#102** Level B. €3,000 namesake **out of v1**. No Level C. Do not revive.
2. **`hou-zeng-pfc` — CONSUMED Level A.** PR **#103**. $1,000/$200 namesake `∀ n>4` **out of v1**. Level B declined (OPE-1047). Do not email Hou/Zeng. Do not revive.
3. **`sun-135` — ARCHIVED (OPE-1042 REJECT / OPE-1062 stamp).** Proved 2020; not live cash. Do not revive.

RSA Factoring Challenge **ended 2007**. Millennium / Beal $1M **out of v1 as a solve**. No prize claim.

## Formalize-only shortlist (OPE-1062, 2026-09-07) — WAVE CONSUMED

Catalog-audit mill fully consumed. Do **not** re-prime. Stale “RECOMMENDED PRIME” lines naming these ids are **INPUT to restamp**, not a prime.

1. **`frobenius-real-division` — CONSUMED.** PR **#105** Level A. Catalog `formalized`. Level B `AlgEquiv` **out of v1**. Do not revive.
2. **`noether-normalization` — CONSUMED Level A.** PR **#106**. Catalog `formalized`. Level B namesake **out of v1**. Do not revive.

## Formalize-only shortlist (OPE-1078, 2026-09-07) — WAVE CONSUMED

OPE-1078 mill fully consumed. Do **not** re-prime. Stale “RECOMMENDED PRIME” lines naming these ids are **INPUT to restamp**, not a prime.

1. **`andrasfai-erdos-sos` — CONSUMED.** PR **#108** Level A. Catalog `formalized`. Level B namesake AES **out of v1**. Do not revive.
2. **`ostrowski-q` — CONSUMED Level A.** PR **#109** Level A. Catalog `formalized`. Level B namesake ostrowski **out of v1**. Do not revive.

## Formalize-only shortlist (OPE-1095, 2026-09-07) — WAVE CONSUMED

OPE-1095 mill fully consumed. Do **not** re-prime. Stale “RECOMMENDED PRIME” lines naming these ids are **INPUT to restamp**, not a prime.

1. **`ore-hamiltonian` — CONSUMED.** PR **#111** Level A. Catalog `formalized`. Level B namesake `ore_hamiltonian` **out of v1**. Do not revive.
2. **`bipartite-chromatic-index` — CONSUMED Level A.** PR **#112** Level A. Catalog `formalized`. Level B namesake `konig_edge_chromatic` **out of v1**. Do not revive.

## Formalize-only shortlist (OPE-1110, 2026-09-07) — WAVE CONSUMED

OPE-1110 mill fully consumed. Do **not** re-prime. Stale “RECOMMENDED PRIME” lines naming these ids are **INPUT to restamp**, not a prime.

1. **`schwartz-zippel` — CONSUMED.** PR **#114** Level A. Catalog `formalized`. Level B namesake `schwartz_zippel` **out of v1**. Do not revive.
2. **`hadamard-det` — CONSUMED Level A.** PR **#115** Level A. Catalog `formalized`. Level B namesake `hadamard_det` **out of v1**. Do not revive.

## Formalize-only shortlist (OPE-1125, 2026-09-07) — WAVE CONSUMED

OPE-1125 mill fully consumed. Do **not** re-prime. Stale “RECOMMENDED PRIME” lines naming these ids are **INPUT to restamp**, not a prime.

1. **`cauchy-binet` — CONSUMED.** PR **#117** Level A. Catalog `formalized`. Level B namesake `cauchy_binet` **out of v1**. Kirchhoff residual **out of v1**. Do not revive.
2. **`bollobas-two-families` — CONSUMED Level A.** PR **#118** Level A. Catalog `formalized`. Level B namesake `bollobas` **out of v1**. Weighted `ℚ` residual **out of v1**. Do not revive.

## Formalize-only shortlist (OPE-1142, 2026-09-08) — WAVE CONSUMED

OPE-1142 mill fully consumed. Do **not** re-prime. Stale “RECOMMENDED PRIME” / leftover-unassigned lines naming these ids are **INPUT to restamp**, not a prime.

1. **`singleton-bound` — CONSUMED.** PR **#120** Level A. Catalog `formalized`. Level B namesake `singleton_bound` **out of v1**. Hamming/Plotkin/MDS residual **out of v1**. Do not revive.
2. **`hook-length` — CONSUMED Level A.** PR **#121** Level A. Catalog `formalized`. Level B namesake `hook_length` **out of v1**. Catalan 2-row / RSK / hook-content residual **out of v1**. Do not revive.

## Formalize-only shortlist (OPE-1157, 2026-09-08)

OPE-1142 mill consumed (#120+#121). Catalog-audit shortlist (not a prize hunt; not a Formalist leftover continuation; not a Level B namesake revival). Independent Mathlib v4.10.0 grep this run.

1. **`birkhoff-von-neumann` — RECOMMENDED PRIME (86).** Birkhoff 1946 / von Neumann 1953: nonnegative `n×n` matrix with row- and column-sums 1 is a convex combination of permutation matrices. Named theorem ZERO; `stdBasisMatrix` / `convexHull` / Hall HIT. **Not** lattice Birkhoff (already `Order/Birkhoff.lean`). **Not** Birkhoff averages. **Not** Hall (already-in; USE glue). **Not** König matching (consumed). **Not** LDL/Cholesky (already `LDL.lower_conj_diag`). Gale–Ryser residual.
2. **`nash-williams-arboricity` leftover (84).** Nash-Williams 1964: arboricity = max `ceil(e(H)/(|V(H)|-1))`. Named theorem ZERO; `IsAcyclic` / `induce` / `edgeFinset` / `completeGraph` / `pathGraph` HIT. **Not** Cayley tree count (consumed leftover Prüfer). **Not** Kirchhoff. **Not** Turán. **Not** matroid union as extra namesake. **Unassigned this tick.**

Director assigns after approval. Scout opened **no attack issues**. Do **not** commission another Scout mill while this unused leftover remains.

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

**Last updated:** 2026-09-08 (OPE-1157 Scout: catalog-audit shortlist. Prime birkhoff-von-neumann. Leftover nash-williams-arboricity. OPE-1142 mill #120+#121 consumed.)
