# Claim policy — Open Math Lab

## Default

**No claim.** Silence is cheaper than a wrong theorem.

## Allowed internal statuses

| status | meaning |
|--------|---------|
| `seed` | placeholder / demo |
| `needs-scout` | not yet dossiered |
| `scored` | feasibility written |
| `attacking` | active attempts |
| `blocked` | waiting on formalization or literature |
| `failed-closed` | dead ends documented; valuable |
| `informal-progress` | human-readable partial result only |
| `lean-checked` | machine-verified artifact in repo |
| `claim-ready` | packet prepared; board not yet decided |

## Board gate

Only Paul (board) may:

- assert external priority/novelty
- contact authors, arXiv, blogs, social
- raise monthly agent budgets or concurrency

## Reviewer veto

Adversarial Reviewer may force status back from `claim-ready` / `lean-checked` (if build is flaky or statement mismatches intent) with a written gap list.
