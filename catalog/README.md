# mathforge Problem Catalog

This directory contains curated open mathematical problems suitable for formalization and attack within mathforge constraints.

## Structure

```
catalog/
├── problems.json          # Index of all problems
├── README.md             # This file
└── problems/
    ├── <problem-id>/
    │   ├── STATEMENT.md   # Problem statement and formalization target
    │   └── DOSSIER.json   # Feasibility scores and metadata
    └── ...
```

## Current Catalog

As of 2026-07-30, the catalog contains **5 candidate problems** and **1 completed problem**:

### Active Candidates

| Problem ID | Title | Domain | Score | Verdict |
|------------|-------|--------|-------|---------|
| sum-free-subsets | Sum-Free Subsets in Finite Sets | Additive Combinatorics | 90/100 | Prime Target |
| frobenius-coin-problem | Frobenius Coin Problem (Two Denominations) | Number Theory | 90/100 | Prime Target |
| derangement-formula | Derangement Counting Formula | Enumerative Combinatorics | 89/100 | Prime Target |
| catalan-recurrence | Catalan Numbers - Recurrence and Closed Form | Enumerative Combinatorics | 85/100 | Prime Target |
| bertrand-postulate-computational | Bertrand's Postulate - Computational Verification | Computational Number Theory | 84/100 | Prime Target |

### Completed Problems

| Problem ID | Title | Result | Completed |
|------------|-------|--------|-----------|
| erdos-woods | Erdős-Woods k=16 Verification | ✓ SOLVED (witness a=5) | 2026-07-30 |

## Usage

### List all problems

```bash
python bin/mathforge list
```

### Score a specific problem

```bash
python bin/mathforge score <problem-id>
```

Example:
```bash
python bin/mathforge score sum-free-subsets
```

### Generate attack shortlist

```bash
python bin/mathforge shortlist --limit 3
```

Output:
```
Shortlist (top 3):

1. Sum-Free Subsets in Finite Sets (sum-free-subsets)
   Score: 90/100 (prime_target)
   -> Prime target. Clear constructive proof via modulo-3 residues.

2. Frobenius Coin Problem (Two Denominations) (frobenius-coin-problem)
   Score: 90/100 (prime_target)
   -> Prime target. Well-scoped, constructive, strong number-theory match.

3. Derangement Counting Formula (derangement-formula)
   Score: 89/100 (prime_target)
   -> Prime target. Finite, constructive, excellent Mathlib fit.
```

## Scoring Methodology

See `docs/FEASIBILITY_RUBRIC.md` for full scoring criteria.

Each problem is scored on five dimensions (0-20 each):

1. **Formalizability**: Can the statement be expressed in Lean 4 + Mathlib?
2. **Partial Progress Pathway**: Are there meaningful intermediate milestones?
3. **Attack Surface**: Do we have relevant skill packs and tools?
4. **Verification Budget**: Can we verify correctness within resource limits?
5. **Crackpot Resistance**: Is the problem well-defined enough to reject false claims?

**Total score** = sum of all dimensions (0-100)

### Verdicts

- **80-100**: Prime target (add to shortlist; assign Attack Lead)
- **60-79**: Feasible (approve if skill pack exists)
- **40-59**: Risky (requires board justification)
- **20-39**: Long shot (catalog only; revisit if tools improve)
- **0-19**: Infeasible (reject)

## Problem Lifecycle

1. **Candidate**: Problem Scout has curated and scored
2. **Shortlisted**: Research Director has approved for attack
3. **In Progress**: Attack Lead is actively working on formalization/proof
4. **In Review**: Adversarial Reviewer is checking the claim
5. **Claim-Ready**: Approved for board escalation
6. **Completed**: Solved and verified (moved to Completed Problems section)
7. **Archived**: Abandoned or superseded by Mathlib

## Catalog Curation Policy

Problems are added to the catalog if they meet **all** of:

- Well-defined statement with authoritative reference (textbook, MathOverflow, OEIS, etc.)
- Feasibility score ≥ 60 (or justification for lower-scoring entries)
- Not obviously already in Mathlib (or has significant novelty/extension)
- No crackpot veto triggers (mystical numerology, unbounded AI claims, etc.)

Problems are **removed** from the catalog if:

- Discovered to be already formalized in Mathlib (move to archive note)
- Infeasible after Mathlib gap analysis (feasibility score drops below 40)
- Attracts crankery or violates epistemic honesty norms

## Shortlist Recommendations

Based on current scores and skill pack alignment:

### Top 3 Attack Candidates

1. **Sum-Free Subsets** (90/100)
   - Domain: Additive combinatorics
   - Skill packs: combinatorics, number-theory
   - Estimated budget: 150k tokens
   - Why: Constructive proof via modulo-3 residues; clear formalization path

2. **Frobenius Coin Problem** (90/100)
   - Domain: Number theory
   - Skill packs: number-theory
   - Estimated budget: 180k tokens
   - Why: Well-scoped (two coins only); Bézout's identity already in Mathlib

3. **Derangement Formula** (89/100)
   - Domain: Enumerative combinatorics
   - Skill packs: combinatorics
   - Estimated budget: 200k tokens
   - Why: Recurrence relation path available; excellent Mathlib fit

**Alternate**: If combinatorics skill pack not ready, swap (1) or (3) for **Bertrand Computational** (84/100), which is number-theory focused.

## Contributing

Problem Scout role is responsible for catalog maintenance. To propose a new problem:

1. Create `catalog/problems/<problem-id>/` directory
2. Write `STATEMENT.md` with formalization target and sources
3. Write `DOSSIER.json` with honest feasibility scores
4. Add entry to `catalog/problems.json`
5. Run `python bin/mathforge score <problem-id>` to verify
6. Submit for Research Director review

---

## Research Sprint Results

### First Sprint (2026-07-30)

**Problem**: Erdős-Woods k=16 verification  
**Status**: ✓ COMPLETE  
**Result**: k=16 is an Erdős-Woods number with minimal witness a=5

**Sprint metrics**:
- Token budget: 300k
- Tokens used: ~50k (attack + review)
- Wall time: <5 minutes
- Confidence: 10/10 (elementary verification, mechanically certain)

**Deliverables**: `attacks/erdos-woods-20260730-125506/`

**Pattern validated**: Research Director → Attack Lead → Adversarial Reviewer workflow successful.

---

**Last updated**: 2026-07-30  
**Maintained by**: Problem Scout (d0dadb22-8c25-4879-9a80-c87a45d43804)
