# Feasibility Rubric

## Purpose

Score open mathematical problems for Open Math Lab attack feasibility. Output: honest go/no-go recommendations, not overpromises.

## Rubric Version

**Current**: v1 (2026-07-29)

## Scoring Dimensions (1–5 scale)

### 1. Formalizable (weight: high)

Can the problem statement and solution be expressed in Lean 4 + Mathlib?

- **5**: Direct Mathlib vocabulary (e.g., partition theorems, finite graph properties)
- **4**: Requires minor definitions, clear formalization path exists
- **3**: Moderate gaps, but standard mathematical objects
- **2**: Substantial formalization burden (missing theory)
- **1**: Fundamentally informal or computational (no theorem to state)

**Rationale**: Lean checkability is our truth gate. Unformalizable = unverifiable.

### 2. Partial Progress Paths (weight: high)

Can we make measurable progress even if full solution fails?

- **5**: Clear intermediate milestones (e.g., "verify for n ≤ 12", "formalize statement", "prove special case")
- **4**: Likely checkpoints, requires some discovery
- **3**: Some partial results possible, unclear boundaries
- **2**: All-or-nothing (RH-style)
- **1**: No partial credit available

**Rationale**: Failed attacks should produce dead-end maps, not just token burn.

### 3. Literature Clarity (weight: medium)

How well-documented is the problem?

- **5**: Published papers, known proof techniques, clear formulation (e.g., Schur's theorem)
- **4**: Well-posed problem with references (e.g., OEIS sequences, MO posts)
- **3**: Mentioned in literature but sparse details
- **2**: Informal conjecture, vague formulation
- **1**: No reliable sources, potential crackpot territory

**Rationale**: We need ground truth to verify against and learn from.

### 4. Compute Bounded (weight: medium)

Is computational exploration tractable?

- **5**: Finite enumeration (e.g., graphs ≤ 10 vertices, n ≤ 1000)
- **4**: Bounded search with optimizations (e.g., SAT solving, interval arithmetic)
- **3**: Heuristic search, may not terminate
- **2**: Exponential blowup, infeasible ranges
- **1**: No computational angle

**Rationale**: Agents excel at search + verification. Infinite unbounded exploration doesn't.

### 5. Agent Skill Fit (weight: medium)

Do we have or can we build skill packs for this domain?

- **5**: Strong Mathlib coverage + agent tactics (e.g., `Finset` combinatorics)
- **4**: Good coverage, some skill-pack curation needed
- **3**: Moderate coverage, significant upfront work
- **2**: Sparse Mathlib support
- **1**: No relevant infrastructure

**Rationale**: Skill packs (tactic templates, lemma libraries) are force multipliers.

### 6. Crackpot Risk (weight: penalty)

How likely is this to be a fool's errand or crank magnet?

- **0**: Established formalization gap, bounded problem
- **1**: Well-posed conjecture, no crank associations
- **2**: Tangential to crank-favorite topics (Collatz, 3n+1)
- **3**: Often misunderstood, requires care (twin primes computational bounds)
- **4**: Actively attracts crank attempts
- **5**: Mystical numerology territory (Illuminati primes, π patterns)

**Rationale**: Reputation risk. We prefer Mathlib gaps over conspiracy theory adjacency.

## Overall Score Calculation

```
overall = (
    formalizable * 0.25 +
    partial_progress_paths * 0.25 +
    literature_clarity * 0.15 +
    compute_bounded * 0.15 +
    agent_skill_fit * 0.20
) - (crackpot_risk * 0.10)
```

Clamped to [1, 5].

## Recommendation Thresholds

| Overall Score | Recommendation | Meaning |
|---------------|----------------|---------|
| ≥ 4.0 | **attack** | Strong candidate, assign to Attack Lead |
| 3.5–3.9 | **consider** | Borderline, may need skill-pack investment first |
| 3.0–3.4 | **formalize-only** | Good Mathlib contribution, not original research |
| 2.0–2.9 | **defer** | Not ready, revisit after infrastructure improves |
| < 2.0 | **reject** | Not feasible or too risky |

## Budget Estimate (tokens)

Rough token budget per recommendation tier:

- **attack** candidates: 150k–400k tokens (formalization + attack + review)
- **consider**: 100k–200k tokens (smaller scope or uncertain success)
- **formalize-only**: 100k–300k tokens (translation work, not discovery)
- **defer/reject**: 0 tokens (catalog only, no active work)

## Scoring Process

1. Read problem statement and sources (`problems/<id>/STATEMENT.md`)
2. Research literature (MathOverflow, OEIS, papers)
3. Check Mathlib for existing coverage or gaps
4. Score each dimension with rationale
5. Calculate overall score and recommendation
6. Write `problems/<id>/feasibility.json` with full breakdown
7. Update `catalog/problems.json` status to `scored`

## CLI Usage

```bash
# Score a problem (interactive prompts for each dimension)
python bin/mathforge score <problem-id>

# View scored problems
python bin/mathforge catalog

# Filter by recommendation
python bin/mathforge catalog --rec attack
```

## Calibration Examples

### High Score (attack): Erdős-Woods number k=16

- **Formalizable**: 4.5 (number theory, finite verification)
- **Partial**: 5.0 (interval search, incremental bounds)
- **Literature**: 4.0 (published papers, clear definition)
- **Compute**: 4.0 (bounded search space)
- **Skill Fit**: 4.5 (Mathlib number theory strong)
- **Crackpot**: 0.5 (niche but legit)
- **Overall**: 4.3 → **attack**

### Medium Score (formalize-only): Schur's Partition Theorem

- **Formalizable**: 5.0 (classic combinatorics)
- **Partial**: 4.5 (incremental formalization steps)
- **Literature**: 5.0 (1926 theorem, known proofs)
- **Compute**: 3.5 (verification exists, not primary goal)
- **Skill Fit**: 4.0 (Mathlib partition theory)
- **Crackpot**: 0.0 (established math)
- **Overall**: 4.4 → **formalize-only** (not discovery)

### Low Score (reject): Collatz conjecture full proof

- **Formalizable**: 3.0 (statement yes, proof unknown)
- **Partial**: 1.0 (all-or-nothing)
- **Literature**: 5.0 (extremely well-documented)
- **Compute**: 2.0 (verified to 2^68, but doesn't prove conjecture)
- **Skill Fit**: 3.0 (easy to state, no known tactics)
- **Crackpot**: 5.0 (crank magnet)
- **Overall**: 1.8 → **reject**

## Versioning

- **v0-stub**: Initial bootstrap scores (used for demo catalog)
- **v1**: This rubric (2026-07-29), first production version
- Future versions will refine weights and add dimensions as we calibrate

## Notes

- Scores are **estimates**, not guarantees. Real attacks may succeed/fail differently.
- Revisit scores quarterly as Mathlib expands and agent capabilities improve.
- If a problem status changes (e.g., Mathlib adds coverage), rescore and update catalog.
