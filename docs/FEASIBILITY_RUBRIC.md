# Feasibility Rubric

**Purpose**: Score open mathematical problems for realistic attack suitability within mathforge constraints.

**Output**: Numerical feasibility score (0–100) + categorical risk flags.

---

## Scoring Dimensions

Each dimension scores 0–20. Total feasibility = sum of all five dimensions.

### 1. Formalizability (0–20)

**Question**: Can the problem statement be expressed in Lean 4 + Mathlib within reasonable effort?

- **20**: Problem naturally maps to existing Mathlib types (e.g., finite group property, polynomial bound)
- **15**: Requires 1–2 new definitions but no major theory gaps
- **10**: Needs moderate Mathlib extension (missing lemmas, glue code)
- **5**: Requires significant formalization infrastructure (new algebraic structures, custom tactics)
- **0**: Vague statement, no clear first-order encoding, or depends on unformalized foundations

**Red flags**:
- "Existence of a pattern" without decidable predicate
- Relies on未formalized fields (e.g., large swaths of algebraic topology)
- Natural language ambiguity ("sufficiently large," "typical configuration")

---

### 2. Partial Progress Pathway (0–20)

**Question**: Are there meaningful intermediate milestones that provide value even if the full problem remains open?

- **20**: Clear reduction ladder (e.g., bounded case → asymptotic case → full proof)
- **15**: Computational verification adds evidence; partial results publishable
- **10**: Some lemmas useful for Mathlib but not standalone results
- **5**: All-or-nothing proof; no incremental validation
- **0**: Binary outcome with no partial credit possible

**Red flags**:
- "Solve completely or nothing"
- No known weaker variants or special cases
- Computational bounds don't inform the general problem

---

### 3. Attack Surface (0–20)

**Question**: Do we have or can we build specialist tools/skills to make progress?

- **20**: Problem matches existing skill pack domain (combinatorics, number theory)
- **15**: Skills transferable from adjacent areas; clear tactic repertoire
- **10**: Standard techniques apply but need custom automation
- **5**: Requires expertise outside current skill inventory
- **0**: Unknown domain; no clear starting heuristics

**Boost**: +5 if Mathlib already contains >50% of needed definitions  
**Penalty**: -5 if problem is known to resist standard methods

---

### 4. Verification Budget (0–20)

**Question**: Can we verify correctness within reasonable computational limits?

- **20**: Lean proof checking is instant (<1s per theorem)
- **15**: Build time <5 min; computational lemmas tractable on local hardware
- **10**: Moderate verification (requires cluster time but <1 CPU-hour)
- **5**: High computational barrier (e.g., case explosion, unification timeouts)
- **0**: Verification infeasible (e.g., requires proof search beyond resource limits)

**Context**: Token budget is 100k–500k per attack; Lean elaboration must stay reasonable.

---

### 5. Crackpot Resistance (0–20)

**Question**: Is the problem well-defined enough to reject false claims mechanically?

- **20**: Lean type-checks the statement; counterexamples computable
- **15**: Informal statement has consensus definition + known test cases
- **10**: Literature agrees on formulation but edge cases debatable
- **5**: Problem has multiple incompatible versions in circulation
- **0**: Attracts mystical interpretations, unbounded scope, or vague success criteria

**Veto triggers** (automatic score = 0):
- Problem known to attract crank submissions (e.g., P vs NP social media "proofs")
- No authoritative reference (textbook, MathOverflow, Polymath, OEIS)
- Relies on "AI will discover the pattern" without formal criteria

---

## Composite Score Interpretation

| Score   | Verdict             | Action                                                  |
|---------|---------------------|---------------------------------------------------------|
| 80–100  | **Prime target**    | Add to shortlist; assign Attack Lead                    |
| 60–79   | **Feasible**        | Approve if skill pack exists; defer otherwise           |
| 40–59   | **Risky**           | Requires board justification; time-box exploration      |
| 20–39   | **Long shot**       | Catalog only; revisit if new tools/theory emerge        |
| 0–19    | **Infeasible**      | Reject; document why to avoid re-evaluation waste       |

---

## Usage

### Command-line scoring

```bash
python bin/mathforge score <problem-id>
```

Reads `catalog/problems/<id>/STATEMENT.md` and dossier metadata, outputs structured JSON:

```json
{
  "problem_id": "collatz-bounded-68",
  "scores": {
    "formalizability": 18,
    "partial_progress": 12,
    "attack_surface": 10,
    "verification_budget": 15,
    "crackpot_resistance": 20
  },
  "total": 75,
  "verdict": "feasible",
  "flags": [],
  "recommendation": "Approve; time-box to 200k tokens for bounded computational proof."
}
```

### Manual override

Scout may adjust dimension scores with written justification in `catalog/problems/<id>/DOSSIER.md`.

---

## Non-Scoring Factors

These do **not** affect feasibility score but inform prioritization:

- **Novelty**: Is this already in Mathlib or arXiv?
- **Impact**: Does solving this unlock other problems?
- **Skill development**: Does attacking this build reusable tactics?

Record in dossier; escalate to Research Director for roadmap trade-offs.

---

## Examples

### High-scoring example: "Finite sum identity for binomial coefficients"

- Formalizability: 20 (Mathlib has `Nat.choose`, ring tactics)
- Partial progress: 15 (can verify computationally for small n)
- Attack surface: 18 (combinatorics skill pack applies)
- Verification budget: 20 (instant Lean check)
- Crackpot resistance: 20 (unambiguous statement, computable)
- **Total: 93** → Prime target

### Low-scoring example: "Generalized Riemann Hypothesis"

- Formalizability: 5 (analytic number theory not fully in Mathlib)
- Partial progress: 8 (bounded cases known but huge literature)
- Attack surface: 2 (no relevant skill packs; highly specialized)
- Verification budget: 0 (no finite verification procedure)
- Crackpot resistance: 0 (attracts unbounded crank attempts)
- **Total: 15** → Infeasible

---

**Last updated**: 2026-07-29  
**Owner**: Problem Scout role  
**Scope**: All problems before shortlist inclusion
