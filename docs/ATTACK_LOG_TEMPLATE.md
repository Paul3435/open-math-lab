# Attack Log Template

Use this template for `problems/<id>/ATTACK_LOG.md` to document attack sessions on mathematical problems.

---

# Attack Log: [Problem ID] — [Short Problem Title]

## Problem Statement

[Copy formal statement from `problems/<id>/statement.md` or write concise version here]

**Source**: [catalog entry / external reference / original conjecture]  
**Difficulty estimate**: [trivial / easy / medium / hard / research-level]  
**Feasibility score**: [0-10, where 10 = very feasible]

---

## Meta

**Attack Lead**: [Agent ID / human name]  
**Session start**: [ISO 8601 timestamp]  
**Token budget**: [e.g., 80k tokens]  
**Compute budget**: [e.g., 10^7 operations max]  
**Time cap**: [e.g., 30 minutes]

---

## Strategy Selection

**Primary lens**: [number-theory / combinatorics / analysis / algebra / topology / logic]  
**Why this lens**: [brief justification: domain fit, structure, analogies to known problems]  
**Secondary lenses** (if applicable): [list other approaches to try if primary fails]

**Key insights from problem structure**:
- [Insight 1: e.g., "modular structure suggests residue analysis"]
- [Insight 2: e.g., "compactness of domain enables finite cover arguments"]
- [...]

---

## Session Log

### Attempt 1: [Strategy Name, e.g., "Modular Reduction"]

**Goal**: [What this attempt aims to establish or refute]

**Execution**:
- [Step 1: describe what was tried]
- [Step 2: calculation, reduction, or computation]
- [Step 3: result or intermediate finding]
- ...

**Outcome**: [success / partial progress / blocked / counterexample / inconclusive]

**Key findings**:
- [Finding 1]
- [Finding 2]
- ...

**Issues encountered**:
- [Issue 1: e.g., "modular inverse doesn't exist for m=6"]
- [Issue 2: e.g., "inductive step gap at transitioning from n to n+1"]

**Next**: [continue this line / pivot to different strategy / escalate to Reviewer]

---

### Attempt 2: [Strategy Name, e.g., "Induction on n"]

**Goal**: [What this attempt aims to establish or refute]

**Execution**:
- Base case (n = [value]): [verified / counterexample / ...]
- Inductive hypothesis: Assume [statement] holds for n = k.
- Inductive step: Show [statement] for n = k+1.
  - [Step-by-step reasoning]
- ...

**Outcome**: [success / partial progress / blocked / counterexample / inconclusive]

**Key findings**:
- [Finding 1]
- [Finding 2]

**Issues encountered**:
- [Issue 1]
- [Issue 2]

**Next**: [continue this line / pivot to different strategy / escalate to Reviewer]

---

### Attempt 3: [Strategy Name, e.g., "Bounds & Estimates"]

**Goal**: [What this attempt aims to establish or refute]

**Execution**:
- Upper bound: [expression, derivation]
- Lower bound: [expression, derivation]
- Comparison: [tight / loose / gap too large]

**Outcome**: [success / partial progress / blocked / counterexample / inconclusive]

**Key findings**:
- [Finding 1]
- [Finding 2]

**Issues encountered**:
- [Issue 1]
- [Issue 2]

**Next**: [continue this line / pivot to different strategy / escalate to Reviewer]

---

### Computational Verification

**Script/Tool**: [location of verification script, e.g., `problems/<id>/verify.py`]

**Parameters**:
- Range tested: [e.g., n ∈ [1, 10^6]]
- Precision: [e.g., 64-bit integers / floating-point epsilon = 10^-12]
- Runtime: [e.g., 45 seconds]

**Results**:
- [Result 1: e.g., "No counterexamples found for n ≤ 10^6"]
- [Result 2: e.g., "Pattern observed: f(n) ≈ n log n for large n"]
- [Result 3: e.g., "Counterexample at n = 42: expected X, got Y"]

**Interpretation**:
- [What the computational data suggests: supports conjecture / refutes / inconclusive]
- [Caveats: e.g., "floating-point errors near boundaries"]

---

## Reductions & Lemmas

**Lemma 1**: [Statement]
- **Status**: [proved / conjectured / known from Mathlib]
- **Reference**: [Mathlib lemma name / literature citation / proved in this log]
- **Used in**: [Attempt X, Y]

**Lemma 2**: [Statement]
- **Status**: [proved / conjectured / known from Mathlib]
- **Reference**: [Mathlib lemma name / literature citation / proved in this log]
- **Used in**: [Attempt X, Y]

**Reduction to known result**: [If applicable]
- **Known result**: [Theorem name, e.g., "Fermat's Little Theorem"]
- **Reduction argument**: [How the problem reduces to the known result]
- **Gaps in reduction**: [List any assumptions or steps not yet verified]

---

## Summary

**Status**: [in-progress / ready-for-review / blocked / counterexample-found / proof-sketch-complete]

**Confidence level**: [low (0-3) / medium (4-6) / high (7-10)]  
**Confidence justification**: [Why this confidence level: e.g., "computational evidence strong but no proof" → medium]

**Main result**:
- [Concise statement of what was achieved: proof sketch / counterexample / partial progress / dead end]

**Remaining gaps**:
1. [Gap 1: e.g., "uniform convergence not proven, only pointwise"]
2. [Gap 2: e.g., "inductive step assumes divisibility without verification"]
3. [...]

**Recommended next steps**:
1. [Next step 1: e.g., "Hand to Adversarial Reviewer to verify reduction to known theorem"]
2. [Next step 2: e.g., "Formalize base case in Lean before proceeding"]
3. [Next step 3: e.g., "Try topology lens if algebra approach remains blocked"]

---

## Resources Consumed

**Tokens used**: [e.g., ~65k tokens / 80k budget]  
**Compute**: [e.g., ~10^6 operations / 10^7 budget]  
**Wall-clock time**: [e.g., 22 minutes / 30 minute cap]

**Budget status**: [under budget / approaching limit / over budget]  
**Reason for stopping**: [budget exhausted / clear next handoff / blocked / proof complete]

---

## Handoff

**Handoff to**: [Adversarial Reviewer / Formalist / Research Director / blocked—no handoff]

**Deliverables**:
- This `ATTACK_LOG.md`
- [Computational scripts: `problems/<id>/verify.py`, etc.]
- [Proof sketch document: if separate from this log]
- [Lean stub: if formalization started]

**Specific request for next agent**:
- [e.g., "Reviewer: please verify the reduction to Fermat's Little Theorem in Attempt 2"]
- [e.g., "Formalist: ready for Lean encoding; see Lemma 1 dependencies"]
- [e.g., "Research Director: blocked on Lemma 2; need specialist input or problem pivot"]

---

## Appendix: Scratch Work

[Optional: rough calculations, exploratory notes, discarded approaches]

---

## Session History

### Session 1: [ISO 8601 timestamp]
- Attempts 1-3: [summary]
- Outcome: [summary]
- Handoff: [to whom / status]

### Session 2: [ISO 8601 timestamp]
- Continuation from Session 1
- New attempts: [summary]
- Outcome: [summary]
- Handoff: [to whom / status]

[Add new session entries as attacks continue]

---

## Anti-Pattern Checklist

Before marking "ready-for-review" or "proof-sketch-complete," verify you have NOT:

- [ ] Assumed commutativity without proof (algebra)
- [ ] Interchanged limits without justification (analysis)
- [ ] Used modular inverses without checking coprimality (number theory)
- [ ] Overcounted without symmetry correction (combinatorics)
- [ ] Assumed compactness without verification (topology)
- [ ] Confused syntax (⊢) and semantics (⊨) (logic)
- [ ] Over-relied on numerical evidence without rigorous argument (all domains)
- [ ] Ignored edge cases (n=0, n=1, empty set, trivial cases)
- [ ] Made unbounded search claims ("checked all n") without halting criterion

If any box is unchecked and the anti-pattern applies, **fix it before handoff**.
