# Combinatorics Skill Pack

## Purpose

Attack strategies for problems involving counting, arrangements, selections, graph structures, and discrete optimization.

## When to Use This Pack

Use combinatorics lens when the problem involves:

- **Counting & enumeration**: permutations, combinations, arrangements
- **Graph theory**: colorings, matchings, paths, connectivity
- **Recurrence relations**: sequences defined recursively
- **Generating functions**: formal power series for counting
- **Inclusion-Exclusion**: overcounting corrections
- **Pigeonhole principle**: in combinatorial settings
- **Extremal combinatorics**: maximum/minimum configurations
- **Partitions & compositions**: breaking sets into parts

## Core Strategies

### 1. Generating Functions
- Ordinary generating functions (OGF) for sequences: A(x) = Σ aₙxⁿ
- Exponential generating functions (EGF) for labeled structures
- Convolution for product rules
- Extract coefficients via partial fractions or series expansion
- Use known generating functions (Fibonacci, Catalan, etc.)

### 2. Recurrence Relations
- Set up recurrence from problem structure (e.g., a₀, a₁, then aₙ = ...)
- Solve via characteristic equation for linear recurrences
- Iterate small cases to find closed form
- Verify base cases and inductive step

### 3. Inclusion-Exclusion Principle
- Count unions via |A ∪ B| = |A| + |B| - |A ∩ B|
- Generalized form for multiple sets
- Derangements, surjections, and restricted arrangements
- Bonferroni inequalities for bounds

### 4. Graph Coloring & Matching
- Greedy coloring algorithms
- Brooks' theorem for degree bounds
- Hall's marriage theorem for bipartite matchings
- Chromatic polynomial for graph colorings
- Ramsey theory for forced structures

### 5. Double Counting & Bijections
- Count the same set in two ways (prove equality)
- Construct bijection between sets (prove cardinality equality)
- Involution principle (pairing off to cancel)

### 6. Extremal Arguments
- Maximize/minimize configurations under constraints
- Erdős-Ko-Rado theorem (intersecting families)
- Turán's theorem (edge density without cliques)
- Sperner's theorem (antichains)

### 7. Small-Case Enumeration
- Compute first 10-20 terms of sequence
- Look for patterns (linear, polynomial, exponential growth)
- Check OEIS (Online Encyclopedia of Integer Sequences)
- Validate conjectures on small instances

## Common Pitfalls & Dead Ends

### Anti-Patterns: Do NOT Do This

1. **Overcounting without correction**
   - **Why it fails**: Counting labeled vs. unlabeled objects, ordered vs. unordered arrangements leads to wrong totals.
   - **Example**: Counting permutations of {A, B, B} as 3! = 6 instead of 3!/2! = 3 (because two Bs are indistinguishable).
   - **Fix**: Use multinomial coefficients for repeated elements; apply Burnside's lemma for symmetries; explicitly check if order matters.

2. **Ignoring symmetry**
   - **Why it fails**: Symmetric structures are overcounted if not quotiented by automorphisms.
   - **Example**: Counting necklaces of n beads as 2ⁿ instead of using Pólya enumeration (cyclic + reflection symmetry).
   - **Fix**: Use Burnside's lemma (average fixed points under group action) or Pólya enumeration theorem.

3. **Incorrect recurrence setup**
   - **Why it fails**: Missing base cases or boundary conditions invalidates the recurrence solution.
   - **Example**: Setting aₙ = aₙ₋₁ + aₙ₋₂ without defining a₀, a₁ gives infinitely many solutions.
   - **Fix**: Explicitly verify base cases (a₀, a₁, ...) and boundary conditions; check small cases (n=0, 1, 2) match recurrence.

4. **Generating function algebra errors**
   - **Why it fails**: Incorrect term alignment, wrong convergence assumptions, or algebraic mistakes in series manipulation.
   - **Example**: Claiming A(x)B(x) = Σ aₙbₙxⁿ instead of Σ (Σᵢ aᵢbₙ₋ᵢ)xⁿ (convolution).
   - **Fix**: Verify coefficient extraction step-by-step; check convergence radius; use known identities (geometric series, binomial theorem).

5. **Graph structure assumptions**
   - **Why it fails**: Assuming connectivity, planarity, or bipartiteness without verification invalidates graph-theoretic arguments.
   - **Example**: Claiming χ(G) ≤ 4 for all planar graphs (true) but applying to non-planar K₅ (false: χ(K₅) = 5).
   - **Fix**: Verify graph properties explicitly (BFS for connectivity, Kuratowski for planarity, 2-coloring for bipartiteness).

6. **Confusing combinations and permutations**
   - **Why it fails**: C(n,k) counts unordered selections; P(n,k) counts ordered selections; mixing them gives wrong counts.
   - **Example**: Counting "choose 3 people from 5 for ordered roles" as C(5,3) = 10 instead of P(5,3) = 60.
   - **Fix**: Ask "does order matter?" If yes, use permutations; if no, use combinations.

7. **Over-relying on OEIS**
   - **Why it fails**: OEIS match suggests a pattern but doesn't prove it; sequences can match for small n and diverge later.

8. **Counting representations instead of isomorphism classes** (lab lesson OPE-13/18)
   - **Why it fails**: Reflecting a spine or shifting labels can inflate “verified trees” without new combinatorial objects (2142 → 560 caterpillars).
   - **Fix**: Define a canonical form; cross-check with an independent isomorphism invariant (e.g. AHU); report both raw and distinct counts.
   - **Example**: Sequence 1, 2, 4, 8, ... matches both 2ⁿ and "number of binary trees on n nodes" for small n but they differ later.
   - **Fix**: Use OEIS to guess closed form or identify known sequences, then prove the match rigorously (bijection, induction, etc.).

### Known Hard Subdomains (Budget Carefully)

- **Exact chromatic number**: NP-hard; heuristic bounds often best we can do.
- **Non-linear recurrences**: May lack closed form; asymptotic analysis instead.
- **Extremal graph theory**: Often requires deep theorems (Turán, Ramsey).

## Budget & Stopping Criteria

- **Token budget per reduction attempt**: 100k tokens max
- **Compute budget**: Enumeration beyond 10^7 objects requires justification.
- **Time cap**: 30 minutes per attack session before checkpoint.

### Stop When

- Closed-form solution emerges → hand to Formalist
- Counterexample found in small cases → document and hand to Reviewer
- No progress after 3 strategy pivots → write failed-closed summary
- Reduction to known combinatorial identity → verify reduction with Reviewer

## Handoff Criteria

### → Adversarial Reviewer

Hand off when:

- You have a combinatorial "proof" (bijection, induction, etc.)
- Computational verification for small cases (n ≤ 20)
- Generating function derivation (needs algebraic verification)
- Graph-theoretic claim (needs counterexample search)

**Deliverable to Reviewer:**
- `ATTACK_LOG.md` with strategy attempts
- Proof sketch or computational enumeration
- Explicit claim and edge cases
- Remaining gaps (e.g., "bijection construction unclear for n > 10")

### → Formalist

Hand off when:

- Proof is clean and Reviewer-approved
- Combinatorial identity is ready for Lean encoding
- Graph property needs formal verification
- Recurrence solution is validated

**Deliverable to Formalist:**
- Structured proof outline
- Dependencies (e.g., Mathlib's graph library, finite set lemmas)
- Edge cases and boundary conditions

## Example Attack Template

```markdown
# Attack: [Problem ID] — [Short Title]

## Problem Statement

[Formal statement from problems/<id>/statement.md]

## Strategy Choice

Using combinatorics lens because: [counting structure, graph property, etc.]

## Attempt 1: Generating Function Approach

- Define A(x) = Σ aₙxⁿ where aₙ = [...]
- Recurrence: aₙ = [...]
- Generating function: A(x) = [closed form or functional equation]
- Extract coefficient: aₙ = [closed form]
- **Outcome**: [success / algebra too complex / no closed form]

## Attempt 2: Recurrence Relation

- Base cases: a₀ = [...], a₁ = [...]
- Recurrence: aₙ = [...]
- Characteristic equation: [...]
- General solution: aₙ = [...]
- Verified for n ≤ 10: [yes/no]
- **Outcome**: [closed form found / non-linear recurrence / blocked]

## Attempt 3: Inclusion-Exclusion

- Total count (no restrictions): [...]
- Subtract forbidden configurations: [...]
- Add back double-counted: [...]
- Final count: [...]
- **Outcome**: [matches conjecture / counterexample at n=X]

## Attempt 4: Graph Coloring (if applicable)

- Model as graph: vertices = [...], edges = [...]
- Chromatic number χ(G) ≤ [bound]
- Greedy coloring: [result]
- Counterexample search: [none found / found at n=X]
- **Outcome**: [conjecture holds / counterexample]

## Computational Enumeration

- Computed aₙ for n ≤ 20: [list or script location]
- Pattern observed: [linear / polynomial / exponential / ...]
- OEIS match: [sequence ID if found]

## Summary

**Status**: [in-progress / ready-for-review / blocked]  
**Confidence**: [low / medium / high]  
**Next step**: [hand to Reviewer / try bijection / formalize in Lean]  
**Remaining risks**: [list gaps, e.g., "bijection not constructive"]

## Tokens Used

~X tokens / 100k budget
```

## Example: Bounded Combinatorial Conjecture

**Problem**: Prove that for any graph G on n vertices with maximum degree Δ, the chromatic number χ(G) ≤ Δ + 1.

**Attack Strategy**:
1. **Greedy coloring**: Show greedy algorithm uses at most Δ+1 colors (proof by induction).
2. **Counterexample search**: Check small graphs (n ≤ 10, Δ ≤ 5) for violations.
3. **Reduction to Brooks' theorem**: If G is not a complete graph or odd cycle, χ(G) ≤ Δ.
4. **Formalization**: Encode greedy algorithm and induction proof in Lean.

**Handoff**:
- If greedy proof is clean → Adversarial Reviewer checks induction gaps.
- If Reviewer approves → Formalist encodes in Lean with Mathlib graph theory.

## Skill Pack Maintenance

- Add new combinatorial identities as they prove useful.
- Archive failed generating function attempts with notes on why.
- Update budget estimates based on actual token/compute costs.
- Link to successful Lean formalizations in `proofs/`.
