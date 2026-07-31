# Topology Skill Pack

## Purpose

Attack strategies for problems involving topological spaces, continuity, compactness, connectedness, separation axioms, and algebraic topology.

## When to Use This Pack

Use topology lens when the problem involves:

- **Point-set topology**: open/closed sets, neighborhoods, bases, subbases, closure, interior, boundary
- **Continuity & homeomorphisms**: continuous maps, open/closed maps, homeomorphic spaces
- **Compactness**: finite subcover property, sequential compactness, Bolzano-Weierstrass, Heine-Borel
- **Connectedness**: connected/disconnected spaces, path-connectedness, components
- **Separation axioms**: T₀, T₁, T₂ (Hausdorff), T₃ (regular), T₄ (normal)
- **Metric spaces**: metrics, open balls, completeness, Cauchy sequences, Baire category
- **Algebraic topology**: homotopy, fundamental group, covering spaces, homology, cohomology
- **Manifolds**: charts, atlases, differentiable structures, tangent spaces

## Core Strategies

### 1. Open Set Characterizations
- Verify topology axioms: ∅, X open; arbitrary unions open; finite intersections open
- Subbasis generates topology via finite intersections then arbitrary unions
- Closure characterization: x ∈ cl(A) ⟺ every neighborhood of x intersects A
- Interior: largest open set contained in A; boundary: cl(A) \ int(A)

### 2. Continuity Arguments
- f: X → Y continuous ⟺ preimages of open sets are open
- Sequential continuity (metric spaces): xₙ → x ⟹ f(xₙ) → f(x)
- Homeomorphism: bijective, continuous, with continuous inverse
- Pasting lemma: glue continuous functions on closed/open covers

### 3. Compactness Techniques
- Heine-Borel (R^n): compact ⟺ closed and bounded
- Sequential compactness: every sequence has convergent subsequence
- Finite subcover property: every open cover has finite subcover
- Continuous image of compact is compact
- Tychonoff's theorem: product of compact spaces is compact (AC)

### 4. Connectedness Arguments
- X connected ⟺ no separation into disjoint nonempty open sets
- Path-connected ⟹ connected (converse false: topologist's sine curve)
- Intermediate Value Theorem: continuous image of connected is connected
- Components are maximal connected subspaces

### 5. Separation Axioms
- T₀ (Kolmogorov): points distinguishable by open sets
- T₁: points are closed sets
- T₂ (Hausdorff): distinct points have disjoint neighborhoods
- T₃ (regular): closed sets and points outside have disjoint neighborhoods
- T₄ (normal): disjoint closed sets have disjoint neighborhoods
- Urysohn's lemma (normal): continuous function separating closed sets

### 6. Metric Space Techniques
- d(x,y) satisfies: non-negativity, symmetry, triangle inequality, d(x,y)=0 ⟺ x=y
- Completeness: every Cauchy sequence converges
- Baire category theorem: complete metric spaces are Baire (countable union of nowhere dense ≠ whole space)
- Contraction mapping theorem: Banach fixed-point theorem

### 7. Algebraic Topology (Advanced)
- Fundamental group π₁(X, x₀): homotopy classes of loops
- Van Kampen's theorem: gluing fundamental groups
- Covering space theory: lifts, deck transformations, Galois correspondence
- Homology groups Hₙ(X): algebraic invariants, functoriality, long exact sequences

### 8. Computational & Visualization
- Plot topological spaces in R² or R³ to visualize
- Compute fundamental group via presentations
- Check homeomorphism invariants (compactness, connectedness, T₂, etc.)
- Use CW-complex structure for homology computation

## Common Pitfalls & Dead Ends

### Anti-Patterns: Do NOT Do This

1. **Assuming metric space properties in general topology**
   - **Why it fails**: Not all topological spaces are metrizable; sequential arguments fail without first-countability.
   - **Example**: Zariski topology on algebraic varieties is not Hausdorff or metrizable.
   - **Fix**: Check if space is metrizable or first-countable before using sequences; use nets or filters in general.

2. **Confusing open vs. closed maps**
   - **Why it fails**: Continuous maps need not be open or closed; homeomorphisms are both.
   - **Example**: f: [0,2π) → S¹ by f(θ) = e^(iθ) is continuous and bijective but not a homeomorphism (inverse not continuous).
   - **Fix**: Verify inverse is continuous for homeomorphism; check image of open/closed sets explicitly.

3. **Assuming compactness is preserved under continuous maps in reverse**
   - **Why it fails**: Preimage of compact need not be compact.
   - **Example**: f: R → R by f(x) = x is continuous; [0,1] is compact but f⁻¹([0,1]) = [0,1] is compact only because domain is R (not general).
   - **Fix**: Only forward direction holds: continuous image of compact is compact.

4. **Ignoring separation axioms**
   - **Why it fails**: Many theorems require Hausdorff (e.g., compact subsets of Hausdorff spaces are closed).
   - **Example**: In non-Hausdorff spaces, limits are not unique; sequences can converge to multiple points.
   - **Fix**: Explicitly check separation axioms; state when Hausdorff is assumed.

5. **Confusing path-connected and connected**
   - **Why it fails**: Path-connected ⟹ connected, but converse is false.
   - **Example**: Topologist's sine curve {(x, sin(1/x)) : x > 0} ∪ {(0,0)} is connected but not path-connected.
   - **Fix**: Prove path-connectedness explicitly by constructing paths; don't assume from connectedness.

6. **Assuming topology is generated by metric**
   - **Why it fails**: Many topologies are not metrizable (e.g., product topology on R^∞, Zariski topology).
   - **Example**: R^R with product topology is not first-countable, so not metrizable.
   - **Fix**: Check metrizability (e.g., Urysohn metrization theorem: regular + second-countable ⟹ metrizable).

7. **Misapplying Tychonoff's theorem**
   - **Why it fails**: Requires axiom of choice; product topology is not the box topology.
   - **Example**: Box topology on R^∞ is not compact, but product topology is (by Tychonoff).
   - **Fix**: Use product topology (finite intersections of cylinder sets), not box topology.

8. **Over-relying on algebraic topology for simple problems**
   - **Why it fails**: Computing fundamental groups or homology is overkill for point-set topology questions.
   - **Example**: Checking if S² is homeomorphic to R² doesn't need homology (compactness suffices).
   - **Fix**: Use simplest invariants first (compactness, connectedness, Hausdorff); escalate to algebraic topology only if needed.

### Known Hard Subdomains (Budget Carefully)

- **Algebraic topology**: Homology/cohomology computation, spectral sequences, homotopy groups πₙ for n ≥ 2.
- **Differential topology**: Transversality, Morse theory, cobordism, exotic structures.
- **Geometric topology**: Knot theory, 3-manifolds, Poincaré conjecture machinery.
- **Dimension theory**: Covering dimension, Lebesgue dimension, fractal dimension.

## Budget & Stopping Criteria

- **Token budget per reduction attempt**: 100k tokens max
- **Compute budget**: Fundamental group computation for CW-complexes beyond 10 cells needs justification.
- **Time cap**: 30 minutes per attack session before checkpoint.

### Stop When

- Topological property is established (compact, connected, Hausdorff, etc.) → hand to Formalist
- Counterexample found (e.g., space is not compact) → document and hand to Reviewer
- No progress after 3 strategy pivots → write failed-closed summary
- Reduction to known topology theorem (Heine-Borel, Tychonoff, etc.) → verify with Reviewer

## Handoff Criteria

### → Adversarial Reviewer

Hand off when:

- You have a topology "proof" (compactness, connectedness, homeomorphism)
- Visualization or diagram of topological space
- Reduction to known theorem (verify reduction is valid)
- Claim about topological invariants (needs counterexample search)

**Deliverable to Reviewer:**
- `ATTACK_LOG.md` with strategy attempts
- Proof sketch with explicit open set arguments or subcover constructions
- Diagrams or plots (if applicable)
- Explicit claim and hypotheses
- Remaining gaps (e.g., "open cover construction not explicit")

### → Formalist

Hand off when:

- Proof is clean and Reviewer-approved
- Statement involves standard topological concepts (compactness, continuity, etc.)
- Dependencies on Mathlib.Topology identified
- Edge cases (discrete topology, trivial topology, etc.) documented

**Deliverable to Formalist:**
- Structured proof outline with lemma dependencies
- Explicit topology definitions (open sets, bases, etc.)
- References to Mathlib lemmas (e.g., `IsCompact.image`, `IsConnected.image`)

## Example Attack Template

```markdown
# Attack: [Problem ID] — [Short Title]

## Problem Statement

[Formal statement from problems/<id>/statement.md]

## Strategy Choice

Using topology lens because: [involves open sets/compactness/continuity/connectedness/etc.]

## Attempt 1: Compactness Argument

- Space X = [...]
- Open cover: {Uᵢ}ᵢ∈I where Uᵢ = [...]
- Finite subcover: {U₁, ..., Uₙ} where n = [...]
- Verify ⋃ⁿᵢ₌₁ Uᵢ = X: [yes/no]
- Conclusion: X is compact
- **Outcome**: [compact / not compact (no finite subcover for cover {...}) / ...]

## Attempt 2: Connectedness via Separation

- Suppose X = A ∪ B where A, B are nonempty, disjoint, open.
- Then A = X \ B is also closed, and B = X \ A is also closed.
- Contradiction: [X is interval / path-connected / ... so cannot be separated]
- Conclusion: X is connected
- **Outcome**: [connected / not connected (explicit separation: A = {...}, B = {...}) / ...]

## Attempt 3: Continuity via Preimages

- Function f: X → Y defined by f(x) = [...]
- Let V ⊆ Y be open.
- Preimage f⁻¹(V) = {...}
- Check f⁻¹(V) is open in X: [yes/no, using open set definition]
- Conclusion: f is continuous
- **Outcome**: [continuous / not continuous (counterexample: V = {...} has closed preimage) / ...]

## Attempt 4: Hausdorff Property

- Let x, y ∈ X be distinct points.
- Neighborhoods U of x, V of y such that U ∩ V = ∅:
  - U = {...}, V = {...}
  - Check U, V open and disjoint: [yes/no]
- Conclusion: X is Hausdorff (T₂)
- **Outcome**: [Hausdorff / not Hausdorff (no disjoint neighborhoods for x = {...}, y = {...}) / ...]

## Attempt 5: Fundamental Group (if applicable)

- Space X = [...]
- Base point x₀ = [...]
- Loops: representatives [α], [β], ... where α(t) = [...]
- Relations: [αβ] = [...], [α⁻¹] = [...], ...
- Group presentation: π₁(X, x₀) = ⟨generators | relations⟩ = [...]
- Conclusion: π₁(X, x₀) ≅ [Z, Z/nZ, free group, ...]
- **Outcome**: [fundamental group computed / too complex to compute / ...]

## Visualization

- Plot of space X in R²: [shows connected/disconnected / compact/non-compact]
- Homotopy diagram: [shows path-connectedness or lack thereof]

## Summary

**Status**: [in-progress / ready-for-review / blocked]  
**Confidence**: [low / medium / high]  
**Next step**: [hand to Reviewer / try covering space argument / formalize compactness proof in Lean]  
**Remaining risks**: [list gaps, e.g., "Hausdorff property assumed but not verified"]

## Tokens Used

~X tokens / 100k budget
```

## Skill Pack Maintenance

- Add new topological invariants and theorems as they prove useful (e.g., Urysohn's lemma, Tietze extension).
- Archive failed compactness arguments with notes on why finite subcovers weren't found.
- Update visualization scripts for common spaces (torus, Klein bottle, etc.).
- Link to successful Lean formalizations in `proofs/` (especially for compactness, connectedness, Hausdorff).
