# Analysis Skill Pack

## Purpose

Attack strategies for problems involving limits, continuity, differentiability, integration, sequences, series, and function spaces.

## When to Use This Pack

Use analysis lens when the problem involves:

- **Limits & continuity**: ε-δ arguments, uniform continuity, pointwise vs. uniform convergence
- **Differentiation**: mean value theorem, Taylor series, optimization
- **Integration**: Riemann/Lebesgue integration, Fubini's theorem, dominated convergence
- **Sequences & series**: convergence tests, power series, Fourier series
- **Metric spaces**: completeness, compactness, Banach fixed-point theorem
- **Inequalities**: Hölder, Minkowski, Jensen, Cauchy-Schwarz (continuous case)
- **Complex analysis**: holomorphic functions, contour integration, residue theorem

## Core Strategies

### 1. ε-δ Arguments & Limit Analysis
- Prove continuity/uniform continuity via ε-δ definitions
- Diagonal arguments for subsequences
- Bolzano-Weierstrass for bounded sequences
- Squeeze theorem for limit evaluation
- Limsup/liminf for non-convergent sequences

### 2. Mean Value Theorem & Derivatives
- Rolle's theorem for intermediate critical points
- MVT for monotonicity and boundedness
- Taylor's theorem with remainder for approximations
- L'Hôpital's rule for indeterminate forms
- Implicit function theorem for constraint optimization

### 3. Integration Techniques
- Fundamental theorem of calculus (both parts)
- Integration by parts and substitution
- Dominated convergence theorem for interchange of limits/integrals
- Fubini's theorem for iterated integrals
- Residue theorem for complex contour integrals

### 4. Convergence Tests
- **Series**: ratio test, root test, integral test, comparison test, alternating series test
- **Sequences of functions**: pointwise vs. uniform convergence, Weierstrass M-test
- **Power series**: radius of convergence, term-by-term differentiation/integration
- **Fourier series**: convergence in L² vs. pointwise

### 5. Compactness & Completeness
- Heine-Borel theorem (R^n: compact ⟺ closed and bounded)
- Arzelà-Ascoli theorem for function spaces
- Banach fixed-point theorem for contraction mappings
- Baire category theorem for complete metric spaces

### 6. Inequalities & Estimates
- Cauchy-Schwarz in inner product spaces
- Hölder and Minkowski inequalities (Lᵖ spaces)
- Jensen's inequality for convex functions
- Chebyshev's inequality for probability/measure bounds

### 7. Computational Verification
- Numerical integration (quadrature) for definite integrals
- Root-finding (Newton-Raphson) for fixed points
- Series truncation with error bounds
- Plot functions to visualize behavior

## Common Pitfalls & Dead Ends

### Anti-Patterns: Do NOT Do This

1. **Assuming uniform convergence without proof**
   - **Why it fails**: Pointwise convergence does NOT preserve continuity, integrability, or differentiability.
   - **Example**: fₙ(x) = xⁿ on [0,1] converges pointwise but not uniformly; limit is discontinuous.
   - **Fix**: Use Weierstrass M-test or Dini's theorem for uniform convergence.

2. **Interchanging limits without justification**
   - **Why it fails**: lim_{n→∞} lim_{m→∞} aₙₘ ≠ lim_{m→∞} lim_{n→∞} aₙₘ in general.
   - **Example**: aₙₘ = n/(n+m) → different limits depending on order.
   - **Fix**: Use dominated convergence theorem or uniform convergence to justify interchange.

3. **Ignoring domain restrictions**
   - **Why it fails**: Taylor series may not converge outside radius of convergence; derivatives may not exist at boundary points.
   - **Example**: log(x) Taylor series at x=1 has radius 1; diverges for x ≤ 0.
   - **Fix**: Always specify domain explicitly; check boundary behavior.

4. **Applying MVT to non-differentiable functions**
   - **Why it fails**: MVT requires differentiability on open interval and continuity on closed interval.
   - **Example**: f(x) = |x| on [-1,1] is not differentiable at 0.
   - **Fix**: Verify differentiability assumptions; use intermediate value theorem if only continuity holds.

5. **Confusing absolute vs. conditional convergence**
   - **Why it fails**: Conditionally convergent series can be rearranged to converge to any value (Riemann rearrangement theorem).
   - **Example**: Σ (-1)ⁿ/n converges conditionally but not absolutely.
   - **Fix**: Use ratio/root test for absolute convergence; be explicit about rearrangement validity.

6. **Neglecting Lebesgue vs. Riemann integration**
   - **Why it fails**: Dominated convergence, Fubini require Lebesgue integrability; Riemann integrals don't compose well.
   - **Example**: Dirichlet function (1 on rationals, 0 on irrationals) is Lebesgue integrable (integral = 0) but not Riemann integrable.
   - **Fix**: State which integral is used; for measure-theoretic arguments, default to Lebesgue.

7. **Over-relying on numerical computation**
   - **Why it fails**: Floating-point errors accumulate; numerical evidence ≠ proof.
   - **Example**: Computing series to 10^6 terms doesn't prove convergence.
   - **Fix**: Use numerical evidence to guide proof strategy, not as the proof itself.

### Known Hard Subdomains (Budget Carefully)

- **Functional analysis**: Spectral theory, operator norms, dual spaces require advanced machinery.
- **Harmonic analysis**: Fourier transforms, convolution algebras, distribution theory are deep.
- **PDE theory**: Sobolev spaces, weak solutions, regularity theory are specialist topics.
- **Analytic number theory**: Riemann zeta function, L-functions, prime gaps need deep analysis + number theory.

## Budget & Stopping Criteria

- **Token budget per reduction attempt**: 100k tokens max
- **Compute budget**: Numerical integration/series evaluation beyond 10^7 terms needs justification.
- **Time cap**: 30 minutes per attack session before checkpoint.

### Stop When

- Rigorous ε-δ proof emerges → hand to Formalist for Lean encoding
- Counterexample found (e.g., discontinuity, divergence) → document and hand to Reviewer
- No progress after 3 strategy pivots → write failed-closed summary
- Reduction to known analysis theorem (MVT, dominated convergence, etc.) → verify with Reviewer

## Handoff Criteria

### → Adversarial Reviewer

Hand off when:

- You have an ε-δ "proof" of continuity/convergence
- Numerical evidence for integral/series convergence (e.g., computed to 10^6 terms)
- Reduction to known theorem (verify reduction is valid)
- Claim of discontinuity/divergence (needs rigorous counterexample)

**Deliverable to Reviewer:**
- `ATTACK_LOG.md` with strategy attempts
- Proof sketch with explicit ε-δ or convergence arguments
- Numerical data (if applicable)
- Explicit claim and hypotheses
- Remaining gaps (e.g., "uniform convergence not verified")

### → Formalist

Hand off when:

- Proof is clean and Reviewer-approved
- Statement involves standard analysis concepts (limits, continuity, derivatives, integrals)
- Dependencies on Mathlib.Analysis identified
- Edge cases and boundary conditions documented

**Deliverable to Formalist:**
- Structured proof outline with lemma dependencies
- Explicit domain restrictions and hypotheses
- References to Mathlib lemmas (e.g., `continuous_of_epsilon_delta`, `integral_mono`)

## Example Attack Template

```markdown
# Attack: [Problem ID] — [Short Title]

## Problem Statement

[Formal statement from problems/<id>/statement.md]

## Strategy Choice

Using analysis lens because: [involves limits/continuity/derivatives/integrals/etc.]

## Attempt 1: ε-δ Argument for Continuity

- Let ε > 0 be given.
- Choose δ = [expression in terms of ε].
- Verify |x - x₀| < δ ⟹ |f(x) - f(x₀)| < ε:
  - [calculation steps]
- **Outcome**: [proof complete / gap at ... / counterexample at x = ...]

## Attempt 2: Mean Value Theorem

- Verify f is continuous on [a,b] and differentiable on (a,b): [yes/no]
- Apply MVT: ∃c ∈ (a,b) such that f'(c) = (f(b) - f(a))/(b - a)
- Bound f'(c): [using derivative calculation]
- Conclude: [desired inequality/property]
- **Outcome**: [proof sketch / blocked by non-differentiability / ...]

## Attempt 3: Series Convergence Test

- Series: Σ aₙ where aₙ = [...]
- Ratio test: lim |aₙ₊₁/aₙ| = [...]
- Conclusion: [converges absolutely / diverges / inconclusive]
- Numerical check: partial sums for n ≤ 10^6: [script location]
- **Outcome**: [converges / diverges / conditionally convergent]

## Attempt 4: Dominated Convergence for Limit Interchange

- Sequence of functions: fₙ(x) = [...]
- Pointwise limit: f(x) = lim fₙ(x) = [...]
- Dominating function: |fₙ(x)| ≤ g(x) where ∫g < ∞: [yes/no]
- Conclusion: lim ∫fₙ = ∫f = [...]
- **Outcome**: [interchange valid / dominating function not integrable / ...]

## Computational Verification

- Numerical integration of ∫f for [a,b]: [result from quadrature]
- Series partial sums S₁₀₀₀₀₀₀ = [value]
- Plot of f(x) on [a,b]: [shows continuity / discontinuity at ...]

## Summary

**Status**: [in-progress / ready-for-review / blocked]  
**Confidence**: [low / medium / high]  
**Next step**: [hand to Reviewer / try compactness argument / formalize ε-δ proof in Lean]  
**Remaining risks**: [list gaps, e.g., "uniform convergence not proven, only pointwise"]

## Tokens Used

~X tokens / 100k budget
```

## Skill Pack Maintenance

- Add new convergence tests and inequality techniques as they prove useful.
- Archive failed ε-δ attempts with notes on why domains were restricted.
- Update numerical verification scripts with error bound estimates.
- Link to successful Lean formalizations in `proofs/` (especially for MVT, DCT, etc.).
