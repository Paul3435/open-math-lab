# Number Theory Skill Pack

## Purpose

Attack strategies for conjectures involving integers, primes, divisibility, modular arithmetic, and number-theoretic functions.

## When to Use This Pack

Use number-theory lens when the problem involves:

- **Integers and divisibility**: GCD, LCM, prime factorization
- **Modular arithmetic**: congruences, residue classes, cyclic groups
- **Prime numbers**: distribution, gaps, primality
- **Number-theoretic functions**: φ(n), σ(n), τ(n), μ(n)
- **Diophantine equations**: integer solutions to polynomial equations
- **Additive/multiplicative properties**: sums, products, partitions

## Core Strategies

### 1. Modular Arithmetic & Residue Analysis
- Reduce statements modulo small primes or composite moduli
- Look for patterns in residue classes
- Use Chinese Remainder Theorem for composite moduli
- Check Fermat's Little Theorem / Euler's theorem constraints

### 2. Induction & Well-Ordering
- Strong induction on integer parameters
- Well-ordering principle for minimal counterexamples
- Infinite descent for impossibility proofs
- Structural induction on prime factorizations

### 3. Pigeonhole Principle
- Bounded residues → repeated values
- Dirichlet's box principle for density arguments
- Generalized pigeonhole for counts

### 4. Bounds & Estimates
- Upper/lower bounds via inequalities (AM-GM, Cauchy-Schwarz)
- Asymptotic analysis (O, Ω, Θ notation)
- Stirling's approximation for factorials
- Prime Number Theorem estimates

### 5. Divisibility & GCD Techniques
- Euclidean algorithm and Bézout's identity
- Unique factorization (Fundamental Theorem of Arithmetic)
- Divisibility chains and lattice arguments

### 6. Small-Case Enumeration
- Brute-force check for n ≤ 100 or similar bounds
- Pattern recognition in small cases
- Counterexample search in bounded ranges

## Common Pitfalls & Dead Ends

### Anti-Patterns: Do NOT Do This

1. **Unbounded search without structure**
   - **Why it fails**: Enumerating infinitely without a halting criterion wastes compute and never proves general statements.
   - **Example**: "Check all primes p to see if 2p+1 is prime" never terminates and doesn't prove anything about the conjecture.
   - **Fix**: Use bounded search (n ≤ 10^6) for patterns, then prove general case with induction/modular arithmetic/etc.

2. **Ignoring parity**
   - **Why it fails**: Many number-theory claims hinge on odd/even distinctions; missing this loses critical structure.
   - **Example**: Claiming "n² + n is even for all n" without checking both n even and n odd cases.
   - **Fix**: Split cases: n = 2k (even) and n = 2k+1 (odd); verify claim holds for both.

3. **Assuming primality without proof**
   - **Why it fails**: Composite numbers masquerading as primes can invalidate arguments.
   - **Example**: Assuming Fermat numbers Fₙ = 2^(2ⁿ) + 1 are always prime (false for n ≥ 5).
   - **Fix**: Use primality tests (trial division, Miller-Rabin) or factor explicitly; cite known results (e.g., Mersenne prime database).

4. **Modular reasoning errors**
   - **Why it fails**: Modular inverses a⁻¹ mod m exist only when gcd(a, m) = 1; division is not well-defined otherwise.
   - **Example**: Trying to solve 2x ≡ 1 (mod 6) fails because gcd(2, 6) = 2 ≠ 1.
   - **Fix**: Check coprimality before inverting; use Bézout's identity to find inverses explicitly.

5. **Overlooking edge cases**
   - **Why it fails**: n=0, n=1, negative integers often break inductive steps or modular patterns.
   - **Example**: Claiming "φ(n) < n for all n" fails at n=1 (φ(1) = 1).
   - **Fix**: Explicitly verify base cases; state domain restrictions (e.g., "for n ≥ 2").

6. **Confusing necessary and sufficient conditions**
   - **Why it fails**: "If p is prime then p is odd" is not equivalent to "If p is odd then p is prime."
   - **Example**: 9 is odd but not prime.
   - **Fix**: Distinguish hypotheses (if) from conclusions (then); prove both directions for iff claims.

7. **Over-relying on computational evidence**
   - **Why it fails**: "Verified for n ≤ 10^9" does not prove the claim for all n; counterexamples can be astronomically large.
   - **Example**: Pólya conjecture (more numbers ≤ n have odd number of prime factors than even) holds up to n ≈ 906,150,257 but is false.
   - **Fix**: Use computation to guide proof strategy, not as the proof itself; always seek rigorous argument.

### Known Hard Subdomains (Budget Carefully)

- **Multiplicative functions on sparse sets**: Often requires deep analytic number theory.
- **Goldbach-type problems**: Additive prime problems are notoriously hard.
- **Perfect number variants**: Mersenne primes, perfect numbers require heavy computation.

## Budget & Stopping Criteria

- **Token budget per reduction attempt**: 100k tokens max
- **Compute budget**: If brute-force search exceeds 10^8 operations, stop and document.
- **Time cap**: 30 minutes per attack session before checkpoint.

### Stop When

- All modular reductions (mod 2, 3, 5, 7, …) pass → escalate to Formalist
- Counterexample found → document and hand to Reviewer
- No progress after 3 distinct strategy pivots → write failed-closed summary
- Proof sketch emerges → hand to Formalist for Lean formalization

## Handoff Criteria

### → Adversarial Reviewer

Hand off when:

- You have a "proof" in natural language (must be challenged)
- Computational evidence for n ≤ 10^6 but no proof
- Reduction to a known result (verify the reduction is correct)
- Claim of impossibility (needs counterexample verification)

**Deliverable to Reviewer:**
- `ATTACK_LOG.md` with strategy attempts
- Proof sketch or computational data
- Explicit claim and hypotheses
- Remaining gaps / assumptions

### → Formalist

Hand off when:

- Proof sketch is clean and the Reviewer has approved it
- Statement is ready for Lean encoding
- Lemma reductions are identified and need formal verification

**Deliverable to Formalist:**
- Proof outline in structured steps
- Dependencies on Mathlib lemmas (if known)
- Edge cases and boundary conditions

## Example Attack Template

```markdown
# Attack: [Problem ID] — [Short Title]

## Problem Statement

[Formal statement from problems/<id>/statement.md]

## Strategy Choice

Using number-theory lens because: [integer structure, modular properties, etc.]

## Attempt 1: Modular Reduction

- Checked mod 2: [result]
- Checked mod 3: [result]
- Checked mod 5: [result]
- **Outcome**: [patterns found / no contradiction / counterexample]

## Attempt 2: Induction on n

- Base case (n=1): [verified]
- Inductive step: [tried, gap at ...]
- **Outcome**: [blocked by ... / proof sketch emerges]

## Attempt 3: Bounds & Estimates

- Upper bound via AM-GM: [expression]
- Lower bound via [technique]: [expression]
- Compared bounds: [tight? loose?]
- **Outcome**: [conclusive? inconclusive?]

## Computational Check

- Verified for n ≤ 1000: [script location]
- No counterexamples found.

## Summary

**Status**: [in-progress / ready-for-review / blocked]  
**Confidence**: [low / medium / high]  
**Next step**: [hand to Reviewer / try divisibility angle / formalize in Lean]  
**Remaining risks**: [list gaps]

## Tokens Used

~X tokens / 100k budget
```

## Skill Pack Maintenance

- Add new strategies as they prove reusable across multiple problems.
- Archive dead-end techniques with "why it failed" notes.
- Update budget guidance based on actual attack costs.
- Link to successful formalizations in `proofs/`.
