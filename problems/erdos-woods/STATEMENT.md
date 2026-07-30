# Erdős-Woods number existence for k=16

**id:** `erdos-woods`

## Informal statement

An integer k is called an **Erdős-Woods number** if there exists a positive integer a such that for each integer d with 0 < d ≤ k, at least one of the numbers a, a+1, ..., a+k has a nontrivial common factor with d.

The conjecture states that every sufficiently large integer is an Erdős-Woods number. For small k, determining whether k is an Erdős-Woods number requires exhaustive computational search or mathematical proof.

**Research question:** Is k=16 an Erdős-Woods number?

Current status: k=16 is believed to be an Erdős-Woods number but lacks complete computational verification across all necessary search ranges. The search space is bounded but computationally intensive.

## Why feasible?

1. **Bounded search space**: For any k, there exists a computable bound B(k) such that if no witness a ≤ B(k) exists, then k is not an Erdős-Woods number. For k=16, heuristic bounds suggest B(16) ≤ 10^12.

2. **Parallelizable**: The search can be partitioned into independent intervals.

3. **Checkable**: Each candidate witness a can be verified in polynomial time.

4. **Formalizable**: The definition translates cleanly to Lean/Mathlib (divisibility, intervals, existential claims).

5. **Partial progress measurable**: Progress = (intervals checked) / (total search space).

6. **Literature base**: Papers by Erdős & Woods (1980), Cégielski et al. (2006), computational number theory databases.

## Why this specific problem?

- **Not a crackpot target**: Well-defined finite search, no connection to RH/Goldbach/P=NP.
- **Research value**: Erdős-Woods numbers connect to covering systems, modular arithmetic patterns, and sieve theory.
- **Attack-ready**: Skill pack = experimental number theory + Python/Lean verification.
- **Honest frame**: This is a verification task, not a deep theorem proof.

## References

- Erdős, P., & Woods, A. R. (1980). "Some computational results on a problem of Erdős and Graham." Utilitas Mathematica, 17, 253-260.
- Cégielski, P., Matiyasevich, Y., & Richard, D. (2006). "Definability and decidability issues in extensions of the integers with the divisibility predicate." Journal of Symbolic Logic, 71(2), 643-656.
- OEIS A059756: Erdős-Woods numbers
- Mathlib gaps: No current formalization of Erdős-Woods number definition in Mathlib (as of Jan 2025).
