# Derangement Counting Formula

## Informal Statement

A **derangement** of a finite set is a permutation with no fixed points.

**Claim**: The number of derangements of an n-element set is:

D(n) = n! · Σ_{k=0}^{n} (-1)^k / k!

Equivalently, D(n) = round(n! / e) for n ≥ 1.

## Formalization Target

```lean
def derangement_count (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => ∀ i, σ i ≠ i)).card

theorem derangement_formula (n : ℕ) :
  (derangement_count n : ℚ) = n.factorial * (Finset.range (n + 1)).sum (fun k => (-1 : ℚ) ^ k / k.factorial) :=
```

## Motivation

- Classic result in enumerative combinatorics
- Connects permutations, inclusion-exclusion, and factorials
- Concrete, finite, computable; no classical choice needed

## Known Results

- Proof via inclusion-exclusion principle
- Recurrence: D(n) = (n - 1) · (D(n-1) + D(n-2))
- Asymptotic: D(n) ~ n! / e

## Sources

- Stanley, "Enumerative Combinatorics", Volume 1
- OEIS A000166 (subfactorial or derangements)
- Mathlib: `Equiv.Perm`, `Finset.card`, inclusion-exclusion (partially)

## Attack Strategy

1. Define `derangement_count` via filtered permutations
2. Prove small cases (n = 0, 1, 2, 3) by `decide`
3. Formalize inclusion-exclusion for permutations
4. Derive formula from inclusion-exclusion
5. Optional: prove recurrence relation and asymptotic bound

## Partial Progress

- Small-case verification (n ≤ 10) is standalone value
- Inclusion-exclusion formalization benefits Mathlib combinatorics
- Recurrence relation is easier to prove and may be sufficient

## Mathlib Gaps

- General inclusion-exclusion is not fully formalized
- May need to build custom tactic for finite set alternating sums
- `Equiv.Perm` API exists but may need helper lemmas
