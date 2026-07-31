# Sum-Free Subsets in Finite Sets

## Informal Statement

For a finite set S ⊆ ℕ, a subset A ⊆ S is **sum-free** if there do not exist x, y, z ∈ A (not necessarily distinct) such that x + y = z.

**Claim**: Every finite set of n positive integers contains a sum-free subset of size at least n/3.

## Formalization Target

```lean
theorem sum_free_subset_bound (S : Finset ℕ) (hS : S.Nonempty) :
  ∃ A : Finset ℕ, A ⊆ S ∧ IsSumFree A ∧ A.card * 3 ≥ S.card :=
```

where `IsSumFree A` is defined as:

```lean
def IsSumFree (A : Finset ℕ) : Prop :=
  ∀ x y z, x ∈ A → y ∈ A → z ∈ A → x + y ≠ z
```

## Motivation

This is a classical result in additive combinatorics. The bound n/3 is tight (consider {1, 2, 3}).

## Known Results

- The n/3 bound is achievable by taking residues modulo 3 (e.g., all elements ≡ 1 mod 3)
- Erdős-Ko-Rado theorem and Ramsey theory connections
- Constructive proof via greedy or probabilistic method

## Sources

- "Additive Combinatorics" by Tao & Vu, Chapter 2
- MathOverflow: https://mathoverflow.net/questions/tagged/additive-combinatorics
- Related to OEIS A007865 (maximal sum-free sets)

## Attack Strategy

1. Define `IsSumFree` predicate in Lean
2. Prove the modulo-3 construction explicitly
3. Show this construction achieves the bound
4. Optional: formalize the probabilistic argument as alternative proof

## Partial Progress

Even formalizing `IsSumFree` and proving basic properties (empty set is sum-free, singletons are sum-free) adds value to Mathlib.
