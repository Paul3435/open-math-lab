# Erdős-Woods Numbers

## Problem Statement

A positive integer k is called an **Erdős-Woods number** if there exists a positive integer a such that for every integer j in the open interval (a, a+k) — that is, for each j with a < j < a+k — the integer j shares at least one prime factor with either a or a+k (the interval endpoints).

**Known result**: k = 16 is an Erdős-Woods number with minimal witness **a = 2184** (Erdős & Woods, 1980).

## Formal Definition

Given k ∈ ℕ⁺, we say k is an Erdős-Woods number if:

∃a ∈ ℕ⁺: ∀j ∈ ℕ, (a < j < a+k) ⇒ [gcd(j, a) > 1 ∨ gcd(j, a+k) > 1]

Equivalently: every integer in the open interval (a, a+k) is composite relative to the endpoints {a, a+k}.

## Background

- **Source**: Erdős, P. and Woods, A. R. (1980), *Some new results on problem of Erdős and Graham*
- **Known Erdős-Woods numbers**: 16, 22, 34, 36, 46, 56, 64, 66, 70, 76, 78, 86, 88, 92, 94, ...
- **Canonical example**: k=16 with minimal witness a=2184
  - Every integer j with 2184 < j < 2200 shares a prime factor with 2184 or 2200

## Mathematical Context

The Erdős-Woods property characterizes intervals where the endpoints "cover" all interior points through shared divisibility. This is related to:

- Arithmetic progressions and covering systems
- Distribution of smooth numbers
- Computational bounds on witness existence

## Literature References

1. Erdős, P. and Woods, A. R. (1980). "Some new results on problem of Erdős and Graham"
2. OEIS A059756: Erdős-Woods numbers
3. Computational searches have verified witnesses for small k values

## Verification Approach

To verify a claimed witness (k, a):

1. Check interval bounds: compute a+k
2. For each integer j in (a, a+k):
   - Compute gcd(j, a)
   - Compute gcd(j, a+k)
   - Verify at least one gcd > 1
3. If all j satisfy the condition, (k, a) is a valid witness pair

**Primes relevant for k=16**: {2, 3, 5, 7, 11, 13}

For a=2184, k=16:
- Endpoints: 2184 = 2³ × 3 × 7 × 13, 2200 = 2³ × 5² × 11
- Interval: (2184, 2200) contains 15 integers: 2185, 2186, ..., 2199
- Each must share a factor with 2184 or 2200

## Success Criteria

**Mathematical formalization** (Lean 4):
- Formalize the definition of Erdős-Woods numbers
- Verify k=16, a=2184 as a witness pair
- Computational proof via exhaustive divisibility check

**Computational verification**:
- Script verifying each j ∈ (2184, 2200) shares a factor with an endpoint
- Clean output showing gcd results for transparency

## Domain

**Primary**: Elementary Number Theory  
**Secondary**: Computational Number Theory, Formalization

## Difficulty Estimate

**Mathematical complexity**: Low (definition is elementary, known result)  
**Computational complexity**: Trivial (verification is 15 gcd computations)  
**Formalization complexity**: Low-Medium (Lean statement + computational certificate)  
**Feasibility score**: 7.5 / 10 (straightforward formalization of known result)

## Notes

This problem serves as a **calibration target** for the lab's verification pipeline. The mathematical claim is settled; the value lies in producing a machine-checked artifact demonstrating the witness property.
