# Frobenius Coin Problem (Two Denominations)

## Informal Statement

Given two coprime positive integers a and b, the **Frobenius number** g(a, b) is the largest integer that **cannot** be represented as a non-negative integer linear combination of a and b.

**Claim**: g(a, b) = ab - a - b

## Formalization Target

```lean
def representable (a b n : ℕ) : Prop :=
  ∃ x y : ℕ, n = a * x + b * y

def frobenius_number (a b : ℕ) : ℕ :=
  a * b - a - b

theorem frobenius_two_coins (a b : ℕ) (ha : a > 0) (hb : b > 0) (hcoprime : Nat.gcd a b = 1) :
  (∀ n > frobenius_number a b, representable a b n) ∧
  ¬ representable a b (frobenius_number a b) :=
```

## Motivation

- Classic problem in number theory and discrete optimization
- Finite bound, constructive proof available
- Applications to change-making, scheduling, resource allocation

## Known Results

- Formula g(a, b) = ab - a - b is well-known
- Proof uses Bézout's identity and modular arithmetic
- Three or more denominations: NP-hard (out of scope)

## Sources

- "Concrete Mathematics" by Graham, Knuth, Patashnik, Section 3.3
- OEIS A028387 (Frobenius numbers)
- Mathlib: `Nat.gcd`, `Nat.Coprime`, Bézout's identity

## Attack Strategy

1. Formalize `representable` predicate
2. Prove representability for all n ≥ ab (Chicken McNugget theorem)
3. Show ab - a - b is not representable via case analysis
4. Combine into full theorem

## Partial Progress

- Small-case verification (e.g., a=3, b=5 → g=7) by `decide`
- Bézout lemmas for Lean are partially in Mathlib
- Even partial proof (one direction) adds value

## Mathlib Gaps

- Bézout's identity exists but may need glue lemmas
- Modular arithmetic reasoning may require custom tactics
- Representability predicate is new definition
