# Bertrand's Postulate - Computational Verification Bound

## Informal Statement

**Bertrand's Postulate**: For every integer n ≥ 1, there exists a prime p such that n < p < 2n.

This is already proven in Mathlib. However, the **computational gap** remains:

**Claim**: Verify Bertrand's Postulate computationally for all n ≤ 10^6 and formalize the verification certificate in Lean.

## Formalization Target

```lean
theorem bertrand_verified_to_million :
  ∀ n : ℕ, 1 ≤ n → n ≤ 1000000 → ∃ p, n < p ∧ p < 2 * n ∧ Nat.Prime p :=
by
  intro n hn_ge hn_le
  -- Tactic that checks precomputed witness table
  decide
```

## Motivation

Computational verification provides:
1. Independent confidence in the general theorem
2. Explicit witness primes for applications
3. Demonstration of `decide` tactic scaling for number-theoretic bounds

## Known Results

- Bertrand's Postulate is **proven** in Mathlib: `Nat.exists_prime_lt_and_le`
- Computational verification to 10^6 is well within modern hardware
- Primality testing is in P (AKS) and fast in practice (Miller-Rabin)

## Sources

- Mathlib: `Nat.Prime`, `Nat.exists_prime_lt_and_le`
- OEIS A006992 (primes proving Bertrand's postulate)
- Computational number theory: primality certificates

## Attack Strategy

1. Generate witness table: for each n ∈ [1, 10^6], find smallest prime in (n, 2n)
2. Encode table as Lean `def bertrand_witnesses : Fin 1000000 → ℕ`
3. Prove witnesses are correct via `decide` tactic on primality + bounds
4. Reflect main theorem from witness table

## Partial Progress

- Witness generation script (Python/Sage) is standalone artifact
- Even verifying to n ≤ 1000 demonstrates technique
- Primality certificate infrastructure reusable for other problems

## Risks

- Large Lean file (witness table); may need compression or intervals
- `decide` tactic timeout if verification naive
- Mathlib may reject as redundant to general theorem (but certificate value remains)
