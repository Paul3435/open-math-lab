# Catalan Numbers - Recurrence and Closed Form Equivalence

## Informal Statement

The **Catalan numbers** C(n) count various combinatorial structures (binary trees, Dyck paths, polygon triangulations).

**Claim**: Prove equivalence of the recurrence and closed-form definitions:

Recurrence: C(0) = 1, C(n+1) = Σ_{i=0}^{n} C(i) · C(n-i)

Closed form: C(n) = (2n)! / ((n+1)! · n!)

## Formalization Target

```lean
def catalan_rec : ℕ → ℕ
| 0 => 1
| n + 1 => (Finset.range (n + 1)).sum (fun i => catalan_rec i * catalan_rec (n - i))

def catalan_closed (n : ℕ) : ℕ :=
  (2 * n).factorial / ((n + 1).factorial * n.factorial)

theorem catalan_equivalence (n : ℕ) :
  catalan_rec n = catalan_closed n :=
```

## Motivation

- Fundamental sequence in combinatorics
- Demonstrates proof by induction with symbolic computation
- Multiple combinatorial interpretations (all equivalent)

## Known Results

- Well-studied; proofs via generating functions, bijections, or direct induction
- Appears in OEIS A000108
- Many Catalan number properties already in various proof assistants

## Sources

- Stanley, "Catalan Numbers", monograph
- OEIS A000108
- Mathlib: `Nat.factorial`, `Finset.sum`, induction tactics

## Attack Strategy

1. Define `catalan_rec` and `catalan_closed`
2. Verify small cases (n ≤ 5) by `decide`
3. Prove closed form satisfies recurrence via binomial coefficient manipulation
4. Use strong induction to establish equivalence

## Partial Progress

- Small-case verification is standalone
- Either direction (rec → closed or closed → rec) is partial progress
- Binomial coefficient lemmas are reusable Mathlib contributions

## Challenges

- Factorial division in ℕ requires proving divisibility first
- Binomial coefficient algebra may be tedious without automation
- Generating function approach (algebraic proof) may be out of scope

## Mathlib Gaps

- Binomial coefficient identities exist but may need extensions
- Factorial division lemmas may need helper theorems
- Strong induction tactic exists but may need customization
