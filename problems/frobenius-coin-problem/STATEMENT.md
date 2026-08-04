# Frobenius coin problem (two denominations)

**id:** `frobenius-coin-problem`  
**sprint:** OPE-21 / OPE-22  
**status:** shortlisted → attack

## Informal statement

Let a, b be coprime positive integers (gcd(a,b)=1). A non-negative integer n is
**representable** if there exist x,y ∈ ℕ₀ with

    n = a·x + b·y.

The **Frobenius number** g(a,b) is the largest integer that is *not* representable.
**Claim (classical):**

    g(a, b) = a·b − a − b.

Equivalently:

1. ab − a − b is not representable;
2. every integer n > ab − a − b is representable.

**Scope hard stop:** exactly **two** denominations. Three or more is NP-hard under
natural formulations and is **out of scope** for this lab bet.

## Why this bet (director)

- Not attacked before in this lab (unlike EW, sum-free, caterpillars).
- Prime feasibility dossier (90/100): constructive, Mathlib-friendly (gcd, Bézout).
- Clear partial milestones: small pairs by compute → non-representability → full formula.
- Low crackpot surface: textbook theorem (Concrete Mathematics §3.3), not a conjecture.

## Formalization target (Lean 4 sketch)

```lean
def Representable (a b n : ℕ) : Prop :=
  ∃ x y : ℕ, n = a * x + b * y

def frobeniusTwo (a b : ℕ) : ℕ := a * b - a - b

theorem frobenius_two_coins
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hcoprime : Nat.Coprime a b) :
    (¬ Representable a b (frobeniusTwo a b)) ∧
    (∀ n, frobeniusTwo a b < n → Representable a b n) := by
  sorry
```

Prefer Mathlib names (`Nat.Coprime`) once checked against installed toolchain.

## Attack plan (budget-capped)

1. **Warmup compute:** for several coprime pairs (e.g. (3,5)→7, (4,7)→17, (5,8)→27),
   enumerate representable set up to ab and verify formula + maximality.
2. **Non-representability argument:** ab−a−b ≡ −a (mod b) and ≡ −b (mod a); no
   non-neg solution.
3. **Representability for n > g:** standard residue / Chicken McNugget path using Bézout.
4. **Lean:** definitions + small `decide` examples first; main theorem only if lemmas close.
5. **Stop** at token/time budget; hand residual gaps to Formalist/Reviewer. Default **no claim**.

## Success criteria (honest)

| Level | Criteria | Status label |
|-------|----------|--------------|
| A | Python/cert checks for ≥20 coprime pairs + edge cases (min(a,b)=1) | `heuristic` OK |
| B | Lean defs + examples sorry-free; main thm may sorry | `informal` |
| C | Full `lake build` of main theorem | `formalized` (still no external claim w/o board) |

## References

- Graham, Knuth, Patashnik — *Concrete Mathematics*, §3.3
- OEIS A028387 (related Frobenius values)
- Mathlib: `Nat.gcd`, `Nat.Coprime`, Bézout

## Residual risks (pre-attack)

- ℕ subtraction `a*b - a - b` needs a,b ≥ 1 and care when a=1 (g=−1 conventionally /
  every n≥0 representable — pin convention in code and Lean).
- Confusing “positive combination” vs non-negative.
- Scope creep to ≥3 coins.
