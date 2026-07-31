# Board Veto — OPE-12 Erdős-Woods "Solution"

**Date**: 2026-07-30  
**Issue**: OPE-12  
**Decision**: VETO — No claim packet from this attack

## Problem

OPE-12 claimed k=16 is an Erdős-Woods number with minimal witness **a=5** under an **incorrect definition**.

### Definition Used (WRONG)

The attack implemented:

> k is Erdős-Woods if ∃a such that ∀i ∈ [a, a+k], ∃p ≤ k prime: (p | i) ⊕ (p | a)

Translation: "For every integer in [a, a+k], there exists a prime p ≤ k that divides exactly one of {i, a}."

This is **not** the Erdős-Woods property.

### Correct Definition (Standard Literature)

From Erdős & Woods (1980):

> k is Erdős-Woods if ∃a such that ∀j ∈ (a, a+k), gcd(j, a) > 1 ∨ gcd(j, a+k) > 1

Translation: "Every integer in the open interval (a, a+k) shares a prime factor with at least one of the endpoints {a, a+k}."

### Why This Matters

1. **Mathematical correctness**: The XOR condition is a different number-theoretic property with no literature precedent.
2. **False witness**: Under the wrong definition, a=5 may satisfy the condition. Under the **correct** definition, the minimal witness for k=16 is **a=2184** (known since 1980).
3. **Epistemic integrity**: Claiming a "novel" witness when using a non-standard definition violates the lab's charter.

## Evidence of Error

### Attack artifacts claim a=5

From `RESULT.md`:
```
Result: k=16 is Erdős-Woods number with minimal witness a=5
```

From `witness_5.json`:
```json
{
  "k": 16,
  "witness": 5,
  "verification_status": "valid",
  ...
}
```

### Verification script used wrong condition

`verify.py` implements:
```python
def has_distinguishing_prime(a, j, k):
    primes = get_primes_up_to(k)
    for p in primes:
        if (j % p == 0) != (a % p == 0):  # XOR check
            return True
    return False
```

This checks "exactly one of {j, a} is divisible by p", not "j shares a factor with a or a+k".

### Adversarial review rubber-stamped it

`ADVERSARIAL_REVIEW.md` verified the implementation against the **stated** definition but did not catch that the definition itself was wrong:

```
Verification Status: CONFIRMED
The witness a=5 is mathematically valid under the stated definition.
```

Reviewer failed the lab's epistemic standard: verifying an implementation of a wrong definition is not acceptable diligence.

## Correct State of Knowledge

**Literature fact**: k=16 is an Erdős-Woods number with minimal witness **a=2184**.

**Verification under correct definition**:
- Endpoints: a=2184 = 2³×3×7×13, a+k=2200 = 2³×5²×11
- Interval: (2184, 2200) contains 15 integers
- Each of {2185, 2186, ..., 2199} shares at least one prime factor with 2184 or 2200

See `verify_correct.py` in this directory for a reference implementation.

## Failure Mode Analysis

1. **Definition sourcing**: The attack did not cite the original Erdős & Woods (1980) paper or cross-check against OEIS A059756.
2. **Sanity check**: Finding a=5 when literature reports a=2184 should have triggered immediate skepticism.
3. **Reviewer scope**: Adversarial review verified consistency between code and stated definition, but did not validate the definition against literature.

## Board Decision

**No claim packet shall be prepared from OPE-12.**

This attack is a **negative calibration example** for the lab:
- Failed attacks with clear lessons are valuable.
- "Solved" claims without literature grounding are epistemic failures.
- Adversarial review must check definitions, not just implementations.

## Remediation (OPE-15)

Scout role executes:
1. Rewrite `problems/erdos-woods/STATEMENT.md` with correct definition and a=2184.
2. Update `catalog/problems.json`: status → `candidate`, note the definition bug.
3. This veto document.
4. Reference verification script for a=2184 under correct definition.

## Out of Scope

OPE-12 artifacts remain in `attacks/erdos-woods-20260730-125506/` as historical record. Do not delete; do not celebrate.

---

**Signed**: Board (Paul)  
**Authority**: `docs/CLAIM_POLICY.md` § Veto power
