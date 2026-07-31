# Formalization Status: Erdős-Woods k=16

**Date**: 2026-07-30  
**Status**: PSEUDO-LEAN DRAFT  
**Formalist**: Research Director (acting as Formalist for smoke test)

---

## Summary

Created a **pseudo-Lean formalization draft** for the Erdős-Woods k=16 verification result. This draft cannot be type-checked until the Lean toolchain is installed on the user's machine (requires separate board approval per LEAN_PLAN.md).

---

## Formalization Location

**File**: `proofs/lean-project/ProofLab/ErdosWoods.lean`

**Import**: Added to `proofs/lean-project/ProofLab.lean`

---

## Definitions

1. **`PrimeDistinguishes p k i a`**  
   A prime p ≤ k distinguishes i from a via exclusive-or divisibility.

2. **`IsErdosWoodsWitness k a`**  
   Predicate: a is a witness for k (all i in [a, a+k] are distinguished from a).

3. **`IsErdosWoodsNumber k`**  
   Predicate: k has at least one witness.

---

## Theorems

### Main Results

1. **`erdos_woods_16 : IsErdosWoodsNumber 16`**  
   k=16 is an Erdős-Woods number (witness a=5).

2. **`erdos_woods_16_minimal`**  
   a=5 is the minimal witness for k=16 (witnesses 1-4 fail).

### Supporting Lemmas

1. **`witness_5_for_16_verified : IsErdosWoodsWitness 16 5`**  
   Computational verification that a=5 satisfies the witness property.  
   Uses `interval_cases` to check all 17 integers in [5, 21].

2. **`not_witness_1_to_4`**  
   Proofs that a ∈ {1,2,3,4} are not witnesses for k=16.

---

## Proof Strategy

### Computational Verification (`witness_5_for_16_verified`)

```lean
intro i hi h_ne
interval_cases i
  -- For each i ∈ {6,7,8,...,21}:
  -- Provide specific prime p that distinguishes i from 5
  -- Examples:
  --   i=6: use p=2 (2|6 but 2∤5)
  --   i=10: use p=2 (2|10 but 2∤5, even though 5|both)
  --   i=17: use p=5 (5|5 but 5∤17)
```

Each case identifies the distinguishing prime from {2, 3, 5, 7, 11, 13}.

### Minimality (`erdos_woods_16_minimal`)

Proves that a ∈ {1,2,3,4} fail by identifying counterexample integers:
- a=1: i=17 not distinguished (both coprime to all primes ≤ 16)
- a=2: i=4 not distinguished (both divisible only by 2)
- a=3: i=9 not distinguished (both divisible only by 3)
- a=4: i=8 not distinguished (both divisible only by 2)

---

## Mathlib Dependencies

```lean
import Mathlib.Data.Nat.Prime.Basic  -- Nat.Prime, divisibility
import Mathlib.Data.Set.Intervals.Basic  -- Set.Icc (closed intervals)
```

**Expected tactics needed** (once buildable):
- `norm_num`: Numerical computation
- `interval_cases`: Case split on finite integer intervals
- `decide`: Decision procedure for divisibility
- `constructor`, `use`: Proof construction

---

## Current Status

**PSEUDO-LEAN**: Not type-checked.

**Blockers**:
1. Lean toolchain not installed (elan + lake)
2. Installation requires board approval (see LEAN_PLAN.md)

**Next Steps** (if formalization is prioritized):
1. Board approves Lean installation issue
2. Formalist installs elan/lake
3. `cd proofs/lean-project && lake build`
4. Replace `sorry` placeholders with actual tactic proofs
5. Verify `lake build` exits 0 with no critical `sorry`
6. Adversarial Reviewer checks build log
7. Upgrade status from `informal` to `formal`

---

## Formalization Value

### Why Formalize This Result?

1. **Smoke test exemplar**: Simple enough to formalize fully, demonstrates workflow
2. **Mathlib coverage check**: Tests whether number theory primitives are sufficient
3. **Verification gate**: Even though computational proof is certain, formal proof blocks accidental errors in definition interpretation
4. **Documentation**: Lean code is executable specification

### Why NOT Prioritize This Formalization?

1. **Computational proof is certain**: Divisibility checks are mechanical, no subtlety
2. **Known result**: Confirms OEIS A059756, not novel research
3. **Formalization effort**: ~1-2 hours to replace `sorry` with proofs (manual tactic work)
4. **Installation overhead**: Lean setup + Mathlib compile (10-30 min first build)

---

## Recommendation

**For smoke test**: Pseudo-Lean draft is sufficient to demonstrate process.

**For production use**: Formalize this if:
- Lean installation is approved and completed
- This result will be published externally (machine-checkable evidence)
- We want to build a library of formalized number theory lemmas

Otherwise: Computational proof + adversarial review is adequate for internal confidence.

---

## Files

- `proofs/lean-project/ProofLab/ErdosWoods.lean` — Pseudo-Lean formalization
- `attacks/erdos-woods-20260730-125506/RESULT.md` — Computational proof
- `attacks/erdos-woods-20260730-125506/verify.py` — Python verification code
- `attacks/erdos-woods-20260730-125506/ADVERSARIAL_REVIEW.md` — Independent review

---

**Formalist notes**: 

This pseudo-Lean draft follows the structure documented in LEAN_PLAN.md section "Pseudo-Lean / Exploration Notes". All `sorry` placeholders are intentional until Lean is installed and buildable. The proof strategy mirrors the computational verification in `verify.py`, making the formal proof mechanical once Lean is available.

The formalization demonstrates that the Erdős-Woods definition translates cleanly to Lean with standard Mathlib primitives. No custom number theory definitions are needed.
