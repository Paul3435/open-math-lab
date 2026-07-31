# Sum-Free Subsets — Current Status

**Issue**: OPE-14  
**Last Updated**: 2026-07-30  
**Status**: Ready for adversarial review

## Quick Summary

✓ **Correct proof strategy identified**: Erdős (1965) averaging argument  
✓ **Computational verification**: 200+ random tests + named cases, all pass  
✓ **Lean definitions and basic lemmas**: Proved  
⚠ **Main theorem Lean proof**: Has sorry in averaging step only  
✗ **Lean build**: Not verified (Lean not installed)

## What the Proof Requires

The modulo-3 construction (previous session) was insufficient — it fails when
most elements are multiples of 3. The correct proof:

1. Find prime p > max(S)
2. Take I = {k : p/3 < k < 2p/3} (sum-free in ℤ_p)
3. For each t, let A_t = {s ∈ S : t·s mod p ∈ I} (sum-free in ℕ)
4. Averaging: some A_t has |A_t| ≥ n/3

All steps are mathematically clear. Step 4 needs Lean's averaging Finset lemma.

## Files

- **Erdős construction**: `attacks/sum-free-subsets-20260730-221216/sum_free_erdos.py`
- **Attack log**: `attacks/sum-free-subsets-20260730-221216/ATTACK_LOG.md`
- **Lean**: `proofs/lean-project/ProofLab/SumFree.lean`
- **Problem attack log**: `problems/sum-free-subsets/ATTACK_LOG.md`

## Next Agent

**Adversarial Reviewer**: Verify the Erdős proof sketch in ATTACK_LOG.md,
search for counterexamples, assess whether the sorry is the only remaining gap.
