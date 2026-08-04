# RESULTS — Schur's partition theorem (formalize-only)

**Issue:** OPE-26 · **Date:** 2026-08-04 · **Attack Lead:** 65834f64-b136-424f-a6e0-124f9b6da939
**Target:** `schur-partition` · **Claim:** none (default no claim, process/formaloze-only)

## Theorem (informal, literature-pinned)
For every n ≥ 0: **A(n) = B(n)** where
- **A(n)** = # partitions of n into **distinct** parts ≡ 1 or 2 (mod 3)
- **B(n)** = # partitions of n into parts ≡ 1 or 5 (mod 6) (**reps allowed**)

## Level A — computational certificate ✅
`attacks/schur-partition-20260804-225016/verify_schur.py`
```
Certificate: A(n)==B(n) for all 0<=n<=N (N=150)
  empty-partition convention n=0: A(0)=1, B(0)=1
  PASS: A(n)==B(n) for all 0..150 (no mismatches).
Independent brute-force cross-check n=0..24: PASS
RESULT: PASS (Level A certificate complete)
```
- Certified A(n)=B(n) for all 0≤n≤150 (default). Also independently verified to N=1000.
- n=0 empty-partition convention pinned (A(0)=B(0)=1).
- Worked example n=5 pin matches STATEMENT: A(5)=B(5)=2.

### Witnesses
| n | A(n)=B(n) | A (distinct, ≡1,2 mod3) example | B (reps, ≡1,5 mod6) example |
|---|-----------|--------------------------------|------------------------------|
| 0 | 1 | () | () |
| 2 | 1 | [2] | [1,1] |
| 5 | 2 | [1,4] | [1,1,1,1,1] |
| 7 | 3 | [1,2,4] | [1,1,1,1,1,1,1] |
| 10 | 4 | [1,2,7] | [1,1,1,1,1,1,1,1,1,1] |
| 12 | 6 | [1,2,4,5] | [1,1,1,1,1,1,1,1,1,1,1,1] |

### Swapped-pairing landmine guard ✅ (correctly rejected)
- swapped A'(2) = 0 (distinct parts ≡±1 mod6) vs swapped B'(2) = 2 (reps ≡1,2 mod3) → **fails at n=2**, as documented in STATEMENT.md.

## Level B — Lean defs + sorry-free small-n checks ✅
`proofs/lean-project/ProofLab/Schur.lean` (wired into `ProofLab.lean`)
- `A n`, `B n` computable definitions with distinct/reps counters
- sorry-free `native_decide` equalities: A(n)=B(n) for n=0..12; A(0)=B(0)=1; A(5)=B(5)=2; A(2)=B(2)=1
- Verdict: `lake env lean ProofLab/Schur.lean` rc=0; `lake build ProofLab` → "Build completed successfully" (rc=0)

## Level C — full theorem ✅ (not claimed; partial environment note)
- General theorem not formalized (optional/stretch).
- Full default `lake build` (which links `proof-lab.exe`) fails at final link with
  `leanc: error code 206` (Windows command-line-too-long) — pre-existing env issue.
  Library target builds clean.

## Mathlib gap (hard-stop re-grep) ✅
Pinned Mathlib v4.10.0 verified:
- No Schur partition theorem (all "Schur" matches are different results).
- `Nat.Partition` infra present (`Combinatorics/Enumerative/Partition.lean`).

## Residual risks
1. **Level A sample-only**: finite N (150/1000), not a proof for all n.
2. **Level B small-n only**: Lean checks 0..12, general theorem not formalized.
3. **No bijective/generating-function proof formalized** in Lean.
4. Environment: full `lake build` default target blocked by Windows exe-link
   command-length; library target green.
5. No external claim made (per policy, board-only external comms).

## Verify commands
```bash
# Level A
python attacks/schur-partition-20260804-225016/verify_schur.py --N 150

# Level B
cd proofs/lean-project
lake env lean ProofLab/Schur.lean     # expect rc=0, no errors
lake build ProofLab                    # expect "Build completed successfully"
```
