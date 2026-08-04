# Attack Log: schur-partition — Schur's partition theorem (formalize-only)

## Problem Statement
Classical 1926 theorem (I. Schur; Andrews, *The Theory of Partitions*): for every
n ≥ 0, **A(n) = B(n)** where
- **A(n)** = # partitions of n into **distinct** parts ≡ 1 or 2 (mod 3)
- **B(n)** = # partitions of n into parts ≡ ±1 (mod 6) (i.e. 1 or 5 mod 6), **reps allowed**

Source: `problems/schur-partition/STATEMENT.md` (2026-08-04 pin)
Difficulty: formalize-only / process — known classical theorem, NOT a discovery
Feasibility score: 5.0/5 (formalizable 18, ...), budget ≈ 220k tokens

## Meta
**Attack Lead:** 65834f64-b136-424f-a6e0-124f9b6da939
**Session start:** 2026-08-04
**Levels:** A (computational cert, required) · B (Lean defs + small-n checks) · C (full theorem, optional)
**Claim:** none (default no claim)

## Strategy Selection
**Primary lens:** partition-theory (generating-function / DP over restricted parts).
**Why:** The two sides differ by (i) distinctness and (ii) congruence modulus
(3 vs 6). A direct DP over allowed part sets plus an independent brute-force
enumerator gives an exact finite certificate without formal bottom-up proof of
the generating-function identity. Lean seed reuses the same counting defs.

## Session Log

### Step 1 — Level A: exact computational certificate (PASS)
`verify_schur.py` implements **two independent** counting methods:
- DP over allowed parts (A: descending loop → distinctness; B: ascending loop → reps)
- brute-force partition-list enumeration (small n, independent cross-check)

Checks:
- A(n)==B(n) for all 0≤n≤150 (default N=150 ≥ 50); also verified to N=1000
- n=0 empty-partition convention: A(0)=B(0)=1
- n=5 worked example pin from STATEMENT: A(5)=B(5)=2
- witnesses for n=0..12 printed
- **swapped-pairing guard**: swapped A'(2)=0 vs swapped B'(2)=2 → fails at n=2,
  confirming the definition landmine is correctly rejected
**Outcome:** PASS (exit 0). Level A satisfied.

### Step 2 — Level B: Lean defs + sorry-free small-n checks (PASS)
`proofs/lean-project/ProofLab/Schur.lean`:
- `partAllowedA` (≡1,2 mod 3) and `partAllowedB` (≡1,5 mod 6) predicates
- `countDistinct` (structural recursion, distinct parts) and `countUnbounded`
  (multiplicity 0..t/p) counters
- `A n` and `B n` defs
- sorry-free `native_decide` checks: A(0)=B(0)=1, A(n)=B(n) for n=1..12,
  A(5)=B(5)=2, A(2)=B(2)=1
- Wired into `ProofLab.lean` import graph
**Outcome:** `lake env lean ProofLab/Schur.lean` rc=0; `lake build ProofLab` rc=0.

### Step 3 — Level C: full theorem lake build (partially blocked)
The general theorem (all n) is NOT formalized — Level C is optional/stretch and
requires a full generating-function or bijection proof in Lean. Additionally the
default `lake build` target fails at the final `.exe` link with `leanc: error
code 206` (Windows "command line too long" when linking `proof-lab.exe` against
all of Mathlib) — a pre-existing environment issue, unrelated to Schur.lean. The
library target (`lake build ProofLab`) succeeds.

### Mathlib gap (hard-stop check)
Re-grepped the pinned Mathlib v4.10.0 tree:
- No "Schur partition theorem" (matched "Schur" hits are RepresentationTheory,
  GroupTheory/SchurZassenhaus, LinearAlgebra/SchurComplement — different results)
- `Combinatorics/Enumerative/Partition.lean` provides `Partition n` infra
**Gap confirmed.** Consistent with OPE-25 scout.

## Summary
**Status:** Level A + B complete; claim status: heuristic/informal (finite
certificate + small-n Lean checks; general theorem not Lean-gated).
**Confidence:** high for the sampled result (exact arithmetic, classical known
theorem).
**Next step:** optional Formalist Level C for full theorem; otherwise issue is
process-complete (formalize-only, no claim).
**Remaining risks:** Level A is sample-only (finite N); Level B is small-n only;
general theorem unformalized; no bijective proof formalized.

## Resources Consumed
~25k tokens (well under 220k budget) · trivial compute · single session.

## Handoff
**Handoff to:** Research Director / board (no Reviewer needed — Level A is
computational; default no claim). PR opened for review.
