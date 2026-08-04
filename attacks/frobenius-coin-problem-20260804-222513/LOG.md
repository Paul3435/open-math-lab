# Attack Log: frobenius-coin-problem — Two-Denomination Frobenius Number

## Problem Statement

For coprime positive integers a, b, the Frobenius number g(a,b) is the largest
non-negative integer not representable as n = a·x + b·y (x, y ≥ 0).
**Claim (classical, textbook):** g(a,b) = ab − a − b.

**Source:** catalog/problems/frobenius-coin-problem (Graham-Knuth-Patashnik §3.3)
**Difficulty:** easy (textbook) — computational cert + Lean seed
**Feasibility score:** 9/10

## Meta
**Attack Lead:** 65834f64-b136-424f-a6e0-124f9b6da939
**Session start:** 2026-08-04
**Token budget:** 180k (dossier) — used ≪ budget
**Levels:** A (computational, required) · B (Lean defs+examples, stretch) · C (full theorem, optional)

## Strategy Selection
**Primary lens:** number-theory (divisibility / modular structure / Bézout).
**Why:** Frobenius is a divisibility/semigroup problem; the bounded-search DP is a
direct, exact certificate of "max non-representable", and the Lean seed reuses
that predicate.

## Session Log

### Step 1 — Level A: exact computational certificate
Wrote `verify_frobenius.py` with an exact DP over [0, a·b] (a·b is a covering
bound, so the max non-representable there is guaranteed exact). Three checks:
- C1 coprime pairs: 22/22 satisfy max-non-rep = ab−a−b.
- C2 min=1 edge: a=1 → all n representable; formula = −1 recorded as the
  "g(1,b)=none" convention. 10/10.
- C3 gcd>1 branch: formula never a largest gap; branch rejected. 6/6.
**Outcome:** PASS (exit 0). Level A satisfied (≥20 coprime pairs + edges).

### Step 2 — Level B: Lean formalization seed, sorry-free
`proofs/lean-project/ProofLab/Frobenius.lean`:
- `representableBool` — decidable bounded decision procedure;
- `representable` (abbrev) — Prop backed by a real `Decidable` so `decide` closes
  instances;
- `frobenius_number a b := a*b - a - b`.
- Sorry-free `decide` examples for (3,5)(2,3)(3,4)(2,5)(4,5)(2,7)(3,7): the value
  ab−a−b, its non-representability, selected gaps, and the full window (g, ab].
- Modules type-check (`lake env lean` rc=0); `lake build ProofLab` passes.
**Pitfall hit:** a plain `def` for `representable` blocked `Decidable` synthesis;
switching to `abbrev` (reducible) fixed it. Also `native_decide` wouldn't
synthesize the instance while `decide` did — used `decide`.
**Outcome:** Level B satisfied.

### Step 3 — Level C: full general theorem (deferred)
The general two-direction theorem is not yet Lean-proved (needs Chicken-McNugget
covering + modular argument). Documented as a goal in the file; this is a Formalist
task and optional for this issue.

## Summary
**Status:** Level A + B complete; claim status informal/heuristic (not Lean-gated
for the general theorem).
**Confidence:** high for the sampled result (exact arithmetic, textbook-known).
**Next step:** optional Formalist Level C; otherwise hand to Reviewer only if the
board wants the general claim Lean-gated.
**Remaining risks:** sample-only Level A; small-pair-only Level B; general theorem
not formalized.

## Resources Consumed
~15k tokens (well under 180k budget) · trivial compute · single session.

## Handoff
**Handoff to:** Research Director / board (no Reviewer needed — Level A is
computational; no claim asserted). PR opened for review.
