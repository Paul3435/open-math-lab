# Attack Log: happy-ending-es3 — ES(3)=5 formalize-only (OPE-403)

**Problem ID:** happy-ending-es3  
**Paperclip:** OPE-403  
**Attack Lead:** grok-4.5 via xai-oauth (no fallback)  
**Session start:** 2026-08-24T18:26:00+02:00  
**Branch base:** `ope/402-post-ramsey-wave` (PR #23 still open at attack start)  
**Branch:** `ope/403-happy-ending-es3`

## Problem Statement

Every set of 5 distinct points in ℝ² in general position (no three collinear)
contains 4 points in convex position (none of the 4 lies in conv of the other 3).

**Pin:** `problems/happy-ending-es3/STATEMENT.md`  
**Expected:** known-classical (Erdős–Szekeres 1935). **No novelty claim.**

## Strategy

Formalize-only Lean 4.10.0 + Mathlib v4.10.0:

1. Orientation determinant plumbing (`orient` on `ℝ × ℝ`).
2. Barycentric / point-in-triangle via nonnegative weights.
3. Hull-vertex extraction (lex maximizer) + convex-independence of hull vertices.
4. Case split: hull ≥ 4 (done) vs triangle + 2 interior (residual).

Partial-progress path authorized by STATEMENT / issue: plumbing alone is a complete
deliverable if case bash overruns budget.

## Session Log

### Attempt 1: Full ES(3)=5 case bash

**Goal:** Zero-sorry full theorem.

**Execution:** Built orientation + barycentric + hull vertex lemmas. Full interior
separating-line case bash hit proof-engineering cost (set-equality edge cases,
sign enumeration, KM-free argument that hull has ≥ 3 vertices under GP).

**Outcome:** partial — see Attempt 2.

### Attempt 2: Board-accepted plumbing + hull≥4 partial theorem

**Goal:** Zero-sorry Mathlib-gap plumbing + honest partial main theorem.

**Delivered in `proofs/lean-project/ProofLab/HappyEndingES3.lean`:**

| Lemma / def | Role |
|-------------|------|
| `orient` + identities | 2D orientation determinant |
| `orient_affine3` | affine in last slot |
| `baryA/B/C`, `bary_sum`, `affine_combination_bary` | barycentrics |
| `mem_convexHull_triangle_of_bary_nonneg` | point-in-triangle |
| `not_mem_segment_of_orient` | third vertex off-segment |
| `InConvexPosition4` | STATEMENT convex-position def |
| `IsHullVertex`, `exists_hull_vertex` | extreme points of finite sets |
| `convexIndependent_hull_vertices` | hull vertices ⇒ convex independent |
| `GeneralPosition`, `EsThreeEqFiveStatement` | STATEMENT predicates |
| `es_three_eq_five_of_hull_card_ge_four` | **partial main** (hull ≥ 4) |

**Verify:**
```
cd proofs/lean-project
lake env lean ProofLab/HappyEndingES3.lean   # EXIT=0
lake build ProofLab                          # green
# grep: zero sorry/admit/custom axiom
```

**Outcome:** success on plumbing + partial main; residual triangle case flagged.

## Residual risks / next steps

1. **Triangle + 2 interior:** prove `hullVertices s` has card ≥ 3 under GP+card≥3;
   then DE separating-line orientation sign bash; show the pair on the double side
   with D,E is `InConvexPosition4` / `ConvexIndependent`.
2. Optionally glue to a single `es_three_eq_five` theorem discharging `EsThreeEqFiveStatement`.
3. ES(4)=9 remains out of scope.

## Math honesty

- **Claim status:** none (formalize-only, known classical).
- **Novelty:** none.
- **Completeness:** PARTIAL — plumbing complete zero-sorry; full ES(3)=5 open on interior case.
