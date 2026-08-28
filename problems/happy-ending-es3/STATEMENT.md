# Formalize the Happy Ending theorem, small case: ES(3)=5

**id:** `happy-ending-es3`
**Pinned:** 2026-08-24 (Research Director OPE-402, ratifying Scout shortlist OPE-390 / PR #21)
**Status:** approved wave PRIME — formalize-only, no novelty claim

## Informal statement (literature-pinned)

**Happy Ending theorem, case ES(3)** (Erdős & Szekeres 1935; Klein's observation):

Every set of **5 distinct points** in the plane in **general position** (no three
collinear) contains **4 points in convex position**, i.e. 4 of the points are the
vertices of a convex quadrilateral.

Notation: `ES(n)` = least N such that any N points in general position contain n
points in convex position. Classical result: `ES(3) = 5`.

## Definition pins (do NOT "fix" without literature)

1. **Distinct points**: all 5 points pairwise different. Duplicate points are not
   allowed and are not handled by degenerate-case reasoning.
2. **General position**: no three of the five points are collinear. Nothing more
   (no "no 4 concyclic", no integrality assumptions).
3. **Convex position / convex quadrilateral**: 4 points p1..p4 are in convex
   position iff each is an extreme point of `{p1,p2,p3,p4}` — equivalently, none
   lies in the convex hull of the other three (which under general position means
   strictly inside the triangle of the others). All 4 must be used as vertices;
   ordering/cyclic permutation is irrelevant.
4. **Ambient**: ℝ² (affine plane). Do not formalize over ℤ²/ℚ² unless the Lean
   statement is parameterized and instantiated at ℝ.

## Worked example (sanity pin)

Take 5 points: hull = triangle {A,B,C}, interior {D,E}. Then D,E,A,B cannot be a
convex 4-gon (D,E interior), but A, D, E, and the correct third vertex form one:
the line through D and E leaves one triangle vertex (say C) alone on one side;
then {C, D, E} ∪ ... — the standard argument shows some 4-subset works. Machine
check: random sampling of 5-point general-position configurations never yields a
counterexample (verify script may certify finitely many rational instances only,
as process fuel — NOT a substitute for the Lean proof).

## Landmines (OPE-12/OPE-25 class)

- The swapped/weaker statement "any 5 points contain 4 points forming *some*
  quadrilateral (possibly non-convex)" is TRIVIAL/false-different — do not prove
  that instead. Convexity of the 4-subset is the content.
- Degenerate hull sizes: hull can have 3, 4, or 5 vertices. Hull=5 is trivially
  done (any 4 hull vertices), hull=4 immediate, hull=3 is the real case.
- ES(4)=9 (Szekeres–Peters 2006) is computer-assisted and OUT OF SCOPE except as
  an explicitly-labeled stretch; its proof is a large case split.

## Formalization target

State and prove in Lean 4 + Mathlib:

```
theorem es_three_eq_five :
    ∀ q : Set ℝ² (or Fin 5 → ℛ²), q.Finite → q.card = 5 →
      (∀ x y z, x ∈ q → y ∈ q → z ∈ q → x ≠ y → y ≠ z → x ≠ z →
        ¬ Collinear ℝ ({x, y, z} : Set ℝ²)) →
      ∃ s ⊆ q, s.Finite ∧ s.card = 4 ∧ ConvexPosition ...
```

Exact Lean shape is the Attack Lead's call once pinned against Mathlib names;
keep defs 1:1 with this file.

### Suggested proof skeleton (classical, elementary)

- Case hull size ≥ 4: pick 4 hull vertices → convex. (`Nat` case analysis)
- Case hull = triangle {A,B,C} with interiors {D,E}: WLOG the line `DE`
  intersects sides AB and AC (relabeled); then B, C, E, D... precisely: the line
  through D and E separates one vertex from the other two; the two separated-
  side vertices together with D and E are in convex position. Orientation signs
  (`det [p2 - p1; p3 - p1]`) decide everything; fully decidable case bash.

### Mathlib plumbing (the genuine contribution)

No Erdős–Szekeres/happy-ending content exists in Mathlib v4.10.0 (gap re-confirmed
by Scout, OPE-390). Needed glue that does not exist yet:
- orientation/orient sign of a point triple in ℝ² (`Orientation`-free version OK:
  `Real.sign_det`),
- strict point-in-triangle via three same-sign orientation tests,
- "extreme point of a 4-point set" ↔ "not in conv of the other 3".
This plumbing is itself reusable Mathlib-gap material — flag it in the PR body.

## Honest frame

- **formalize-only**. Known classical (1935). Default **no claim**.
- Partial-progress friendly: the ℝ² orientation plumbing alone, merged cleanly,
  is a complete deliverable if the full case bash overruns budget.
- Budget cap: ~220k tokens (dossier). Stop at budget; hand to Adversarial Reviewer.

## Acceptance gates

1. Statement matches THIS file (distinctness + general-position hypotheses explicit).
2. Zero `sorry`/`admit`/axiom; `lake env lean <file>` EXIT=0; `lake build ProofLab` green.
3. Branch `ope/<id>-happy-ending-es3`, PR opened (board merges).
4. ATTACK_LOG + ledger + catalog updated; residual risks listed.
