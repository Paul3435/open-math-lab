# RESULTS — krenn-gu Level B timeboxed (8,3) search (OPE-1038)

**Issue:** OPE-1038 · **Date:** 2026-09-06 · **Role:** Attack Lead
**Prior:** Scout OPE-1028 prime; Director OPE-1032 / OPE-1037 CONTINUE; Formalist OPE-1033 Level A (`ProofLab/KrennGu.lean`, PR #101)
**Target:** STATEMENT Level B option 2 — bounded `EqSystem` search at `(N,D)=(8,3)`
**Claim:** none. **Prize claim:** none. **Novelty:** none.

Pin: `catalog/problems/krenn-gu/STATEMENT.md` Level B option 2.
Encoding reused, not re-derived: `Weight` / `EqSystem` / `pmSum` / `IsPerfectMatchingEdges`
(`edgeWeight` reads smaller-index endpoint first, matching Lean).

## Method

**exhaustive-on-a-tiny-weight-set + heuristic local search** over the decidable
ring `{-1,0,1}` (STATEMENT stop-rule). Not SAT. Not Gröbner (no solver / no Sage
on this host). Unrestricted `Complex` was **not** started.

Python replica: `search_eqsystem.py`. Machine report: `search_report.json`.

## Sanity (encoding still compiles as a search)

Even-cycle unit monochromatic `d=2` is `EqSystem` in this replica, matching
Lean `cycle4_eqSystem` for `n=4` and the same construction for `n=6,8`:

| n | d | perfect matchings | colourings | EqSystem |
|---|---|-------------------|------------|----------|
| 4 | 2 | 3 | 16 | yes |
| 6 | 2 | 15 | 64 | yes |
| 8 | 2 | 105 | 256 | yes |

Fast monochromatic-support residual agrees (residual 0). Lean was **not**
edited this ticket (`lake` optional; skipped).

## What was searched

### (N,D)=(8,3), ring `{-1,0,1}`

1. **Exhaustive signed 1-factors, monochromatic.** Circle 1-factorization of
   `K_8` (7 factors). Every 3-tuple of factors (`C(7,3)=35`) with each factor
   a distinct colour; each of 12 edges has weight `±1` on that mono slot;
   all other slots 0. `35 × 2^12 = 143360` patterns, **exhausted** (125440
   skipped because some colour-class sign-product is `-1`, so a constant
   colouring already fails). Evaluated via induced colourings of the support
   perfect matchings (5 support PMs on the first triple). **0 witnesses.**
   Best L1 residual among constant-passing patterns: **2** (mixed-colouring
   leak; example first-bad colouring `(1,1,1,0,0,2,2,1)` on factors `(0,1,2)`).

2. **C_8 `d=2` unit cycle plus one extra signed 1-factor in colour 2.**
   7 candidate extra factors × `2^4` signs, skipping extra factors that reuse
   a cycle edge. **112 patterns, exhausted. 0 witnesses.** Best residual **2**.

3. **Heuristic hill-climb, monochromatic slots only.** Seeded at the even-cycle
   `d=2` embedding in `d=3`; random `{-1,0,1}` mutations. 48 restarts, 1182
   steps, timebox stop. **0 witnesses.** Best residual **1** (the missing
   constant colour-2; first-bad `(2,2,2,2,2,2,2,2)` after a full 6561-colouring
   scan). This is the known `C_8` `d=2` witness sitting inside `d=3`, not a
   `(8,3)` solution.

Bichromatic local search at `(8,3)` was **not reached** (the 120s `(8,3)`
budget ended on the mono hill-climb).

### Fallback `(N,D)=(6,3)`, same ring (ticket: fall back once, then stop)

Reported literature `C(6)=2`; this is **not** a prize claim and **not** Lean
`¬ EqSystem 6 3 W` (XOR not taken).

1. Signed 1-factors: `C(5,3)=10` triples × `2^9=512` → **5120 exhausted.
   0 witnesses.** Best residual **1**.
2. Cycle `d=2` + extra signed 1-factor colour 2: **40 exhausted. 0 witnesses.**
   Best residual **1**.
3. Heuristic hill-climb, **bichromatic** slots allowed: 881 restarts, 22020
   steps, timebox stop. **0 witnesses.** Best residual **1** (again the
   unused third colour on the even-cycle seed).

Wall clock: **165.085s**. Seed 1038.

## What was not searched

- Unrestricted `Complex` weights (ticket: will explode; do not start).
- Full `{-1,0,1}` tensor on `K_8`: 28 edges × 9 colour-pairs = 252 ternary
  slots (`3^252`). Not enumerated. A clean negative here is **only** on the
  stated finite supports above.
- Integer weights outside `{-1,0,1}`; rational / Gaussian-integer phases.
- SAT / Gröbner / numerical `C` optimisation / PyTheus.
- Lean finite nonexistence (`¬ EqSystem 6 3 W` / `¬ EqSystem 8 3 W`). XOR
  not taken; Formalist work; **not sorry-ed**.
- Namesake `∀ even N≥6, ∀ D≥3, ¬ ∃ W, EqSystem N D W` — **out of v1**.
- Hou–Zeng PFC. Sun 1-3-5. AlphaProof `d≥n`. Kevin M. `n=4,d≥4`. Bogdanov
  positive-reals (as a namesake). Archive.* / formal-conjectures.

## Residual risks

1. `(8,3)` over `ℂ` (and even over `ℤ` with larger support) remains open.
   Literature window `2 ≤ C(8) ≤ 3` is unchanged. This log does **not**
   close that window.
2. Best residual 1 on local search is the even-cycle `d=2` embedding — a
   known positive example, not evidence that `d=3` is close.
3. Signed 1-factor triples leak on mixed colourings (residual 2). Cancellation
   on that support was never enough, for every sign pattern with constant
   colourings = 1.
4. Python replica could in principle diverge from Lean `native_decide` on
   a future witness; sanity on `C_4`/`C_6`/`C_8` `d=2` is the calibration.
5. Default **no claim**. Do **not** email Krenn / Leitner. Board is the only
   external-claim authority (`docs/CLAIM_POLICY.md`). €3,000 / Best-Paper
   €1,000 **not claimed**. Best-Paper deadline End of August 2024 treated as
   not live.

## Disposition

Honest partial / clean negative on the stated finite weight-sets = **success**
for this ticket. Level B option 2 landed as a search log. No software-confirmable
`(8,3)` witness. No Lean namesake. No second prime.
