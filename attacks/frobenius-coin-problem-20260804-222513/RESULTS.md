# Frobenius Coin Problem (Two Denominations) — Attack RESULTS

Issue: OPE-22 · Attack Lead · session 2026-08-04
Claim under test: **classical (textbook)**, for coprime a,b > 0,
g(a,b) = ab − a − b is the largest non-negative integer NOT representable as
n = a·x + b·y (x, y ≥ 0). This is *not* a discovery; it is a first lab
investigation producing a computational certificate and Lean formalization seed.

## Level A — computational certificate (DONE, >=20 pairs)

`verify_frobenius.py` performs an *exact* bounded DP over [0, a·b] for each pair
(a·b is a covering bound, so the max non-representable below it is exact).

- **C1 — coprime pairs (required):** 22 coprime pairs (a<b, gcd=1) all satisfy
  `max non-representable == a*b - a - b`. Pairs:
  (2,3)(3,4)(2,5)(3,5)(4,5)(5,6)(2,7)(3,7)(4,7)(5,7)(6,7)(3,8)(5,8)(7,8)
  (2,9)(4,9)(5,9)(7,9)(8,9)(3,10)(7,10)(9,10). 22/22 PASS.
- **C2 — min=1 edge convention:** for a=1 (or b=1) every n>=0 is representable
  (the semigroup is all of ℕ); there is *no* positive non-representable integer.
  Classical formula gives `ab−a−b = −1`, recorded as convention
  "g(1,b) = −1 / none". 10/10 PASS (b=2..11).
- **C3 — gcd>1 branch:** for gcd>1 the formula does **not** give a largest gap;
  infinitely many n are non-representable (n not divisible by gcd). Verified on
  6 non-coprime pairs: the formula value is never a largest gap. Branch reject
  as expected. 6/6 PASS.

Overall RESULT: PASS. Exit code 0.

## Level B — Lean formalization seed (DONE, sorry-free)

`proofs/lean-project/ProofLab/Frobenius.lean`:
- `representableBool` (decidable boolean decision procedure, bounded x,y in [0,n]),
- `representable` (abbrev : Bool result = true) — carries a real `Decidable`,
- `frobenius_number a b := a*b - a - b`.
- **Sorry-free** examples closed by `decide` for pairs (3,5)(2,3)(3,4)(2,5)
  (4,5)(2,7)(3,7): frobenius value = ab−a−b; g not representable; window
  (g, ab] fully representable; selected gaps not representable.
- All modules type-check (`lake env lean` rc=0); `lake build ProofLab` passes
  (exit 0). Note: the repo's `proof-lab` *executable* target does not link on
  this Windows host (`leanc.exe` error 206 — long-path, pre-existing, unrelated
  to this work); the library target and all sources are green.

## Level C — full general theorem (NOT done; optional)

The general two-direction theorem (∀ n > ab−a−b, representable n, for all
coprime a,b) is **not yet Lean-checked**. Left as a goal in the file. Doing it
needs the Chicken-McNugget covering proof (finite window + closure under +a/+b)
and a modular argument for the "g not representable" direction. This is a
Formalist-level task, not required for Level A/B acceptance.

## Status

- Mathematical claim status: **informal / heuristic** (computationally certified,
  small Lean instances sorry-free; full general theorem not Lean-gated).
- **No claim / no external communication** (default). This is a textbook result,
  not a lab discovery.
- Catalog entry updated: `status: candidate` → `verified (computational)`.

## Residual risks / honest caveats

1. Level A proves the formula on 22 sampled pairs (and edges), *not* for all
   coprime pairs — this is computational evidence, not a proof.
2. The Python DP is exact to the a·b covering bound; results are riderly correct
   (int arithmetic, no floats).
3. Level B sorry-free examples cover only small pairs; the general theorem is the
   remaining gap (Level C).
4. The general claim is textbook (Graham–Knuth–Patashnik §3.3); no originality
   is asserted.

## Verify commands

    # Level A
    cd Documents/VSCode/open-math-lab
    python attacks/frobenius-coin-problem-20260804-222513/verify_frobenius.py --all-sizes --max-b 60

    # Level B (type-check all sources, build library)
    cd proofs/lean-project
    lake env lean ProofLab/Frobenius.lean
    lake build ProofLab
