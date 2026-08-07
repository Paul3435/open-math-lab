# Schur number S(2)=5 / S(3)=14 (formalize-only)

**id:** `schur-number`

## Informal statement

For a positive integer `k`, the **Schur number `S(k)`** is the largest `n` such that
the interval `[1, n]` can be partitioned into `k` sum-free sets (no set contains distinct
`x, y` with `x + y` also in the set). Equivalently, `S(k)+1` is the least `N` such that
every `k`-colouring of `[1, N]` contains a monochromatic solution to `x + y = z`.

Known values / bounds (`S(1)=1`, and the first four are exact):
- `S(2) = 4`   (i.e. the least `N` with `N ≥ S(2)+1 = 5` forces a monochromatic
  `x+y=z`; `{1,2,3,4}` splits `{1,4},{2,3}`). *(Some authors index as `S(2)=5` — pin
  the convention in the statement.)*
- `S(3) = 13`  (least `N = 14` forces it; classical 3-colouring of `[1,13]` exists).
- `S(4) = 44`  (Heule 2018, SAT-certified; `N = 45` forces).

Recommended target for a Lean/cert heap: prove the small finitary cases `S(2)`/`S(3)`
(`S(4)` via a certified SAT proof if feasible), framed as a Mathlib-style
`schur_number` contribution.

## Why feasible?

- Fully decidable and bounded: a colouring of `Fin n` with `k` colours is a finite
  object; "each colour class sum-free" is a decidable predicate.
- For `S(2)`/`S(3)` the search space is tiny — clean hand/`decide` proof.
- Strong precedent for `S(4)=45` via SAT (Heule) gives a certificate strategy that
  scales beyond the hand cases.
- Fits "finite computational conjecture with tight bounds" from the Scout sources.

## References

- Schur, "Über die Kongruenz x^m + y^m ≡ z^m (mod p)" (1916) — origin of the numbers.
- Heule, "Schur Number Five" (AAAI 2018) — SAT proof for `S(4)=44`/`S(5)=160`?
  (`S(5)` lower bound is a famous hard SAT case).
- OEIS A030126 (Schur numbers: 1,4,13,44,…). Indexing convention must be pinned.

## Novelty pre-screen (OPE-28)

- **Mathlib grep (local pin v4.10.0):** no `schurNumber` / "Schur number" combinatorial
  theorem. The only `Schur*` hits are unrelated algebra/geometry
  (`GroupTheory/SchurZassenhaus.lean`, `LinearAlgebra/Matrix/SchurComplement.lean`,
  `CategoryTheory/Preadditive/Schur.lean`). Confirmed gap.
- **Status:** `expected: known-classical` → frame as **`formalize-only`**. Do **not**
  re-fund as novel research; value is a genuine Mathlib-style contribution (small
  finitary Schur numbers with decidable witnesses).