# Finite graph Ramsey numbers — R(3,3)=6 / R(4,4)=18 (formalize-only)

**id:** `ramsey-r33`

## Informal statement

For integers `k,l ≥ 2`, the Ramsey number `R(k,l)` is the least `N` such that every
2-colouring of the edges of the complete graph `K_N` contains either a red `K_k` or a
blue `K_l`. Small classical values:

- `R(3,3) = 6`  (elementary; the classic "party of six" bound, upper via pigeonhole on
  a vertex's 5 neighbours, lower via the 5-cycle `C5` colouring of `K_5`).
- `R(3,4) = 9`
- `R(4,4) = 18`  (Greenwood–Gleason 1955).

Formalization goal: define `ramsey g k l` / a `ramseyNumber k l`-style notion over
`SimpleGraph (Fin n)` in Mathlib, prove these small finitary values **without `sorry`**,
and support the finite value by a certified exhaustive / backtracking search where the
hand proof is unwieldy (`R(4,4)=18`).

## Why feasible?

- Fully decidable, bounded: every candidate is a 2-colouring of a finite `K_N`; checking
  "no red `K_k`, no blue `K_l`" is decidable by bounded enumeration.
- Mathlib already provides the right infrastructure: `SimpleGraph.Coloring`,
  `SimpleGraph.Clique`, `Fintype`, finite intervals. Only the **Ramsey dimension** itself
  is missing (see novelty pre-screen below).
- Certification path: enumerate witness colourings for the lower bound and a
  proof-by-computation / `decide` upper bound. `R(3,3)=6` is small enough for a clean
  hand Lean proof; `R(3,4)`/`R(4,4)` can lean on a finite certificate.
- Developer-friendly: works under the slow model (small finite types).

## References

- Ramsey, "On a problem of formal logic" (1930).
- Greenwood & Gleason, "Combinatorial relations and chromatic graphs", Can. J. Math. 7 (1955) —
  `R(3,4)=9`, `R(4,4)=18`, `R(3,5)=14`.
- OEIS A212954 (diagonal small Ramsey numbers `R(n,n)`: 6, 18 = entries are `R(3,3)`, `R(4,4)`).
- Standard elementary proof of `R(3,3)=6`: pigeonhole on vertex degree in `K_6`.

## Novelty pre-screen (OPE-28)

- **Mathlib grep (local pin v4.10.0):** no `ramsey` / `ramseyNumber` theorem or file
  anywhere in `Mathlib` (only incidental author name "Ramsey" in ring-theory headers and
  a mention in `Combinatorics/HalesJewett.lean`/`Hindman.lean` prose). Confirmed gap.
- **Status:** `expected: known-classical` → frame as **`formalize-only`**. Do **not**
  re-fund as novel research; the value is a genuine Mathlib contribution (a Ramsey API
  plus certified small values), not a new theorem.