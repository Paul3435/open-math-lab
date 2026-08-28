# Weak Schur number WS(2) = 8 (formalize-only)

**id:** `weak-schur-ws2`  
**issue:** OPE-462 (Scout OPE-458 #2; Director OPE-460 secondary)  
**expected:** known-classical · **frame:** formalize-only · **novelty claim:** none

## Informal statement (pinned)

The **weak Schur number** `WS(k)` is the largest positive integer `n` such that
the interval `{1, …, n}` admits a `k`-colouring with **no monochromatic weakly
sum-free violation**: there do **not** exist **distinct** `x, y ∈ {1,…,n}`
with `z = x + y ≤ n` and `c(x) = c(y) = c(z)`.

Equivalently, `WS(k) + 1` is the least `N` such that every `k`-colouring of
`{1, …, N}` contains a monochromatic solution to `x + y = z` with `x ≠ y`.

Classical value: **`WS(2) = 8`**.

### Distinctness pin (non-negotiable)

- THE distinctness requirement is **`x ≠ y`**.
- Because `x, y ≥ 1`, the sum `z = x + y` automatically differs from both
  summands, so the triple is pairwise distinct once `x ≠ y`.
- Literature sometimes phrases "pairwise distinct `x,y,z`"; that is equivalent
  under this pin.  Do **not** require any other distinctness side-condition.

### Domain / encoding pin (offset landmine)

- Domain is the integer interval **`{1, …, n}`**, not `{0, …, n-1}` as the
  equation domain.
- Lean encoding: `f : Fin n → Fin k` where position `i : Fin n` carries the
  colour of the integer **`i.val + 1`**.
- Sum in Fin-coordinates: integers `X = x.val+1`, `Y = y.val+1` give
  `Z = X+Y` at Fin-index `x.val + y.val + 1`, with guard
  `x.val + y.val + 1 < n` enforcing `z ≤ n`.

### Scope boundary (do not conflate)

- **Not** classical strong Schur `S(k)` (where `x = y` is allowed; `S(2) = 4`).
- **Not** the closed `schur-partition` partition-identity scope.
- Certificates and witnesses from `ProofLab/SchurNumber.lean` do **not**
  transfer (different extremal sets and different values).

## Main results (Lean, zero `sorry`)

File: `proofs/lean-project/ProofLab/WeakSchur.lean`

| Theorem | Meaning |
|---------|---------|
| `ws2_gt_7` | `¬ HasMonoWeakSchur witnessWS2` on `Fin 8` → `WS(2) ≥ 8` |
| `ws2_le_8` | `∀ f : Fin 9 → Fin 2, HasMonoWeakSchur f` → `WS(2) ≤ 8` |
| `ws2_eq_8` | both bounds → **`WS(2) = 8`** |

### Witness (`ws2_gt_7`)

2-colouring of `{1,…,8}` with classes:

- colour 0: `{1, 2, 4, 8}`
- colour 1: `{3, 5, 6, 7}`

Fin bitstring on positions `0..7` (integers `1..8`): **`00101110`**.  
(The colour-swap `11010001` is the only other valid length-8 colouring;
exhaustive probe.)

### Upper bound (`ws2_le_8`)

Decidable enumeration over all `2^9 = 512` colourings of `Fin 9` — trivially
`native_decide` scale.  **No heuristic search.**

## References (known-classical)

- Abbott, H. L. & Wang, E. T. H., *The partition problem of weak Schur numbers*,
  Ars Combinatoria (survey definition of weak Schur / weakly sum-free colourings).
- Exoo, G. (and subsequent weak-Schur tables): classical value **`WS(2) = 8`**.
- Contrast strong Schur: Schur 1916; OEIS A030126 (`S(2)=4`, `S(3)=13`, …).

## Novelty pre-screen

- Mathlib v4.10.0 pin: no additive Schur / weak-Schur content
  (`Mathlib/Combinatorics`, `Mathlib/NumberTheory` greps clean — Scout OPE-458).
- **Status:** `expected: known-classical` → **formalize-only**.  Do **not**
  re-fund as novel research; value is a Lean-checked statement + certificates
  in the SchurNumber / VanDerWaerden witness discipline.
