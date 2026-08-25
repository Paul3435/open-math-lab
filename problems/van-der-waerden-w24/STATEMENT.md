# Van der Waerden number W(2,4) = 35 (formalize-only)

**id:** `van-der-waerden-w24`  
**Issue:** OPE-455 (bench prime from Scout OPE-430, ratified OPE-454)  
**Expected:** known-classical → formalize-only — **no novelty claim**

## Exact statement (pinned)

The **Van der Waerden number** `W(2,4)` is the least positive integer `N` such that every
2-colouring of `{1, …, N}` contains a monochromatic **4-term arithmetic progression**.

Classical value (computer-assisted upper bound): **`W(2,4) = 35`**
(Chvátal, *Some hard van der Waerden problems*, TCS 1979; also tabulated as
`W(4,2)=35` under the dual `(k,r)` convention).

Equivalent bounds that pin the exact value:

- **Lower bound `W(2,4) > 34`:** there exists a 2-colouring of `{1,…,34}` with **no**
  monochromatic 4-AP.
- **Upper bound `W(2,4) ≤ 35`:** every 2-colouring of `{1,…,35}` **has** a monochromatic 4-AP.

Monotonicity in `N` makes these two facts equivalent to `W(2,4) = 35`.

## Conventions (Lean encoding)

Aligned with closed `van-der-waerden-w23` / `ProofLab/VanDerWaerden.lean`:

| Concept | Encoding |
|--------|----------|
| Interval | `[0, n)` as positions of type `Fin n` (position `i` ↔ integer `i+1`) |
| 2-colouring | `f : Fin n → Bool` |
| Colour lookup | `colorAt f p` — decidable fallback outside range (unused once bounds hold) |
| 4-term AP | positions `a, a+d, a+2d, a+3d` with **`d > 0`** and `a + 3d < n` |
| Mono 4-AP | `HasMono4 f` — the four positions share one colour under `f` |
| Witness | closed-form `Fin 34 → Bool` (bit-mask or case table); Lean check must be **decidable and self-contained** (`native_decide` OK) |

Do **not** use residue/cyclic van der Waerden `W_c` here — the target is the classical
linear-interval number `W(2,4)`.

## Literature / honesty flags

- Infinitary Van der Waerden is already in Mathlib (`Combinatorics/HalesJewett.lean`).
- Finitary values / exact `W(r,k)` remain an explicit Mathlib TODO; this ticket is
  **formalize-only**.
- **Upper bound `W(2,4) ≤ 35` is computer-assisted in the published literature.**
  Exhaustive `native_decide` over all `2^35` colourings does **not** scale.
  Acceptable Lean strategies for the upper half: hand case-analysis transcription, or
  certificate import. **Do not** attempt brute force in Lean.
- Partial ladder (lower bound alone, or a weaker hand upper bound) is an acceptable
  close if honestly labeled in `RESULTS.md`.

## Main Lean targets

```lean
-- lower: W(2,4) > 34
theorem vdw24_gt_34 : ¬ HasMono4 (witness34 : Fin 34 → Bool)

-- upper: W(2,4) ≤ 35  (hard half; may remain open under timebox)
theorem vdw24_le_35 : ∀ f : Fin 35 → Bool, HasMono4 f
```

File: `proofs/lean-project/ProofLab/VanDerWaerden.lean` (carry-over namespace).

## Sources

- Chvátal, *Some hard van der Waerden problems*, Theoretical Computer Science (1979)
- OEIS A005346 / standard VdW tables (`W(2,4)=35`)
- Closed lab artifact: `ProofLab/VanDerWaerden.lean` (`W(2,3)=9`)
- Scout dossier: `catalog/problems/van-der-waerden-w24/DOSSIER.json` (OPE-430)
