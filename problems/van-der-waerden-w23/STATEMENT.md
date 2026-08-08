# Van der Waerden number W(2,3) = 9 (formalize-only)

**id:** `van-der-waerden-w23`

## Informal statement

The **Van der Waerden number** `W(2,3)` is the least `n` such that every
2-colouring of `{1, …, n}` contains a monochromatic 3-term arithmetic
progression.  Its classical value is `W(2,3) = 9`:

- **Upper bound `W(2,3) ≤ 9`:** every 2-colouring of `{1,…,9}` has a
  monochromatic 3-AP.
- **Lower bound `W(2,3) > 8`:** there is a 2-colouring of `{1,…,8}` (e.g.
  `1 1 0 0 1 1 0 0`) with no monochromatic 3-AP.

A 3-term AP is a triple `(a, a+d, a+2d)` with `d ≥ 1`.  Being a property
monotone in `n`, the upper bound at `9` plus failure at `8` pins `9` as the
least such `n`.

## Main results (Lean, zero `sorry`)

- `vdw_le_9 : ∀ f : Fin 9 → Bool, HasMono3 f`
- `vdw_gt_8 : ¬ HasMono3 witness8`
- Proof file: `proofs/lean-project/ProofLab/VanDerWaerden.lean`, verified
  `lake env lean` exit 0.

## Conventions

Colourings are encoded as `f : Fin n → Bool` (position `i` ↔ colour of integer
`i+1`).  A monochromatic 3-AP exists when some `a` and `d > 0` have
`a + 2d < n` with all three positions equal under `f`.

## Novelty pre-screen

Finitary Van der Waerden is an explicit Mathlib TODO
(`Combinatorics/HalesJewett.lean` L50-53); `W(2,3)=9` is classical and fully
decidable.  Framed **formalize-only**, no novelty claim.
