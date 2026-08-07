# Van der Waerden — finite instance W(2,3) = 9

## Informal Statement

**Van der Waerden's theorem (finite form)**: For positive integers `r, k` there is a least
number `W(r, k)` such that every `r`-coloring of `{1, ..., W(r,k)}` contains a monochromatic
`k`-term arithmetic progression.

**Bounded formalize-only target**: prove the exact classical value `W(2,3) = 9`.

- Lower bound: `8` admits a 2-coloring of `{1..8}` with no monochromatic 3-AP.
- Upper bound: every 2-coloring of `{1..9}` contains a monochromatic 3-AP.

This is a **known-classical → formalize-only** bet (no novelty claim). The general/infinitary
theorem is already proved in Mathlib (`Combinatorics/HalesJewett.lean`, which deduces Van der
Waerden's theorem). The **finitary** version — including the exact `W(2,3)=9` value — is an
explicit Mathlib TODO.

## Formalization Target

```lean
-- Monochromatic 3-term AP in any 2-coloring of {1..9}
theorem W23_eq_9 :
    -- every coloring Fin 9 → Bool has x,y,z with z = 2*y - x, color equal
    ...
-- plus a witness that 8 fails (a 2-coloring with no monochromatic 3-AP)
```

Prefer a decidable finite search: enumerate the finitely many 2-colorings of `Fin 8` to show
the lower bound, and prove no 2-coloring of `Fin 9` avoids a monochromatic 3-AP (via `decide`
or a short finite case argument).

## Motivation

1. Explicit TODO in Mathlib (`Combinatorics/HalesJewett.lean`): *"Prove a finitary version of
   Van der Waerden's theorem"*.
2. Bounded, fully decidable — ideal for a slow model; no unbounded search, no novel math.
3. Exercises `Fin`/`Finset`/`Color`/AP reasoning; reusable for larger `W(r,k)`.

## Known Results

- Infinitary Van der Waerden + multidimensional generalisation in Mathlib
  (`Combinatorics/HalesJewett.lean`, `exists_mono_homothetic_copy`).
- Classical exact value `W(2,3) = 9`; `8` is a tight failure witness
  (e.g. color `1,4,6,8` one color and the rest the other).

## Attack Strategy

1. Define 2-coloring as `Fin n → Bool`; define "monochromatic 3-AP" predicate.
2. Lower bound `W(2,3) > 8`: give/verify a closed-form 2-coloring of `Fin 8` and
   `decide`-refute every 3-AP.
3. Upper bound `W(2,3) ≤ 9`: prove every 2-coloring of `Fin 9` has a mono 3-AP
   (finite case analysis / `fin_cases` + `decide`).
4. Conclude `W(2,3) = 9`.

## Sources

- Mathlib `Combinatorics/HalesJewett.lean` (TODO note, lines ~50-53)
- OEIS A005346 / classic Ramsey theory references for `W(2,3)=9`
- Van der Waerden, *Beweis einer Baudetschen Vermutung* (1927)

## Risks

- `decide` on large finite questionnaires may be slow; keep to `Fin 8`/`Fin 9` where the
  proof size stays small.
- Value is classical — mark `expected: formalize-only`; do **not** re-fund as novel.
