# Attack log — van-der-waerden-w23

| when | agent | strategy | result |
|------|-------|----------|--------|
| 2026-08-08 | Attack Lead | Formalize-only via `native_decide`: encode 2-colourings of `Fin n` as `f : Fin n → Bool`, monochromatic-3-AP predicate `HasMono3` (positions a, a+d, a+2d, d>0), certified exhaustive decision | **W(2,3)=9 landed, Lean ZERO-sorry** (`ProofLab/VanDerWaerden.lean`): `vdw_le_9` = every 2-colouring of `Fin 9` has a mono 3-AP (2^9 colourings, `native_decide`); `vdw_gt_8` = witness `11001100` on `Fin 8` has none (tightness). `lake env lean ProofLab/VanDerWaerden.lean` exit 0. |

## Status

- **Done, zero `sorry`, `lake env lean` green:** W(2,3) = 9 via the two bounds.
- Definitions: `colorAt` (decidable colour lookup), `HasMono3` (mono 3-term AP),
  `witness8` (tightness witness). Explicit `Decidable` instance for `HasMono3`
  (required so `native_decide` can enumerate the `∀ f : Fin n → Bool`).

## Residual / notes

- Statement is `formalize-only`, no novelty claim (classical; Mathlib TODO at
  `Combinatorics/HalesJewett.lean`).
- Not wired into Mathlib's `HalesJewett` (infinitary VdW) — left as a
  self-contained `ProofLab` result; a Mathlib PR would lift `W(2,3)=9` as a
  finitary corollary (follow-up, out of scope here).
