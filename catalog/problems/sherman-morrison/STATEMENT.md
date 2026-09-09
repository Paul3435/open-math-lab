# Sherman–Morrison rank-one inverse update — formalize-only

**id:** `sherman-morrison`
**ticket:** OPE-1248 Scout RECOMMENDED PRIME (Director approves after this shortlist)
**expected:** known-classical (Sherman–Morrison 1950:
`(A + uvᵀ)⁻¹ = A⁻¹ − (A⁻¹u vᵀ A⁻¹)/(1 + vᵀ A⁻¹ u)`)
— **no novelty claim**

## Why not classical / why formalize-only

Settled linear algebra: if `A` is invertible and the
scalar `1 + vᵀ A⁻¹ u` is invertible, then the rank-one
update `A + uvᵀ` is invertible with the displayed
inverse. Completely classical (Sherman–Morrison 1950;
Woodbury 1950 is the block residual).

Not an open problem. Not a novelty claim.

**Not** the matrix-determinant / Weinstein–Aronszajn
identity `det(1 + AB) = det(1 + BA)` (already
`det_one_add_mul_comm`, SchurComplement.lean L395 —
**different theorem**; USE as glue if needed; do
**not** re-prove; do **not** cite as Sherman–Morrison).
**Not** Schur complement (already-in). **Not** SVD /
polar / Moore–Penrose (schur-product #129 residual).
**Not** Kirchhoff / DFT / pfaffian (circulant-det /
Cauchy–Binet leftover). **Not** Woodbury (block
residual of *this* id; do **not** sorry Woodbury).

Mathlib v4.10.0 already has the **inverse / rank-one
outer-product infra this theorem needs**:

- `Matrix.inv` / `A⁻¹` (`NonsingularInverse.lean` L191)
- `inv_def` L194 / `mul_nonsing_inv` L233 /
  `nonsing_inv_mul` L239
- `Matrix.vecMulVec` (`Data/Matrix/Basic.lean` L1453) /
  `vecMulVec_apply` L1457
- `Matrix.mulVec` (Basic.lean L1472)
- `Matrix.dotProduct` / `⬝ᵥ` (Basic.lean L662)
- `det_isEmpty` (Determinant/Basic.lean L85) /
  `det_fin_zero` L736 / `det_fin_one` L740 /
  `det_fin_two` L747
- `det_one_add_mul_comm` (SchurComplement.lean L395)
  — **not** namesake

There is **no** named Sherman–Morrison / Woodbury
formula, **no** `shermanMorrison` / `sherman_morrison`
/ `woodbury` / `rankOneUpdate` anywhere under
`Mathlib/` or `Archive/` or `ProofLab/`
(this run → ZERO on those names).
NonsingularInverse.lean ends with inverse/adjugate
algebra, **no** rank-one update. Do **not** import
`Archive.*`.

OPE-1233 shortlist is **CONSUMED**
(#138 kraft-inequality Level A + #139
sabidussi-boxprod Level A). This is a **fresh**
catalog-audit id, **not** a Kraft leftover
continuation, **not** a Sabidussi leftover,
**not** a Schur-product / SVD revival, **not** a
circulant-det leftover, **not** a prize leftover,
**not** a Formalist Level B revival, **not** a
third slot.

Mill NOW: finite rank-one inverse update after
Kraft (prefix-free codes) + Sabidussi (box-product
colouring). `Matrix.inv` + `vecMulVec` are waiting
the same way `Matrix.circulant` waited for the
circulant determinant. **Not a rubber-stamp of
Schur complement.** **Not a rubber-stamp of
Moore–Penrose.**

Do **not** describe an attack as discovering
Sherman–Morrison. Do **not** expand into Woodbury /
SVD / polar / Moore–Penrose as extra namesakes
(Woodbury is leftover-risk of *this* id;
SVD/polar/MP are leftover of consumed schur-product).

## Pinned convention (exact)

**v1 Level A is the inverse of a rank-one update on
named finite matrices over `ℚ`: empty `Fin 0`,
`Fin 1` scalar, and `Fin 2` identity-plus-`e₀e₀ᵀ`,
not labelled Sherman / Woodbury.** Invertibility
(`IsUnit det` / `≠ 0`) is load-bearing.

Suggested pin:

```text
-- Level A (not labelled Sherman / Woodbury):
-- empty Fin 0; Fin 1 scalar; Fin 2 I + e0 e0ᵀ.
-- Not labelled Sherman.

theorem inv_add_vecMulVec_fin_zero
    (u v : Fin 0 → ℚ) :
    ((1 : Matrix (Fin 0) (Fin 0) ℚ) + vecMulVec u v)⁻¹
      = (1 : Matrix (Fin 0) (Fin 0) ℚ)

theorem inv_add_vecMulVec_fin_one
    (a u v : ℚ) (ha : a ≠ 0) (h : a + u * v ≠ 0) :
    (!![a] + vecMulVec ![u] ![v])⁻¹
      = !![1 / (a + u * v)]

def e0 : Fin 2 → ℚ := ![1, 0]

theorem inv_one_add_vecMulVec_e0_fin_two :
    ((1 : Matrix (Fin 2) (Fin 2) ℚ) + vecMulVec e0 e0)⁻¹
      = !![1/2, 0; 0, 1]

-- Level B namesake (all finite rank-one updates; residual OK)
theorem sherman_morrison
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℚ) (u v : n → ℚ)
    (hA : IsUnit A.det)
    (h : IsUnit (1 + v ⬝ᵥ A⁻¹.mulVec u)) :
    (A + vecMulVec u v)⁻¹
      = A⁻¹ - (1 / (1 + v ⬝ᵥ A⁻¹.mulVec u))
          • vecMulVec (A⁻¹.mulVec u) (A⁻¹.vecMul v)
```

Finite `Fin 0` / `Fin 1` / `Fin 2` is load-bearing.
`vecMulVec` rank-one is load-bearing. Inverse over
`ℚ` is load-bearing.

**Level A may land only** empty / Fin 1 scalar /
`I + e₀e₀ᵀ` on Fin 2 (optional extra: Fin 1 written
in Sherman form with `a⁻¹` and the scalar
denominator), **not** labelled Sherman.
Reuse Mathlib `Matrix.inv` / `vecMulVec` /
`mul_nonsing_inv` / `det_fin_one` —
**do not re-prove** inverse or outer product.

**Level B** is the namesake: every finite invertible
rank-one update with invertible scalar denominator
has the Sherman–Morrison inverse. Do not sorry the
namesake; honest partial is allowed (comment
residual, not `sorry`). Woodbury is residual.

## Landmines

1. **Do not re-prove** `Matrix.inv` / `vecMulVec` /
   `mulVec` / `dotProduct` / `mul_nonsing_inv` /
   `det_fin_*` / `det_one_add_mul_comm`.
   Already Mathlib. Use them.
2. **This is not** Weinstein–Aronszajn /
   `det_one_add_mul_comm` (already-in). Different
   theorem (det vs inverse). Do not cite as
   Sherman–Morrison.
3. **This is not** Woodbury. Residual of this id.
   Do not sorry Woodbury. Do not take Woodbury as
   namesake.
4. **This is not** SVD / polar / Moore–Penrose
   (schur-product #129 residual).
5. **This is not** Kirchhoff / DFT / pfaffian
   (circulant-det #132 / Cauchy–Binet leftover).
6. **This is not** `kraft-inequality` (#138) /
   McMillan / Huffman / Shannon.
7. **This is not** `sabidussi-boxprod` (#139) /
   Hedetniemi / Brooks / Vizing domination.
8. **Do not** re-prime the consumed mill list.
9. **Leave OPE-403 alone.** Leave OPE-1195
   leftover status alone.
10. **Do not import `Archive.*`.**
11. Default no claim. No novelty claim.

## Out of v1

- Woodbury matrix identity (block rank-k)
- SVD / polar / Moore–Penrose (schur-product leftover)
- Kirchhoff matrix-tree / DFT / pfaffian
- Prize claims / Millennium / Beal
