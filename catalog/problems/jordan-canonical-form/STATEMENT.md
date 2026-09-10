# Jordan canonical form (named 2×2 blocks, formalize-only)

**id:** `jordan-canonical-form`
**ticket:** OPE-1326 Scout RECOMMENDED PRIME (parent OPE-1325;
post alcuin-integer-triangles #153 + cannonball-square-pyramid #154)
**expected:** known-classical (Camille Jordan 1870: over an
algebraically closed field every square matrix is similar to a
block-diagonal matrix of Jordan blocks) —
**no novelty claim**

## Why not classical / why formalize-only

Settled linear algebra: a Jordan block `J_k(λ)` is the `k×k`
upper-triangular matrix with `λ` on the diagonal and `1` on the
superdiagonal; the namesake says every endomorphism of a finite-
dimensional vector space over an algebraically closed field is
similar to a direct sum of such blocks. Completely classical
(Jordan 1870). Mathlib `docs/undergrad.yaml` still points the
Jordan-normal-form line at Wikipedia — a pin-local gap, not a
discovery.

Not an open problem. Not a novelty claim.

**Not** Jordan–Chevalley–Dunford (`exists_isNilpotent_isSemisimple`,
JordanChevalley.lean L71 already-in: semisimple + nilpotent
polynomial split — **different** theorem; USE as glue if needed, do
**not** re-prove, do **not** cite as Jordan form). **Not** Jordan
algebras (`IsJordan`, Algebra/Jordan/Basic.lean L78 already-in;
nonassociative identity `x²y = x(xy)` ≠ matrix blocks). **Not**
Jordan–Hölder (`jordan_holder` already-in composition series).
**Not** Cayley–Hamilton (`Matrix.aeval_self_charpoly`,
Charpoly/Basic.lean L123 already-in; minpoly divides charpoly —
**USE**, do **not** cite as Jordan form). **Not** Sherman–Morrison
(consumed #141; rank-one inverse ≠ Jordan blocks). **Not**
Cauchy–Binet / circulant-det / Hadamard / Schur-product (consumed
det/matrix mills; det identities ≠ similarity classification).
**Not** Alcuin integer triangles (consumed #153). **Not**
cannonball square-pyramid (consumed #154). **Not** orthogonal
Latin squares (leftover of this shortlist).

Mathlib v4.10.0 already has the **matrix / charpoly infra this
theorem needs**:

- `Matrix` / `Matrix.mul` / `!![…]` notation
- `Matrix.aeval_self_charpoly` (Charpoly/Basic.lean L123) —
  **not** namesake
- `exists_isNilpotent_isSemisimple` (JordanChevalley.lean L71) —
  **different** Dunford split; do **not** re-prove
- `Module.End.genEigenspace` — generalized-eigenspace glue,
  **not** namesake
- `det_fin_two` — 2×2 determinant glue, **not** namesake

There is **no** named Jordan-canonical-form / Jordan-block
theorem, **no** `jordanCanonical` / `JordanForm` / `jordan_form` /
`IsJordanBlock` / `JordanBlock` anywhere under `Mathlib/` or
`Archive/` or `ProofLab/` (this run → ZERO on those names; Jordan
algebra `IsJordan` and Jordan–Chevalley Dunford hits only). Do
**not** import `Archive.*`.

OPE-1310 shortlist is **CONSUMED** (#153 alcuin-integer-triangles
Level A + #154 cannonball-square-pyramid Level A). This is a
**fresh** catalog-audit id, **not** an Alcuin leftover
continuation, **not** a cannonball leftover, **not** a
Sherman–Morrison leftover, **not** a Jordan–Chevalley leftover,
**not** a prize leftover, **not** a Formalist Level B revival,
**not** a third slot.

Mill NOW: finite 2×2 Jordan-block witnesses after integer-triangle
counts + pyramidal squares. `Matrix` / `charpoly` are waiting the
same way `Nat` waited for Alcuin. **Not a rubber-stamp of
Cayley–Hamilton.** **Not a rubber-stamp of Jordan–Chevalley.**

Do **not** describe an attack as discovering Jordan form.
Do **not** expand into the namesake “every matrix over an
algebraically closed field is similar to a Jordan form” as a
sorry (that is leftover-risk of *this* id — do **not** sorry it).
Do **not** label theorems `jordan_*` (Jordan-algebra / Dunford
name collision).

## Pinned convention (exact)

**v1 Level A is the nilpotent 2×2 Jordan block and a diagonal
2×2: `J = !![0, 1; 0, 0]` satisfies `J * J = 0` and `J ≠ 0`, and
`D = !![1, 0; 0, 2]` is diagonal, not labelled Jordan.** Matrix
multiplication on `Fin 2` is load-bearing.

Suggested pin:

```text
-- Level A (not labelled Jordan):
-- named 2×2 blocks.

def jordanNilpotentFinTwo : Matrix (Fin 2) (Fin 2) ℤ :=
  !![0, 1; 0, 0]

theorem jordanNilpotentFinTwo_sq :
    jordanNilpotentFinTwo * jordanNilpotentFinTwo = 0

theorem jordanNilpotentFinTwo_ne_zero :
    jordanNilpotentFinTwo ≠ 0

def jordanDiagonalFinTwo : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1, 0; 0, 2]

theorem jordanDiagonalFinTwo_isDiagonal :
    Matrix.diagonal (fun i : Fin 2 => if i = 0 then 1 else 2)
      = jordanDiagonalFinTwo
    -- pin: D is diagonal (1×1 blocks). Encoding, not labelled Jordan.

-- optional extra: J₁(1) = !![1, 1; 0, 1] has (J-I)^2 = 0

-- Level B namesake (every matrix similar to a Jordan form; residual OK)
theorem jordan_canonical_form :
    ∀ M : Matrix (Fin n) (Fin n) ℂ, ∃ P, IsUnit P ∧
      P⁻¹ * M * P = ⋃ Jordan blocks
    -- do not sorry the namesake
```

Named 2×2 blocks are load-bearing.
`J * J = 0` and `J ≠ 0` are load-bearing (so the zero matrix is
**not** the Level A nilpotent witness).

**Level A may land only** the nilpotent `Fin 2` block / diagonal
`Fin 2` (optional extra: one nontrivial eigenvalue-1 block),
**not** labelled Jordan. Reuse Mathlib `Matrix` / charpoly —
**do not re-prove** Cayley–Hamilton / Dunford / Jordan algebras.

**Level B** is the namesake similarity classification over an
algebraically closed field. Do not sorry the namesake; honest
partial is allowed (comment residual, not `sorry`). Rational
canonical form / primary decomposition extras are residual.

## Landmines

1. **Do not re-prove** `Matrix.mul` / `aeval_self_charpoly` /
   `exists_isNilpotent_isSemisimple` / `IsJordan`.
   Already Mathlib. Use them if needed.
2. **This is not** Jordan–Chevalley–Dunford. Semisimple+nilpotent
   split ≠ block classification. Do not cite as Jordan form.
3. **This is not** Jordan algebras (`IsJordan`). Do not label
   theorems `jordan_*`.
4. **This is not** Jordan–Hölder / Jordan totient / Jordan curve.
5. **This is not** Cayley–Hamilton (already-in glue).
6. **This is not** Sherman–Morrison / Cauchy–Binet / circulant /
   Hadamard / Schur-product (consumed matrix mills).
7. **This is not** `orthogonal-latin-squares` (OPE-1326 leftover).
   Do not prove Latin squares here.
8. **This is not** alcuin-integer-triangles / cannonball-square-pyramid
   (consumed #153+#154) / Frucht / Proth.
9. **Do not** re-prime the consumed mill list.
10. **Leave OPE-403 alone.** Leave OPE-1195 leftover status
    alone.
11. **Do not import `Archive.*`.**
12. Default no claim. No novelty claim.

## Out of v1

- Jordan namesake (every matrix similar to a Jordan form)
- Rational canonical form / primary rational canonical form
- Uniqueness of Jordan blocks
- Prize claims / Millennium / Beal
