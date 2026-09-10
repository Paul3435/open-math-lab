# Legendre three-square theorem (named small-n witnesses, formalize-only)

**id:** `legendre-three-squares`
**ticket:** OPE-1342 Scout RECOMMENDED PRIME (parent OPE-1341;
post jordan-canonical-form #156 + orthogonal-latin-squares #157)
**expected:** known-classical (Adrien-Marie Legendre 1797/98:
a natural number is a sum of three integer squares iff it is
not of the form `4^a (8b + 7)`) —
**no novelty claim**

## Why not classical / why formalize-only

Settled elementary number theory: `n = x² + y² + z²` for
`x, y, z ∈ ℤ` (equivalently `ℕ`, zeros allowed) if and only if
the 4-adic valuation does not leave a factor `≡ 7 (mod 8)`.
Completely classical (Legendre; Gauss later via class numbers).
The namesake “every n not of that form” is a **different**,
larger residual — do **not** sorry it.

Not an open problem. Not a novelty claim. Not live cash.

**Not** Lagrange four-square (`Nat.sum_four_squares`,
SumFourSquares.lean L212 already-in: four squares, **every** n —
**different** theorem; USE as glue if needed, do **not** re-prove,
do **not** cite as three-square). **Not** Fermat two-square
(`Nat.Prime.sq_add_sq`, SumTwoSquares.lean L31 already-in;
primes `≢ 3 (mod 4)` — **different** theorem). **Not**
cannonball square-pyramid (consumed #154; pyramidal number
being square ≠ three squares; do **not** revive Lucas uniqueness
/ Watson / `sum_range_pow` / `Nat.sum_four_squares` as namesake).
**Not** Alcuin integer triangles (consumed #153). **Not**
Jordan canonical form (consumed #156). **Not** orthogonal Latin
squares (consumed #157). **Not** Gauss Eureka / three triangular
numbers (equivalent after `8T+1 = odd square`; residual of
*this* id — do **not** sorry Eureka).

Mathlib v4.10.0 already has the **square / four-square infra
this theorem needs**:

- `Nat` / `^ 2` / `IsSquare` (Algebra/Group/Even.lean L46)
- `Nat.sum_four_squares` (SumFourSquares.lean L212) —
  **not** namesake
- `Nat.Prime.sq_add_sq` (SumTwoSquares.lean L31) —
  **not** namesake
- `Nat.sqrt` / decidable inequality on small `ℕ`

There is **no** named three-square / Legendre-three-square
theorem, **no** `three_square` / `threeSquare` / `ThreeSquare` /
`sum_three_squares` / `sumThreeSquares` / `isSumOfThreeSquares` /
`LegendreThree` / `legendre_three` anywhere under `Mathlib/` or
`Archive/` or `ProofLab/` (this run → ZERO on those names). Do
**not** import `Archive.*`.

OPE-1326 shortlist is **CONSUMED** (#156 jordan-canonical-form
Level A + #157 orthogonal-latin-squares Level A). This is a
**fresh** catalog-audit id, **not** a Jordan leftover
continuation, **not** an OLS leftover, **not** a cannonball
leftover, **not** a four-square leftover, **not** a prize
leftover, **not** a Formalist Level B revival, **not** a
third slot.

Mill NOW: finite three-square witnesses after 2×2 Jordan blocks
+ order-2/3 Latin orthogonality. `Nat` squares are waiting the
same way `Matrix` waited for Jordan. **Not a rubber-stamp of
four-square.** **Not a rubber-stamp of two-square.**

Do **not** describe an attack as discovering Legendre's theorem.
Do **not** expand into “every n not of the form `4^a(8b+7)`”
as a sorry (that is leftover-risk of *this* id — do **not**
sorry it). Do **not** label theorems `legendre_*` (Legendre
symbol / `euler_criterion` already-in name collision).

## Pinned convention (exact)

**v1 Level A is named small-n three-square witnesses:
`1 = 1²+0²+0²`, `2 = 1²+1²+0²`, `3 = 1²+1²+1²`, and `7` is
not a sum of three squares, not labelled Legendre.** Nonneg
integer squares (zeros allowed) are load-bearing.

Suggested pin:

```text
-- Level A (not labelled Legendre):
-- named small-n witnesses.

def IsSumThreeSquares (n : ℕ) : Prop :=
  ∃ a b c : ℕ, a ^ 2 + b ^ 2 + c ^ 2 = n

theorem three_squares_one :
    IsSumThreeSquares 1
    -- 1 = 1² + 0² + 0²

theorem three_squares_two :
    IsSumThreeSquares 2
    -- 1² + 1² + 0²

theorem three_squares_three :
    IsSumThreeSquares 3
    -- 1² + 1² + 1²

theorem three_squares_seven_not :
    ¬ IsSumThreeSquares 7
    -- 7 = 4^0 * (8*0 + 7)

-- optional extra: 6 = 2²+1²+1² / 15 not a sum of three squares

-- Level B namesake (every n not of form 4^a(8b+7); residual OK)
theorem legendre_three_squares :
    ∀ n : ℕ, IsSumThreeSquares n ↔
      ¬ ∃ a b : ℕ, n = 4 ^ a * (8 * b + 7)
    -- do not sorry the namesake
```

Named small-n witnesses are load-bearing.
`¬ IsSumThreeSquares 7` is load-bearing (so the theorem is
**not** “some numbers are three squares”).

**Level A may land only** the small witnesses / the `7` obstruction
(optional extra: `6` yes / `15` no), **not** labelled Legendre.
Reuse Mathlib `Nat` / squares — **do not re-prove** four-square /
two-square.

**Level B** is the namesake characterization. Do not sorry the
namesake; honest partial is allowed (comment residual, not
`sorry`). Gauss Eureka / class-number extras are residual.

## Landmines

1. **Do not re-prove** `Nat.sum_four_squares` / `Nat.Prime.sq_add_sq`
   / `IsSquare`. Already Mathlib. Use them if needed.
2. **This is not** four-square. Four squares always; three squares
   miss `4^a(8b+7)`. Do not cite as three-square.
3. **This is not** two-square / Fermat Christmas theorem.
4. **This is not** cannonball / pyramidal-square / Lucas uniqueness
   / Watson (consumed #154).
5. **This is not** Gauss Eureka (three triangular numbers;
   residual of this id). Do not sorry Eureka.
6. **This is not** `orthogonal-latin-squares` / `jordan-canonical-form`
   (consumed #157+#156).
7. **Do not** label theorems `legendre_*` (Legendre symbol collision
   with already-in `euler_criterion`).
8. **Do not** re-prime the consumed mill list.
9. **Leave OPE-403 alone.** Leave OPE-1195 leftover status
   alone.
10. **Do not import `Archive.*`.**
11. Default no claim. No novelty claim.

## Out of v1

- Legendre namesake (every n not of form `4^a(8b+7)`)
- Gauss Eureka / three triangular numbers
- Class-number / genus theory extras
- Prize claims / Millennium / Beal
