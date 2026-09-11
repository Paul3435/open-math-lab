# Hardy–Ramanujan taxicab 1729 = 1³+12³ = 9³+10³ (formalize-only)

**id:** `taxicab-1729`
**ticket:** OPE-1390 Scout RECOMMENDED PRIME (parent OPE-1389;
post zsqrt5-not-ufd #165 + d8-ne-q8 #166)
**expected:** known-classical (Hardy–Ramanujan / taxicab:
1729 is a sum of two positive cubes in two ways) —
**no novelty claim**

## Why not classical / why formalize-only

Settled elementary arithmetic: `1³ + 12³ = 9³ + 10³ = 1729`,
and these are two essentially different unordered pairs of
positive cubes. Completely classical (Hardy–Ramanujan number;
Ta(2) = 1729). The namesake “1729 is the *smallest* such
positive integer” is a **different**, larger residual — do
**not** sorry it.

Not an open problem. Not a novelty claim. Not live cash.

**Not** Fermat Last Theorem n=3 (`fermatLastTheoremThree`
FLT/Three.lean L725 already-in: `a³+b³ ≠ c³` for positive
`a,b,c` — **different** equation; USE `Nat` / `^ 3`, do
**not** re-prove FLT, do **not** cite as taxicab). **Not**
two-square (`Nat.Prime.sq_add_sq` already-in; squares ≠
cubes). **Not** four-square / three-square (already-in /
consumed #159). **Not** cannonball square-pyramid (consumed
#154; pyramidal squares ≠ two-cube sums). **Not** cubing a
cube (Archive Wiedijk #82 `cannot_cube_a_cube`; do **not**
import `Archive.*`). **Not** Euler partition / Eulerian
trails / Euclid–Euler perfect (consumed Euler *namesakes*,
different theorems). **Not** zsqrt5-not-ufd (consumed #165).
**Not** d8-ne-q8 (consumed #166). **Not** allowing negative
cubes (`3³+4³ = 6³+(-5)³ = 91` is a **different** residual;
positive cubes only).

Mathlib v4.10.0 already has the **Nat power infra this
theorem needs**:

- `Nat` / `HPow` / `^`
- `pow_two` (Algebra/Group/Defs.lean L581)
- `pow_three` (Algebra/Group/Defs.lean L590)
- `fermatLastTheoremThree` (FLT/Three.lean L725) — **different**
  already-in theorem; **not** namesake

There is **no** named `taxicab` / `Taxicab` / `hardyRamanujan`
/ `1729` two-cubes theorem anywhere under `Mathlib/` or
`Archive/` or `ProofLab/` (this run → ZERO on those names;
FLT n=3 is a different equation). Do **not** import
`Archive.*`.

OPE-1374 shortlist is **CONSUMED** (#165+#166). This is a
**fresh** catalog-audit prime, **not** a zsqrt5 leftover
continuation, **not** a d8 leftover, **not** an FLT leftover,
**not** a cannonball leftover, **not** a prize leftover,
**not** a Formalist Level B revival, **not** a third slot.

Mill NOW: finite two-cube witnesses on Mathlib `Nat` / `^ 3`.
`pow_three` is waiting the same way `Zsqrtd.norm` waited for
ℤ[√-5]. **Not a rubber-stamp of FLT n=3.** **Not a
rubber-stamp of two-square.**

Do **not** describe an attack as discovering 1729. Do **not**
expand into “smallest such n” as a sorry (that is
leftover-risk of *this* id — do **not** sorry it). Do **not**
label theorems `fermat_*` / `flt_*` / `sq_add_sq_*` as the
namesake.

## Pinned convention (exact)

**v1 Level A is named small-cube witnesses:
`1³+12³ = 1729 = 9³+10³` in `ℕ`, not labelled Hardy /
Ramanujan / taxicab.**

Suggested pin:

```text
-- Level A (not labelled Hardy / Ramanujan / taxicab):
-- named two-cube witnesses.

theorem cubes_one_twelve :
    (1 : ℕ) ^ 3 + 12 ^ 3 = 1729

theorem cubes_nine_ten :
    (9 : ℕ) ^ 3 + 10 ^ 3 = 1729

theorem taxicab_two_ways :
    (1 : ℕ) ^ 3 + 12 ^ 3 = 9 ^ 3 + 10 ^ 3

-- optional extra: the pairs are distinct as unordered pairs
-- ({1,12} ≠ {9,10})

-- Level B namesake (smallest such n; residual OK)
theorem taxicab_1729 {n a b c d : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hpair : ({a, b} : Set ℕ) ≠ {c, d})
    (h : a ^ 3 + b ^ 3 = n ∧ c ^ 3 + d ^ 3 = n) :
    1729 ≤ n
    -- do not sorry the namesake
```

Named two-cube witnesses are load-bearing. Both pairs sum
to 1729, and they are different unordered pairs, so the
theorem is **not** “some Nats have cubes.”

**Level A may land only** the 1³+12³ / 9³+10³ / equality
(optional extra: unordered pairs distinct), **not** labelled
Hardy / Ramanujan / taxicab. Reuse Mathlib `Nat` / `^ 3` —
**do not re-prove** FLT n=3 / two-square / three-square.

**Level B** is the namesake “1729 is smallest.” Do not sorry
the namesake; honest partial is allowed (comment residual,
not `sorry`). Second taxicab 4104 / signed cubes extras are
residual.

## Landmines

1. **Do not re-prove** `Nat` / `pow_two` / `pow_three`.
   Already Mathlib/core. Use them.
2. **This is not** `fermatLastTheoremThree` (FLT/Three.lean
   L725 already-in). Different equation. USE `^ 3`.
3. **This is not** `Nat.Prime.sq_add_sq` / four-square /
   three-square (already-in / consumed #159).
4. **This is not** cannonball (consumed #154). Pyramidal
   squares ≠ two cubes.
5. **This is not** “smallest n” uniqueness. Residual of
   this id. Do not sorry it.
6. **This is not** signed cubes / 91 / 4104. Residual.
7. **This is not** zsqrt5-not-ufd / d8-ne-q8 (consumed
   #165+#166). Do not prove non-UFD / D8 ≇ Q8 here.
8. **This is not** `euler-brick` (leftover of this shortlist).
   Do not prove the 44,117,240 brick here.
9. **Do not** re-prime the consumed mill list.
10. **Leave OPE-403 alone.** Leave OPE-1195 leftover status
    alone.
11. **Do not import `Archive.*`.**
12. Default no claim. No novelty claim.

## Out of v1

- Namesake “1729 is the smallest taxicab number”
- Second taxicab 4104 / Ta(2,k) for k>2
- Signed cubes / every integer as three cubes
- Euler’s sum-of-powers conjecture / Lander–Parkin fifth powers
- Prize claims / Millennium / Beal
