# ℤ[√-5] is not a UFD (6=2·3=(1+√-5)(1-√-5), formalize-only)

**id:** `zsqrt5-not-ufd`
**ticket:** OPE-1374 Scout RECOMMENDED PRIME (parent OPE-1373;
post myhill-nerode #162 + gray-code #163)
**expected:** known-classical (Dedekind / standard quadratic
example: ℤ[√-5] admits two essentially different
factorizations of 6) —
**no novelty claim**

## Why not classical / why formalize-only

Settled algebraic number theory: in `ℤ√(-5)` one has
`6 = 2 * 3 = (1 + √-5)(1 - √-5)`, and these are
factorizations into irreducibles that are not associates
(norm 4 vs norm 6). Completely classical. The namesake
“`¬ UniqueFactorizationMonoid (ℤ√(-5))` for the whole
ring” is a **different**, larger residual — do **not**
sorry it.

Not an open problem. Not a novelty claim. Not live cash.

**Not** Gaussian integers Euclidean / UFD
(`GaussianInt.lean` `EuclideanDomain ℤ[i]` L243 already-in
— **different** ring `d = -1`; USE `Zsqrtd` / `norm`, do
**not** re-prove, do **not** cite as this theorem). **Not**
Fermat two-square (`Nat.Prime.sq_add_sq` already-in; do
**not** re-prove; do **not** cite as non-UFD). **Not**
four-square / three-square (consumed #159; sums of squares
≠ factorization in `ℤ√(-5)`). **Not** Dedekind-domain
ideal UFM / class number 2 (residual of *this* id; do
**not** sorry class group). **Not** Kummer `padicValNat_choose`
(already-in; different Kummer). **Not** Myhill–Nerode
(consumed #162). **Not** Gray codes (consumed #163). **Not**
frobenius-real-division (consumed #105; `ℝ,ℂ,ℍ` ≠ `ℤ√(-5)`).

Mathlib v4.10.0 already has the **Zsqrtd / norm infra this
theorem needs**:

- `Zsqrtd` / prefix `ℤ√` (NumberTheory/Zsqrtd/Basic.lean L28 / L34)
- `sqrtd` L80 / `norm` L436 / `norm_mul` L462 / `norm_eq_zero_iff` L518
- `Irreducible` (Algebra/Associated/Basic.lean L174)
- `UniqueFactorizationMonoid` (RingTheory/UniqueFactorizationDomain.lean L179)

There is **no** named `zsqrt5` / `not_ufd` / `UniqueFactorizationMonoid (ℤ√` /
`ℤ√(-5)` non-UFD theorem anywhere under `Mathlib/` or
`Archive/` or `ProofLab/` (this run → ZERO on those
names; `GaussianInt` Euclidean is a different ring). Do
**not** import `Archive.*`.

OPE-1357 shortlist is **CONSUMED** (#162+#163). This is a
**fresh** catalog-audit prime, **not** a Gray leftover
continuation, **not** a Myhill–Nerode leftover, **not** a
three-square leftover, **not** a prize leftover, **not** a
Formalist Level B revival, **not** a third slot.

Mill NOW: finite factorization witnesses on Mathlib
`Zsqrtd.norm`. `norm` / `Irreducible` are waiting the same
way `hammingDist` waited for Gray. **Not a rubber-stamp of
GaussianInt.** **Not a rubber-stamp of two-square.**

Do **not** describe an attack as discovering that ℤ[√-5]
fails unique factorization. Do **not** expand into class
number 2 / Dedekind domain as a sorry (that is
leftover-risk of *this* id — do **not** sorry it). Do
**not** label theorems `kummer_*` / `gaussian_*` /
`sq_add_sq_*` as the namesake.

## Pinned convention (exact)

**v1 Level A is named small-factorization witnesses:
`6 = 2*3 = (1+√-5)(1-√-5)` in `ℤ√(-5)`, 2 does not
divide `1+√-5`, and 2 is irreducible hence not prime,
not labelled Dedekind / Kummer / Gaussian.**

Suggested pin:

```text
-- Level A (not labelled Dedekind / Kummer / Gaussian):
-- named small-factorization witnesses.

abbrev Zsqrt5 := ℤ√(-5)

theorem six_two_three :
    (2 : Zsqrt5) * 3 = 6

theorem six_split :
    (⟨1, 1⟩ : Zsqrt5) * ⟨1, -1⟩ = 6

theorem two_not_dvd_one_plus_sqrtd :
    ¬ (2 : Zsqrt5) ∣ ⟨1, 1⟩

theorem two_irreducible :
    Irreducible (2 : Zsqrt5)

-- optional extra: 3 irreducible / ⟨1,1⟩ irreducible / not associates

-- Level B namesake (not a UFM; residual OK)
theorem zsqrt5_not_ufd :
    ¬ UniqueFactorizationMonoid Zsqrt5
    -- do not sorry the namesake
```

Named small-factorization witnesses are load-bearing.
The two products equal 6, and 2 irreducible-not-prime,
are load-bearing (so the theorem is **not** “some
elements of `Zsqrtd` multiply”).

**Level A may land only** the 6=2·3 / 6=(1+√-5)(1-√-5) /
2 ∤ 1+√-5 / 2 irreducible (optional extras: 3 and 1+√-5
irreducible), **not** labelled Dedekind / Kummer /
Gaussian. Reuse Mathlib `Zsqrtd.norm` — **do not re-prove**
GaussianInt Euclidean / two-square / three-square.

**Level B** is the namesake `¬ UniqueFactorizationMonoid`.
Do not sorry the namesake; honest partial is allowed
(comment residual, not `sorry`). Class number / Dedekind
domain extras are residual.

## Landmines

1. **Do not re-prove** `Zsqrtd` / `norm` / `norm_mul` /
   `Irreducible`. Already Mathlib. Use them if needed.
2. **This is not** `EuclideanDomain ℤ[i]` (already-in
   GaussianInt.lean L243). Different ring. USE `Zsqrtd`.
3. **This is not** `Nat.Prime.sq_add_sq` / four-square /
   three-square (already-in / consumed #159).
4. **This is not** Dedekind-domain ideal UFM / class
   number 2. Residual of this id. Do not sorry it.
5. **This is not** Kummer `padicValNat_choose` (already-in).
6. **This is not** myhill-nerode / gray-code (consumed
   #162+#163). Do not prove Nerode / Gray here.
7. **This is not** frobenius-real-division / octonions /
   Hurwitz (consumed #105).
8. **This is not** `d8-ne-q8` (leftover of this shortlist).
   Do not prove D8 ≇ Q8 here.
9. **Do not** re-prime the consumed mill list.
10. **Leave OPE-403 alone.** Leave OPE-1195 leftover status
    alone.
11. **Do not import `Archive.*`.**
12. Default no claim. No novelty claim.

## Out of v1

- Namesake `¬ UniqueFactorizationMonoid (ℤ√(-5))`
- Class number 2 / Dedekind domain / ideal factorization
- Other `d` (√-3, √-6, …)
- Prize claims / Millennium / Beal
