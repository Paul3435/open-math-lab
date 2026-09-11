# D₈ ≇ Q₈ (reflections order 2 vs unique order-2, formalize-only)

**id:** `d8-ne-q8`
**ticket:** OPE-1374 Scout leftover slot #2 (parent OPE-1373;
post myhill-nerode #162 + gray-code #163)
**expected:** known-classical (classification of groups of
order 8: the dihedral group of the square is not the
quaternion group) —
**no novelty claim**

## Why not classical / why formalize-only

Settled finite group theory: `DihedralGroup 4` (order 8)
has four reflections of order 2, while `QuaternionGroup 2`
(order 8) has a unique element of order 2 (`a n`) and every
`xa i` has order 4; hence the groups are not isomorphic.
Completely classical. The namesake “the only groups of
order 8 are C8, C4×C2, C2³, D8, Q8” is a **different**,
larger residual — do **not** sorry it.

Not an open problem. Not a novelty claim. Not live cash.

**Not** Frucht (consumed #150; realizing groups as Aut of
graphs ≠ D8 ≇ Q8 as abstract groups; do **not** revive
Cayley-graph gadgets / GRR / `Aut(K_n)≅S_n`; do **not**
define the square’s Aut as this theorem). **Not**
frobenius-real-division (consumed #105; real division
algebras `ℝ,ℂ,ℍ` ≠ the finite group Q8; Quaternion.lean
TODO `QuaternionGroup 2 ≃* (Quaternion ℤ)ˣ` is residual
of *this* id — do **not** sorry it). **Not** A5 simple
(`alternatingGroup.isSimpleGroup_five` L289 already-in;
different group). **Not** `quaternionGroupZeroEquivDihedralGroupZero`
(Quaternion.lean L141 already-in; **infinite** n=0 case,
**not** D8 vs Q8; do **not** cite as an isomorphism of
order-8 groups). **Not** Myhill–Nerode (consumed #162).
**Not** Gray codes (consumed #163). **Not** `zsqrt5-not-ufd`
(prime of this shortlist).

Mathlib v4.10.0 already has the **Dihedral / Quaternion
infra this theorem needs**:

- `DihedralGroup` (GroupTheory/SpecificGroups/Dihedral.lean L24)
- `card` L117 (`2 * n`) / `orderOf_sr` L147 (`= 2`)
- `QuaternionGroup` (GroupTheory/SpecificGroups/Quaternion.lean L51)
- `card` L165 (`4 * n`) / `orderOf_xa` L197 (`= 4`)
- `quaternionGroupZeroEquivDihedralGroupZero` L141 (n=0 only; **not** namesake)

There is **no** named `d8_ne_q8` / `DihedralGroup 4 ≃* QuaternionGroup 2`
negation / `not_mulEquiv_dihedral_quaternion` anywhere under
`Mathlib/` or `Archive/` or `ProofLab/` (this run → ZERO on
those names; n=0 isomorphism is a different theorem). Do
**not** import `Archive.*`.

OPE-1357 shortlist is **CONSUMED** (#162+#163). This is a
**fresh** catalog-audit leftover id, **not** a Frucht
leftover continuation, **not** a Gray leftover, **not** a
Myhill–Nerode leftover, **not** a prize leftover, **not** a
Formalist Level B revival, **not** a third slot.

Mill NOW: finite order-2 counting leftover beside ℤ[√-5]
factorization witnesses. `orderOf_sr` / `orderOf_xa` are
waiting the same way `norm` waited for the prime. **Not a
rubber-stamp of Frucht.** **Not a rubber-stamp of n=0
isomorphism.**

Do **not** describe an attack as discovering D8 ≇ Q8.
Do **not** expand into the full order-8 classification as
a sorry (that is leftover-risk of *this* id — do **not**
sorry it). Do **not** label theorems `frucht_*` /
`aut_*` / `frobenius_*` as this non-isomorphism.

## Pinned convention (exact)

**v1 Level A is named small-order witnesses: both groups
have card 8, `sr 0` on `DihedralGroup 4` has order 2,
`xa 0` on `QuaternionGroup 2` has order 4, and there is
no multiplicative equivalence, not labelled Frucht /
Frobenius / Cayley.**

Suggested pin:

```text
-- Level A (not labelled Frucht / Frobenius / Cayley):
-- named small-order witnesses.

theorem dihedral_four_card :
    Fintype.card (DihedralGroup 4) = 8

theorem quaternion_two_card :
    Fintype.card (QuaternionGroup 2) = 8

theorem dihedral_sr_order_two :
    orderOf (DihedralGroup.sr 0 : DihedralGroup 4) = 2

theorem quaternion_xa_order_four :
    orderOf (QuaternionGroup.xa 0 : QuaternionGroup 2) = 4

-- optional extra: two distinct D8 reflections both order 2
-- (sr 0 ≠ sr 1), vs unique order-2 in Q8

-- Level B namesake (no MulEquiv; residual OK)
theorem d8_ne_q8 :
    IsEmpty (DihedralGroup 4 ≃* QuaternionGroup 2)
    -- do not sorry the namesake
```

Named small-order witnesses are load-bearing.
Card 8 + a reflection of order 2 + an `xa` of order 4
are load-bearing (so the theorem is **not** “some
inductive groups exist”).

**Level A may land only** the card-8 / `orderOf_sr` /
`orderOf_xa` witnesses (optional extra: two D8
reflections vs unique Q8 order-2), **not** labelled
Frucht / Frobenius / Cayley. Reuse Mathlib `orderOf_sr` /
`orderOf_xa` — **do not re-prove** Frucht / A5 simple /
n=0 isomorphism.

**Level B** is the namesake `IsEmpty (D8 ≃* Q8)` / full
order-8 classification. Do not sorry the namesake; honest
partial is allowed (comment residual, not `sorry`).
`QuaternionGroup 2 ≃* (Quaternion ℤ)ˣ` extras are residual.

## Landmines

1. **Do not re-prove** `DihedralGroup.card` / `orderOf_sr` /
   `QuaternionGroup.card` / `orderOf_xa`. Already Mathlib.
   Use them if needed.
2. **This is not** `quaternionGroupZeroEquivDihedralGroupZero`
   (already-in L141; infinite n=0). Do not cite as D8≅Q8.
3. **This is not** Frucht / Cayley-graph / GRR /
   `Aut(K_n)≅S_n` (consumed #150 residual). Do not define
   the square’s Aut as this theorem.
4. **This is not** frobenius-real-division / `ℍ` as a
   division algebra (consumed #105). Do not sorry
   `QuaternionGroup 2 ≃* (Quaternion ℤ)ˣ`.
5. **This is not** A5 simple (already-in L289).
6. **This is not** myhill-nerode / gray-code (consumed
   #162+#163).
7. **This is not** `zsqrt5-not-ufd` (OPE-1374 prime). Do
   not prove ℤ[√-5] here.
8. **Do not** re-prime the consumed mill list.
9. **Leave OPE-403 alone.** Leave OPE-1195 leftover status
   alone.
10. **Do not import `Archive.*`.**
11. Default no claim. No novelty claim.

## Out of v1

- Namesake `IsEmpty (DihedralGroup 4 ≃* QuaternionGroup 2)`
- Full classification of groups of order 8
- `QuaternionGroup 2 ≃* (Quaternion ℤ)ˣ`
- Prize claims / Millennium / Beal
