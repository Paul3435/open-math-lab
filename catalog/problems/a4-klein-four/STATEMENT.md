# Double transpositions in A₄ are even of order 2 (formalize-only)

**id:** `a4-klein-four`
**ticket:** OPE-1405 Scout leftover slot #2 (parent OPE-1404;
post taxicab-1729 #168 + euler-brick #169)
**expected:** known-classical (the three double
transpositions `(0 1)(2 3)`, `(0 2)(1 3)`, `(0 3)(1 2)`
are even permutations of order 2 in `A₄`; they generate
the Klein four-group `V ⊴ A₄`) —
**no novelty claim**

## Why not classical / why formalize-only

Settled undergraduate finite-group arithmetic. Pin the
standard even double transposition on `Fin 4`:

- `σ = swap 0 1 * swap 2 3`
- `sign σ = 1` (product of two disjoint transpositions)
- `σ ∈ alternatingGroup (Fin 4)`
- `orderOf σ = 2`

Completely classical. Mathlib v4.10.0 already has
`IsKleinFour` as a mixin (`card = 4` and exponent 2) with
instances on `ZMod 2 × ZMod 2` and `DihedralGroup 2`, and
an **in-tree TODO** (KleinFour.lean L30) to identify that
class with the normal subgroup

`V = {1, (1 2)(3 4), (1 3)(2 4), (1 4)(2 3)} ⊴ A₄`.

The namesake “`IsKleinFour` ≃* that normal `V` / exact
sequence `V → A₄ → A₃`” is a **different**, larger residual
— do **not** sorry it. The “`A₄` has no subgroup of order
6” fact is also residual of *this* id (C6-vs-S3 definition
risk if used as Level A) — do **not** sorry it, do **not**
make “no order-6 subgroup” the namesake of Level A.

Not an open problem. Not a novelty claim. Not live cash.

**Not** `alternatingGroup.isSimpleGroup_five`
(Alternating.lean L289 already-in: `A₅` is simple —
**different** group `Fin 5`; USE `alternatingGroup` /
`sign`, do **not** re-prove A₅ simple, do **not** cite as
this A₄ double transposition). **Not** the TODO
“`alternatingGroup α` simple iff `card α ≠ 4`”
(Alternating.lean L37 TODO; residual; do **not** sorry
A₄-not-simple as namesake). **Not** `IsKleinFour`
(`KleinFour.lean` L51 already-in mixin) / instance
`IsKleinFour (DihedralGroup 2)` L63 / instance
`IsKleinFour` on `ZMod 2 × ZMod 2` L59 — **already-in
different carriers**, glue **not** namesake (do **not**
re-prove the mixin, do **not** cite `DihedralGroup 2` as
this A₄ theorem). **Not** d8-ne-q8 (consumed #166;
`DihedralGroup 4` vs `QuaternionGroup 2` is order 8, not
the order-4 `V` in `A₄`; do **not** revive `d8_ne_q8` /
order-8 classification). **Not** Frucht (consumed #150).
**Not** frobenius-real-division (consumed #105). **Not**
A₆ outer automorphism (KleinFour.lean L35 TODO; residual;
do **not** sorry it). **Not** taxicab-1729 / euler-brick
(consumed #168+#169). **Not** simpson-paradox (prime of
this shortlist).

Mathlib v4.10.0 already has the **permutation / sign infra
this theorem needs**:

- `Equiv.swap` (Logic/Equiv/Basic.lean L1383)
- `Equiv.Perm.sign` (GroupTheory/Perm/Sign.lean L365)
- `sign_mul` L373 / `sign_swap` L396
- `alternatingGroup` (SpecificGroups/Alternating.lean L51)
- `mem_alternatingGroup` L69
- `two_mul_card_alternatingGroup` L88
- `Fintype.card_perm` (Data/Fintype/Perm.lean L150)
- `orderOf`
- `IsKleinFour` mixin L51 — **different carrier**, not namesake

There is **no** named `a4_klein` / `kleinFour_A4` /
`doubleTransposition_mem_alternating` / `V4_normal_A4`
theorem anywhere under `Mathlib/` or `Archive/` or
`ProofLab/` (this run → ZERO on those names; `IsKleinFour`
on `DihedralGroup 2` is a different carrier). Do **not**
import `Archive.*`.

OPE-1390 shortlist is **CONSUMED** (#168+#169). This is a
**fresh** catalog-audit leftover id, **not** a d8 leftover
continuation, **not** an A₅-simple leftover, **not** a
Frucht leftover, **not** a prize leftover, **not** a
Formalist Level B revival, **not** a third slot.

Mill NOW: finite even double-transposition witnesses on
Mathlib `sign` / `swap` / `alternatingGroup`. **Not a
rubber-stamp of `isSimpleGroup_five`.** **Not a
rubber-stamp of `IsKleinFour (DihedralGroup 2)`.** **Not
a rubber-stamp of d8-ne-q8.**

Do **not** describe an attack as discovering V₄. Do **not**
expand into the KleinFour.lean L30 isomorphism as a sorry
(that is leftover-risk of *this* id — do **not** sorry it).
Do **not** label theorems `simple_*` / `d8_*` / `frucht_*`
as the namesake.

## Pinned convention (exact)

**v1 Level A is named small-permutation witnesses:
`sign (swap 0 1 * swap 2 3) = 1` / membership in
`alternatingGroup (Fin 4)` / `orderOf = 2`, not labelled
Klein / A₄ / Vierergruppe.**

Suggested pin:

```text
-- Level A (not labelled Klein / A4 / Vierergruppe):
-- named even double-transposition witnesses on Fin 4.

theorem doubleTransp_sign :
    Equiv.Perm.sign
      (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3) = 1

theorem doubleTransp_mem :
    Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3
      ∈ alternatingGroup (Fin 4)

theorem doubleTransp_order_two :
    orderOf (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3) = 2

-- optional extra: the other two double transpositions,
-- or (swap 0 1 * swap 2 3) * (swap 0 2 * swap 1 3)
--   = swap 0 3 * swap 1 2

-- Level B namesake (IsKleinFour ≃* V ⊴ A4; residual OK)
theorem a4_klein_four ...
    -- do not sorry the namesake
```

Named even order-2 double transposition is load-bearing.
`sign = 1` and `orderOf = 2` so the theorem is **not**
“some permutations exist.”

**Level A may land only** the sign / membership / order-2
witness (optional extra: the other two double
transpositions or the product identity), **not** labelled
Klein / A₄ / Vierergruppe. Reuse Mathlib `swap` / `sign` /
`alternatingGroup` — **do not re-prove** `IsKleinFour` /
A₅ simple / d8-ne-q8.

**Level B** is the namesake KleinFour.lean L30 isomorphism.
Do not sorry the namesake; honest partial is allowed
(comment residual, not `sorry`). A₄-not-simple / no
subgroup of order 6 / A₆ outer aut extras are residual.

## Landmines

1. **Do not re-prove** `Equiv.swap` / `sign` / `sign_swap`
   / `alternatingGroup` / `orderOf`. Already Mathlib. Use
   them.
2. **This is not** `isSimpleGroup_five` (Alternating.lean
   L289 already-in). Different group. USE `sign`.
3. **This is not** `IsKleinFour (DihedralGroup 2)` /
   `ZMod 2 × ZMod 2` (already-in different carriers).
4. **This is not** the KleinFour.lean L30 isomorphism
   `V ≃* A₄` kernel. Residual of this id. Do not sorry it.
5. **This is not** “A₄ has no subgroup of order 6.”
   Residual (C6 vs S3 definition risk). Do not sorry it;
   do not make it Level A.
6. **This is not** d8-ne-q8 (consumed #166). Order 8 ≠
   order-4 V in A₄. Do not revive order-8 classification.
7. **This is not** Frucht / frobenius-real-division
   (consumed #150 / #105).
8. **This is not** taxicab-1729 / euler-brick (consumed
   #168+#169).
9. **This is not** `simpson-paradox` (OPE-1405 prime).
   Do not prove the 2×2×2 table here.
10. **Do not** re-prime the consumed mill list.
11. **Leave OPE-403 alone.** Leave OPE-1195 leftover status
    alone.
12. **Do not import `Archive.*`.**
13. Default no claim. No novelty claim.

## Out of v1

- Namesake `IsKleinFour` ≃* normal V in A₄ / `V → A₄ → A₃`
- A₄ not simple / no subgroup of order 6
- A₆ outer automorphism / S₆ outer aut
- Order-8 classification / d8_ne_q8
- Prize claims / Millennium / Beal
