/-
Named even double-transposition witnesses — Level A only
(`sign (swap 0 1 * swap 2 3) = 1` /
`swap 0 1 * swap 2 3 ∈ alternatingGroup (Fin 4)` /
`orderOf = 2`).
**Not labelled Klein / A4 / Vierergruppe.**

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 pin `a719ba5c3115` has `Equiv.swap` / `sign` /
`sign_mul` / `sign_swap` / `alternatingGroup` /
`mem_alternatingGroup` / `orderOf` as **infra**.
ZERO named `a4_klein` / `kleinFour_A4` / `V4_normal_A4` /
`doubleTransposition_mem_alternating` theorem under `Mathlib/`
or `Archive/` or `ProofLab/` (this run). Completing the Level A
named even order-2 double transposition is the gap this ticket
lands. The Level B namesake `a4_klein_four`
(`IsKleinFour ≃*` normal `V ⊴ A₄` / KleinFour.lean L30 TODO)
is **out of this ticket** and is **not** sorry-ed. A₄-not-simple
/ no subgroup of order 6 / A₆ outer aut extras are residual of
this id — **out of v1**, not sorry-ed. Do **not** label theorems
`a4_klein_four` / `klein_*` / `simple_*` / `d8_*` / `frucht_*`
as the namesake. Do **not** define the namesake via
`IsKleinFour` on `DihedralGroup 2` / `ZMod 2 × ZMod 2`.

Pin: `catalog/problems/a4-klein-four/STATEMENT.md`
(OPE-1414; Scout OPE-1405 leftover slot #2; Director OPE-1409 HOLD).
Encoding: named even double-transposition witnesses via Mathlib
`Equiv.swap` / `sign` / `sign_mul` / `sign_swap` /
`alternatingGroup` / `mem_alternatingGroup` / `orderOf`.
Zero `sorry`. Do not import `Archive.*`.

This is **not** `Equiv.swap` / `sign` / `sign_swap` /
`alternatingGroup` / `orderOf` — already Mathlib.
**USE, do not re-prove; do not cite as this A₄ witness.**
This is **not** `alternatingGroup.isSimpleGroup_five`
(Alternating.lean L289 already-in: `A₅` is simple) —
**different** group `Fin 5`. USE `sign`; do **not** re-prove
A₅ simple; do **not** cite as this double transposition.
This is **not** `IsKleinFour` (KleinFour.lean L51) /
instance `IsKleinFour (DihedralGroup 2)` L63 /
instance `IsKleinFour` on `ZMod 2 × ZMod 2` L59 —
already-in **different carriers**. Do **not** re-prove the mixin.
This is **not** the KleinFour.lean L30 isomorphism
`IsKleinFour ≃*` normal `V` in `A₄`. Residual of this id.
Do **not** sorry it.
This is **not** “A₄ has no subgroup of order 6”
(residual; C6 vs S3 definition risk). Do **not** sorry it;
do **not** make it Level A.
This is **not** D8 ≇ Q8 (`ProofLab/D8NeQ8.lean`, consumed #166).
Order 8 ≠ order-4 `V` in `A₄`. Do **not** revive order-8
classification.
This is **not** simpson-paradox (`ProofLab/SimpsonParadox.lean`,
consumed #171). Rates ≠ permutations.
This is **not** taxicab-1729 (`ProofLab/Taxicab1729.lean`,
consumed #168). Cubes ≠ permutations.
This is **not** euler-brick (`ProofLab/EulerBrick.lean`,
consumed #169). Face diagonals ≠ permutations.
This is **not** ℤ[√-5] not UFD (`ProofLab/Zsqrt5NotUfd.lean`,
consumed #165).
This is **not** Frucht (`ProofLab/FruchtGraphAut.lean`, consumed #150).
Do not re-prime the consumed mill. Leave OPE-403 alone.
Leave OPE-1195 alone.

v1 is named even order-2 double transposition:
`sign (swap 0 1 * swap 2 3) = 1`, membership in
`alternatingGroup (Fin 4)`, `orderOf = 2`,
**not labelled Klein / A4 / Vierergruppe**.
`sign = 1` and `orderOf = 2` are load-bearing (so Level A is
**not** “some permutations exist”).

Level A: `doubleTransp_sign` / `doubleTransp_mem` /
`doubleTransp_order_two`.
Optional extra: the other two double transpositions, or the
product identity
`(swap 0 1 * swap 2 3) * (swap 0 2 * swap 1 3)
  = swap 0 3 * swap 1 2`.
**Not** labelled Klein / A4 / Vierergruppe.

Transcribed classical argument (the three double transpositions
`(0 1)(2 3)`, `(0 2)(1 3)`, `(0 3)(1 2)` are even of order 2
in `A₄`). Compact form: Wikipedia *Alternating group* / *Klein
four-group*. Type pin: `Equiv.swap` / `sign` /
`alternatingGroup (Fin 4)`. `IsKleinFour` on `DihedralGroup 2`
is a different already-in carrier. A₅ simple is a different
already-in theorem. Simpson-paradox is the consumed prime of
this shortlist. No novelty claim. Default no claim.

Level B namesake OUT of this ticket (do not sorry):
-- theorem a4_klein_four ...
--     -- do not sorry the namesake
-/
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

namespace ProofLab.A4KleinFour

open Equiv Equiv.Perm

/-! ## Level A: sign=1 / mem A₄ / orderOf=2
(not labelled Klein / A4 / Vierergruppe) -/

/-- `σ = swap 0 1 * swap 2 3` is even.
Glue: Mathlib `sign_mul` / `sign_swap`.
Not labelled Klein / A4 / Vierergruppe.
Load-bearing named even double transposition on `Fin 4`. -/
theorem doubleTransp_sign :
    Equiv.Perm.sign
      (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3) = 1 := by
  rw [Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap (by decide : (0 : Fin 4) ≠ 1),
      Equiv.Perm.sign_swap (by decide : (2 : Fin 4) ≠ 3)]
  rfl

/-- `σ = swap 0 1 * swap 2 3` lies in `alternatingGroup (Fin 4)`.
Glue: Mathlib `mem_alternatingGroup` + `doubleTransp_sign`.
Not labelled Klein / A4 / Vierergruppe. -/
theorem doubleTransp_mem :
    Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3
      ∈ alternatingGroup (Fin 4) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  exact doubleTransp_sign

/-- The two factors of `σ` commute: disjoint transpositions.
Glue: Mathlib `swap_mul_eq_mul_swap`. -/
lemma doubleTransp_commute :
    Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3 =
      Equiv.swap 2 3 * Equiv.swap 0 1 := by
  -- `swap 2 3` fixes 0 and 1, so conjugating `swap 0 1` is a no-op.
  rw [swap_mul_eq_mul_swap]
  simp [swap_inv, swap_apply_of_ne_of_ne]

/-- `σ² = 1`. Glue: commute + `swap_mul_self`. -/
lemma doubleTransp_sq :
    (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3) ^ 2 = 1 := by
  -- `(s*t)^2 = s*(t*(s*t)) = s*((t*s)*t) = s*((s*t)*t) = (s*s)*(t*t)`.
  rw [pow_two, mul_assoc]
  have hts :
      Equiv.swap (2 : Fin 4) 3 * Equiv.swap 0 1 =
        Equiv.swap 0 1 * Equiv.swap 2 3 := doubleTransp_commute.symm
  rw [← mul_assoc (Equiv.swap (2 : Fin 4) 3), hts, mul_assoc,
      swap_mul_self, mul_one, swap_mul_self]

/-- `σ ≠ 1`. Evaluates at `0`: left side is `1`, right side is `0`. -/
lemma doubleTransp_ne_one :
    Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3 ≠ 1 := by
  intro h
  have h0 :
      ((Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3 : Perm (Fin 4)) 0) =
        (1 : Perm (Fin 4)) 0 := by rw [h]
  have hleft :
      ((Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3 : Perm (Fin 4)) 0) =
        1 := by
    rw [mul_apply]
    have ht : Equiv.swap (2 : Fin 4) 3 0 = 0 :=
      swap_apply_of_ne_of_ne (by decide) (by decide)
    rw [ht, swap_apply_left]
  have hright : ((1 : Perm (Fin 4)) 0) = 0 := rfl
  exact absurd (hleft.symm.trans (h0.trans hright)) (by decide)

/-- `σ` has order 2.
Glue: Mathlib `orderOf_eq_prime` (with `Fact (Nat.Prime 2)`).
Not labelled Klein / A4 / Vierergruppe.
Load-bearing named order-2 double transposition on `Fin 4`. -/
theorem doubleTransp_order_two :
    orderOf (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime doubleTransp_sq doubleTransp_ne_one

/-- Optional extra: the other two double transpositions are even. -/
theorem doubleTransp_02_13_sign :
    Equiv.Perm.sign
      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap 1 3) = 1 := by
  rw [Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap (by decide : (0 : Fin 4) ≠ 2),
      Equiv.Perm.sign_swap (by decide : (1 : Fin 4) ≠ 3)]
  rfl

theorem doubleTransp_03_12_sign :
    Equiv.Perm.sign
      (Equiv.swap (0 : Fin 4) 3 * Equiv.swap 1 2) = 1 := by
  rw [Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap (by decide : (0 : Fin 4) ≠ 3),
      Equiv.Perm.sign_swap (by decide : (1 : Fin 4) ≠ 2)]
  rfl

/-- Optional extra: product identity of the three double transpositions.
`(swap 0 1 * swap 2 3) * (swap 0 2 * swap 1 3) = swap 0 3 * swap 1 2`.
Does **not** sorry the KleinFour.lean L30 namesake. -/
theorem doubleTransp_product :
    (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3) *
      (Equiv.swap 0 2 * Equiv.swap 1 3) =
      Equiv.swap 0 3 * Equiv.swap 1 2 := by
  ext i
  fin_cases i <;> decide

/-
Residual (Level B, **out of this ticket**, not sorry-ed):
`a4_klein_four` — `IsKleinFour ≃*` normal `V ⊴ A₄`
(KleinFour.lean L30 TODO). Do **not** sorry the namesake.
A₄-not-simple / no subgroup of order 6 / A₆ outer aut are
residual of this id, **out of v1**; do **not** sorry them.
Do **not** prove `a4_klein_four` as namesake / `IsKleinFour ≃* V ⊴ A₄`
/ A₄ no subgroup of order 6 / A₄-not-simple / A₆ outer aut /
`isSimpleGroup_five` as namesake / `IsKleinFour` as namesake /
d8-ne-q8 leftover-revivals / order-8 classification /
simpson-paradox leftover-revivals / taxicab-1729 leftover-revivals /
euler-brick leftover-revivals / perfect cuboid /
zsqrt5-not-ufd leftover-revivals / UniqueFactorizationMonoid /
myhill-nerode / gray-code / Frucht leftover-revivals.
Leave OPE-403 alone. Leave OPE-1195 alone.
Do **not** label theorems `a4_klein_four` / `klein_*` /
`simple_*` / `d8_*` / `frucht_*`.
-/

end ProofLab.A4KleinFour
