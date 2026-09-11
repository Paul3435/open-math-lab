/-
Named small-order witnesses — Level A only
(`Fintype.card (DihedralGroup 4) = 8` /
`Fintype.card (QuaternionGroup 2) = 8` /
`orderOf (sr 0) = 2` / `orderOf (xa 0) = 4`).
**Not labelled Frucht / Frobenius / Cayley.**

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 pin `a719ba5c3115` has `DihedralGroup` / `card` /
`orderOf_sr` / `QuaternionGroup` / `card` / `orderOf_xa` as **infra**.
ZERO named `d8_ne_q8` / `not_mulEquiv_dihedral` /
`DihedralGroup 4 ≃* QuaternionGroup 2` theorem under `Mathlib/` or
`Archive/` or `ProofLab/` (this run). Completing the Level A named
small-order witnesses is the gap this ticket lands. The Level B
namesake `d8_ne_q8` (`IsEmpty (DihedralGroup 4 ≃* QuaternionGroup 2)`)
is **out of this ticket** and is **not** sorry-ed. Full order-8
classification / `QuaternionGroup 2 ≃* (Quaternion ℤ)ˣ` extras are
residual of this id. Do **not** label theorems `frucht_*` / `aut_*` /
`frobenius_*` / `cayley_*` as this non-isomorphism. Do **not** define
the namesake via Aut of the square.

Pin: `catalog/problems/d8-ne-q8/STATEMENT.md`
(OPE-1385; Scout OPE-1374 leftover slot #2; Director OPE-1384).
Encoding: named small-order witnesses via Mathlib `DihedralGroup.card` /
`orderOf_sr` / `QuaternionGroup.card` / `orderOf_xa`.
Zero `sorry`. Do not import `Archive.*`.

This is **not** `DihedralGroup.card` / `orderOf_sr` /
`QuaternionGroup.card` / `orderOf_xa`
(`GroupTheory/SpecificGroups/Dihedral.lean` L117 / L147;
`Quaternion.lean` L165 / L197) — already Mathlib.
**USE, do not re-prove; do not cite as D8 ≇ Q8.**
This is **not** `quaternionGroupZeroEquivDihedralGroupZero`
(`Quaternion.lean` L141). Infinite n=0 isomorphism, **not** D8 vs Q8.
USE as contrast; do **not** re-prove; do **not** cite as D8≅Q8.
This is **not** Frucht (`ProofLab/FruchtGraphAut.lean`, consumed #150).
Do **not** revive Cayley-graph / GRR / `Aut(K_n)≅S_n`; do **not**
define the square's Aut as this theorem.
This is **not** frobenius-real-division
(`ProofLab/FrobeniusRealDivision.lean`, consumed #105).
Do **not** revive ℍ AlgEquiv; do **not** sorry
`QuaternionGroup 2 ≃* (Quaternion ℤ)ˣ`.
This is **not** A5 simple (`alternatingGroup.isSimpleGroup_five` L289).
This is **not** Myhill–Nerode (`ProofLab/MyhillNerode.lean`, consumed #162).
Do **not** revive Kleene regex iff DFA.
This is **not** Gray codes (`ProofLab/GrayCode.lean`, consumed #163).
Do **not** revive hypercube Hamiltonian.
This is **not** ℤ[√-5] not UFD (`ProofLab/Zsqrt5NotUfd.lean`, consumed #165).
Do **not** revive UniqueFactorizationMonoid / class number 2.
Do not re-prime the consumed mill. Leave OPE-403 alone.
Leave OPE-1195 alone.

v1 is named small-order witnesses: both groups have card 8,
`sr 0` on `DihedralGroup 4` has order 2, `xa 0` on
`QuaternionGroup 2` has order 4, **not labelled Frucht /
Frobenius / Cayley**. Card 8 + a reflection of order 2 + an
`xa` of order 4 are load-bearing (so Level A is **not**
"some inductive groups exist").

Level A: `dihedral_four_card` / `quaternion_two_card` /
`dihedral_sr_order_two` / `quaternion_xa_order_four`.
Optional extra: two distinct D8 reflections both order 2
(`sr 0 ≠ sr 1`); unique order-2 in Q8 (`a 2`).
**Not** labelled Frucht / Frobenius / Cayley.

Transcribed classical argument (classification of groups of
order 8: D8 has reflections of order 2, Q8 has `xa` of order 4
and a unique order-2 element). Compact form: Wikipedia
*Dihedral group* / *Quaternion group*. Type pin:
`DihedralGroup 4` / `QuaternionGroup 2` / `orderOf`.
n=0 isomorphism is a different already-in theorem. Frucht is
a different consumed mill. ℤ[√-5] not UFD is the consumed
prime of this shortlist. No novelty claim. Default no claim.

Level B namesake OUT of this ticket (do not sorry):
-- theorem d8_ne_q8 :
--     IsEmpty (DihedralGroup 4 ≃* QuaternionGroup 2)
-/
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.Tactic

namespace ProofLab.D8NeQ8

open DihedralGroup QuaternionGroup

/-- `DihedralGroup 4` has 8 elements. Glue: Mathlib `DihedralGroup.card`
(`2 * 4 = 8`). Not labelled Frucht. -/
theorem dihedral_four_card : Fintype.card (DihedralGroup 4) = 8 :=
  DihedralGroup.card

/-- `QuaternionGroup 2` has 8 elements. Glue: Mathlib `QuaternionGroup.card`
(`4 * 2 = 8`). Not labelled Frobenius. -/
theorem quaternion_two_card : Fintype.card (QuaternionGroup 2) = 8 :=
  QuaternionGroup.card

/-- A reflection of `DihedralGroup 4` has order 2.
Glue: Mathlib `DihedralGroup.orderOf_sr`. Not labelled Cayley. -/
theorem dihedral_sr_order_two :
    orderOf (sr 0 : DihedralGroup 4) = 2 :=
  DihedralGroup.orderOf_sr _

/-- An `xa` of `QuaternionGroup 2` has order 4.
Glue: Mathlib `QuaternionGroup.orderOf_xa`. Not labelled Frobenius. -/
theorem quaternion_xa_order_four :
    orderOf (xa 0 : QuaternionGroup 2) = 4 :=
  QuaternionGroup.orderOf_xa _

/-- Optional extra: two distinct D8 reflections, both order 2. -/
theorem dihedral_sr_zero_ne_one :
    (sr 0 : DihedralGroup 4) ≠ sr 1 := by
  intro h
  injection h with h'
  exact absurd h' (by decide)

theorem dihedral_two_reflections_order_two :
    (sr 0 : DihedralGroup 4) ≠ sr 1 ∧
      orderOf (sr 0 : DihedralGroup 4) = 2 ∧
      orderOf (sr 1 : DihedralGroup 4) = 2 :=
  ⟨dihedral_sr_zero_ne_one, DihedralGroup.orderOf_sr _, DihedralGroup.orderOf_sr _⟩

/-- Optional extra: unique order-2 element of Q8 is `a 2`. -/
theorem quaternion_a_two_order_two :
    orderOf (a 2 : QuaternionGroup 2) = 2 := by
  rw [QuaternionGroup.orderOf_a]
  have : (2 : ZMod (2 * 2)).val = 2 := rfl
  simp [this]

theorem quaternion_eq_a_two_of_order_two {g : QuaternionGroup 2}
    (hg : orderOf g = 2) : g = a 2 := by
  cases g with
  | xa i =>
    have := QuaternionGroup.orderOf_xa (n := 2) i
    omega
  | a i =>
    have hi : orderOf (a i : QuaternionGroup 2) = 4 / Nat.gcd 4 i.val := by
      simpa using QuaternionGroup.orderOf_a (n := 2) i
    have hdiv : 4 / Nat.gcd 4 i.val = 2 := by
      rw [← hi, hg]
    have hval : i.val = 2 := by
      have : i.val < 4 := ZMod.val_lt i
      interval_cases i.val
      · -- gcd 4 0 = 4, 4/4 = 1
        simp [Nat.gcd_zero_right] at hdiv
      · -- gcd 4 1 = 1, 4/1 = 4
        simp at hdiv
      · rfl
      · -- gcd 4 3 = 1, 4/1 = 4
        simp at hdiv
    apply congrArg a
    exact ZMod.val_injective (2 * 2) (by simpa using hval)

/-
Residual of this id (comment, not sorry):
- namesake `IsEmpty (DihedralGroup 4 ≃* QuaternionGroup 2)`
- full classification of groups of order 8
- `QuaternionGroup 2 ≃* (Quaternion ℤ)ˣ`
-/

end ProofLab.D8NeQ8
