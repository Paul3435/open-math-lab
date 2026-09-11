/-
Named two-cube witnesses — Level A only
(`1³ + 12³ = 1729` / `9³ + 10³ = 1729` / equality).
**Not labelled Hardy / Ramanujan / taxicab.**

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 pin `a719ba5c3115` has `Nat` / `HPow` / `^` /
`pow_two` / `pow_three` as **infra**. ZERO named `taxicab` /
`Taxicab` / `hardyRamanujan` / `HardyRamanujan` theorem under
`Mathlib/` or `Archive/` or `ProofLab/` (this run; Dual.lean URL
fragment 172988 only — not namesake). Completing the Level A
named two-cube witnesses is the gap this ticket lands. The
Level B namesake `taxicab_1729` (1729 is the smallest such `n`)
is **out of this ticket** and is **not** sorry-ed. Second
taxicab 4104 / signed cubes / 91 extras are residual of this
id. Do **not** label theorems `taxicab_1729` / `hardy_*` /
`ramanujan_*` / `fermat_*` / `flt_*` / `sq_add_sq_*` as the
namesake. Do **not** define the namesake via smallest-n
uniqueness.

Pin: `catalog/problems/taxicab-1729/STATEMENT.md`
(OPE-1395; Scout OPE-1390 RECOMMENDED PRIME; Director OPE-1394).
Encoding: named two-cube witnesses via Mathlib `Nat` / `^ 3`.
Zero `sorry`. Do not import `Archive.*`.

This is **not** `Nat` / `HPow` / `^` / `pow_two` / `pow_three`
(`Algebra/Group/Defs.lean`) — already Mathlib.
**USE, do not re-prove; do not cite as this two-ways sum.**
This is **not** `fermatLastTheoremThree` (`FLT/Three.lean` L725).
Different equation `a³+b³ ≠ c³`. USE `^ 3`; do **not** re-prove;
do **not** cite as this two-ways sum.
This is **not** `Nat.Prime.sq_add_sq` — already-in two-square.
This is **not** four-square / three-square
(`ProofLab/LegendreThreeSquares.lean`, consumed #159).
This is **not** cannonball
(`ProofLab/CannonballSquarePyramid.lean`, consumed #154).
This is **not** ℤ[√-5] not UFD
(`ProofLab/Zsqrt5NotUfd.lean`, consumed #165).
This is **not** D8 ≇ Q8 (`ProofLab/D8NeQ8.lean`, consumed #166).
This is **not** euler-brick (leftover of this shortlist).
Do not re-prime the consumed mill. Leave OPE-403 alone.
Leave OPE-1195 alone.

v1 is named two-cube witnesses: `1³+12³ = 1729` and
`9³+10³ = 1729` and they are equal, **not labelled Hardy /
Ramanujan / taxicab**. Named pairs are load-bearing (so
Level A is **not** "some Nats have cubes").

Level A: `cubes_one_twelve` / `cubes_nine_ten` / `two_ways`.
Optional extra: unordered pairs distinct (`{1,12} ≠ {9,10}`).
**Not** labelled Hardy / Ramanujan / taxicab.

Transcribed classical argument (Hardy–Ramanujan number /
Ta(2)=1729). Compact form: Wikipedia *1729 (number)* /
*Taxicab number*. Type pin: `Nat` / `^ 3`. FLT n=3 is a
different already-in equation. Two-square is a different
already-in theorem. Euler brick is the leftover of this
shortlist. No novelty claim. Default no claim.

Level B namesake OUT of this ticket (do not sorry):
-- theorem taxicab_1729 {n a b c d : ℕ}
--     (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
--     (hpair : ({a, b} : Set ℕ) ≠ {c, d})
--     (h : a ^ 3 + b ^ 3 = n ∧ c ^ 3 + d ^ 3 = n) :
--     1729 ≤ n
-/
import Mathlib.Tactic

namespace ProofLab.Taxicab1729

/-! ## Level A: 1³+12³ = 1729 = 9³+10³
(not labelled Hardy / Ramanujan / taxicab) -/

/-- `1³ + 12³ = 1729`. Glue: Mathlib `Nat` / `^ 3`.
Not labelled Hardy / Ramanujan / taxicab. -/
theorem cubes_one_twelve : (1 : ℕ) ^ 3 + 12 ^ 3 = 1729 := by
  rfl

/-- `9³ + 10³ = 1729`. Glue: Mathlib `Nat` / `^ 3`.
Not labelled Hardy / Ramanujan / taxicab. -/
theorem cubes_nine_ten : (9 : ℕ) ^ 3 + 10 ^ 3 = 1729 := by
  rfl

/-- The two named pairs sum to the same value.
Glue; **not** labelled Hardy / Ramanujan / taxicab. -/
theorem two_ways : (1 : ℕ) ^ 3 + 12 ^ 3 = 9 ^ 3 + 10 ^ 3 :=
  cubes_one_twelve.trans cubes_nine_ten.symm

/-- Optional extra: the pairs are distinct as unordered pairs.
Glue; **not** labelled Hardy / Ramanujan / taxicab. -/
theorem pairs_distinct : ({(1 : ℕ), 12} : Set ℕ) ≠ {9, 10} := by
  intro h
  have h1 : (1 : ℕ) ∈ ({(1 : ℕ), 12} : Set ℕ) := by simp
  have : (1 : ℕ) ∈ ({9, 10} : Set ℕ) := h ▸ h1
  simp at this

/-
Residual (Level B, **out of this ticket**, not sorry-ed):
`taxicab_1729` — 1729 is the smallest positive `n` that is a
sum of two positive cubes in two essentially different
unordered ways. Do **not** sorry the namesake.
Second taxicab 4104 / signed cubes / 91 remain residual of
this id; do **not** expand them as extra namesakes.
Do **not** prove `fermatLastTheoremThree` as namesake /
`Nat.Prime.sq_add_sq` as namesake / `Nat.sum_four_squares`
as namesake / cannonball leftover-revivals / euler-brick /
44-117-240 brick / perfect cuboid / zsqrt5-not-ufd
leftover-revivals / UniqueFactorizationMonoid / d8-ne-q8
leftover-revivals / `DihedralGroup 4 ≃* QuaternionGroup 2`.
Leave OPE-403 alone. Leave OPE-1195 alone.
Do **not** label theorems `taxicab_1729` / `hardy_*` /
`ramanujan_*` / `fermat_*` / `flt_*` / `sq_add_sq_*`.
-/

end ProofLab.Taxicab1729
