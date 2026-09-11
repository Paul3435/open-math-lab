/-
Named factorial-plus-one square witnesses — Level A only
(`4!+1=5²` / `5!+1=11²` / `7!+1=71²`).
**Not labelled Brocard / Ramanujan / Wilson.**

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 pin `a719ba5c3115` has `Nat.factorial` / scoped `n !` /
`factorial_succ` / `pow_two` / `IsSquare` as **infra**. ZERO named
`brocard` / `Brocard` / `brocard_problem` / `factorial_plus_one_square` /
`BrocardRamanujan` theorem under `Mathlib/` or `Archive/` or `ProofLab/`
(this run; NQueens comments mention the leftover id only — not namesake).
Completing the Level A named factorial-plus-one square witnesses is the
gap this ticket lands. The Level B namesake `brocard_factorial_square`
(only `n = 4, 5, 7`; Brocard–Ramanujan) is **OPEN**, **out of this
ticket**, and is **not** sorry-ed. Brocard points / Brocard angle /
Wilson primes are residual of this id. Do **not** label theorems
`wilson_*` / `euclid_*` / `brocard_point_*` / `taxicab_*` as the
namesake. Do **not** define the namesake via uniqueness.

Pin: `catalog/problems/brocard-factorial-square/STATEMENT.md`
(OPE-1429; Scout OPE-1419 leftover HOLD; Director OPE-1428).
Encoding: named factorial-plus-one squares via Mathlib `Nat.factorial`
/ `^ 2`. Zero `sorry`. Do not import `Archive.*`.

This is **not** `Nat.factorial` / `factorial_succ` / `pow_two`
(`Data/Nat/Factorial/Basic.lean`, `Algebra/Group/Defs.lean`) —
already Mathlib. **USE, do not re-prove; do not cite as Brocard.**
This is **not** `wilsons_lemma` (`NumberTheory/Wilson.lean` L38).
Different congruence `(p-1)! ≡ -1 (mod p)`. USE factorial; do **not**
re-prove; do **not** cite as Brocard.
This is **not** `exists_infinite_primes`
(`Data/Nat/Prime/Basic.lean` L82). Different Euclid infinitude whose
proof uses `minFac (n ! + 1)` as a *prime* gadget, **not** a square.
USE factorial; do **not** re-prove; do **not** cite Euclid as Brocard.
This is **not** Brocard points / Brocard angle (geometry name
collision). Do **not** sorry them. Do **not** label theorems
`brocard_point_*`.
This is **not** cannonball (`ProofLab/CannonballSquarePyramid.lean`,
consumed #154). Pyramidal-square ≠ factorial-plus-one square.
This is **not** taxicab-1729 (`ProofLab/Taxicab1729.lean`, consumed
#168). Two-cube sums ≠ factorial squares; Ramanujan's name here is
the Brocard–Ramanujan residual of *this* id, not taxicab.
This is **not** euler-brick (`ProofLab/EulerBrick.lean`, consumed
#169).
This is **not** n-queens (`ProofLab/NQueens.lean`, consumed #174).
Do **not** prove `queens_two_none` / `queens_three_none` /
`queens_four` here.
This is **not** simpson-paradox (#171) / a4-klein-four (#172).
Do not re-prime the consumed mill. Leave OPE-403 alone.
Leave OPE-1195 alone.

v1 is named small factorial-plus-one squares: `4!+1=5²` /
`5!+1=11²` / `7!+1=71²`, **not labelled Brocard / Ramanujan /
Wilson**. Named three-line identities are load-bearing (so Level A
is **not** "some Nats square").

Level A: `brocard_four` / `brocard_five` / `brocard_seven`.
Optional extra: `6!+1=721` is not a square (`brocard_six_not`).
**Not** labelled Brocard / Ramanujan / Wilson.

Transcribed classical argument (Brocard 1876 / Ramanujan). Compact
form: Wikipedia *Brocard's problem*. Type pin: `Nat.factorial` /
`pow_two`. Wilson and Euclid infinitude are different already-in
theorems. n-queens is the consumed prime of this shortlist. No
novelty claim. Default no claim.

Level B namesake OUT of this ticket (do not sorry):
-- theorem brocard_factorial_square ...
--     -- only n = 4, 5, 7 make n!+1 a square (OPEN)
-/
import Mathlib.Tactic

namespace ProofLab.BrocardFactorialSquare

/-! ## Level A: 4!+1=5² / 5!+1=11² / 7!+1=71²
(not labelled Brocard / Ramanujan / Wilson) -/

/-- `4! + 1 = 5²`. Glue: Mathlib `Nat.factorial` / `^ 2`.
Not labelled Brocard / Ramanujan / Wilson. -/
theorem brocard_four : Nat.factorial 4 + 1 = 5 ^ 2 := by
  rfl

/-- `5! + 1 = 11²`. Glue: Mathlib `Nat.factorial` / `^ 2`.
Not labelled Brocard / Ramanujan / Wilson. -/
theorem brocard_five : Nat.factorial 5 + 1 = 11 ^ 2 := by
  rfl

/-- `7! + 1 = 71²`. Glue: Mathlib `Nat.factorial` / `^ 2`.
Not labelled Brocard / Ramanujan / Wilson. -/
theorem brocard_seven : Nat.factorial 7 + 1 = 71 ^ 2 := by
  rfl

/-- Optional extra: `6! + 1 = 721` is not a square.
Glue; **not** labelled Brocard / Ramanujan / Wilson. -/
theorem brocard_six_not : ¬ ∃ k : ℕ, Nat.factorial 6 + 1 = k ^ 2 := by
  rintro ⟨k, hk⟩
  have h721 : Nat.factorial 6 + 1 = 721 := rfl
  rw [h721, pow_two] at hk
  by_cases hle : k ≤ 26
  · have : k * k ≤ 26 * 26 := Nat.mul_le_mul hle hle
    omega
  · have hk27 : 27 ≤ k := Nat.succ_le_of_lt (lt_of_not_ge hle)
    have : 27 * 27 ≤ k * k := Nat.mul_le_mul hk27 hk27
    omega

/-
Residual (Level B, **out of this ticket**, not sorry-ed):
`brocard_factorial_square` — the only positive `n` with `n! + 1` a
square are `n = 4, 5, 7` (Brocard–Ramanujan; **OPEN**). Do **not**
sorry the namesake.
Brocard points / Brocard angle / Wilson primes remain residual of
this id; do **not** expand them as extra namesakes.
Do **not** prove `brocard_factorial_square` namesake uniqueness /
only `n=4,5,7` / Brocard points / Brocard angle / `wilson_*` /
Wilson primes / `euclid_*` / `exists_infinite_primes`
leftover-revivals / n-queens leftover-revivals /
`queens_two_none` / `queens_four` / simpson-paradox
leftover-revivals / a4-klein-four leftover-revivals /
taxicab-1729 / euler-brick / cannonball leftover-revivals /
krenn-gu / hou-zeng-pfc / sun-135.
Leave OPE-403 alone. Leave OPE-1195 alone.
Do **not** label theorems `wilson_*` / `euclid_*` /
`brocard_point_*` / `taxicab_*`.
-/

end ProofLab.BrocardFactorialSquare
