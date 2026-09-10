/-
Named small-n three-square witnesses — Level A only
(`1 = 1²+0²+0²` / `2 = 1²+1²+0²` / `3 = 1²+1²+1²` / `7` is not).
**Not labelled Legendre.**

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 pin `a719ba5c3115` has `Nat` / `^ 2` / `IsSquare`
as **infra**. ZERO named three-square / `three_square` /
`threeSquare` / `ThreeSquare` / `sum_three_squares` /
`sumThreeSquares` / `isSumOfThreeSquares` / `LegendreThree` /
`legendre_three` under `Mathlib/` or `Archive/` or `ProofLab/`.
Completing the Level A named small-n witnesses is the gap this
ticket lands. The Level B namesake `legendre_three_squares`
(every `n` not of the form `4^a(8b+7)`) is **out of this ticket**
and is **not** sorry-ed. Gauss Eureka / three triangular numbers
are residual of this id.

Pin: `catalog/problems/legendre-three-squares/STATEMENT.md`
(OPE-1347; Scout OPE-1342 RECOMMENDED PRIME; Director OPE-1346).
Encoding: `IsSumThreeSquares` via Mathlib `Nat` squares. Zero
`sorry`. Do not import `Archive.*`.
Do **not** label theorems `legendre_*` (Legendre-symbol /
`euler_criterion` already-in name collision).

This is **not** `Nat` / `^ 2` / `IsSquare` — already Mathlib.
**USE, do not re-prove; do not cite as three-square.**
This is **not** `Nat.sum_four_squares`
(`NumberTheory/SumFourSquares.lean` L212) — DIFFERENT already-in
four-square theorem (every `n`, four squares). Do **not** re-prove;
do **not** cite as three-square; do **not** define this namesake
via four-square.
This is **not** `Nat.Prime.sq_add_sq`
(`NumberTheory/SumTwoSquares.lean` L31) — DIFFERENT already-in
two-square theorem. Do **not** re-prove; do **not** cite as
three-square.
This is **not** cannonball square-pyramid
(`ProofLab/CannonballSquarePyramid.lean`, consumed #154).
Pyramidal = square ≠ three squares. Do **not** revive Lucas
uniqueness / Watson / `Nat.sum_four_squares` as namesake.
This is **not** Jordan canonical form
(`ProofLab/JordanCanonicalForm.lean`, consumed #156).
This is **not** orthogonal Latin squares
(`ProofLab/OrthogonalLatinSquares.lean`, consumed #157).
This is **not** Alcuin integer triangles
(`ProofLab/AlcuinIntegerTriangles.lean`, consumed #153).
This is **not** langford-pairing (OPE-1342 leftover; unassigned
this tick). Do **not** prove Langford / Skolem here.
Do not re-prime the consumed mill. Leave OPE-403 alone.
Leave OPE-1195 alone.

v1 is named small-n three-square witnesses:
`1 = 1²+0²+0²`, `2 = 1²+1²+0²`, `3 = 1²+1²+1²`, and `7` is not
a sum of three squares, **not labelled Legendre**. Nonneg integer
squares (zeros allowed) are load-bearing. `¬ IsSumThreeSquares 7`
is load-bearing (so Level A is **not** "some numbers are three
squares").

Level A: `1` / `2` / `3` yes and `7` no. Optional extra: `6` yes
/ `15` no. **Not** labelled Legendre.

Transcribed classical argument (Adrien-Marie Legendre 1797/98;
small-n exhaustive `0²..2²` for the `7` obstruction). Compact
form: Wikipedia *Legendre's three-square theorem*. Type pin:
`IsSumThreeSquares` / `Nat` squares. Four-square
`Nat.sum_four_squares` is a different already-in theorem.
Two-square `Nat.Prime.sq_add_sq` is a different already-in
theorem. No novelty claim. Default no claim.
-/
import Mathlib.Tactic

set_option linter.unusedVariables false

namespace ProofLab.LegendreThreeSquares

/-! ## Encoding: three nonnegative squares (not labelled Legendre) -/

/-- `n` is a sum of three nonnegative integer squares (zeros
allowed). Encoding; **not** labelled Legendre. Does **not**
re-prove `Nat` / `^ 2` / `IsSquare` / `Nat.sum_four_squares` /
`Nat.Prime.sq_add_sq`. -/
def IsSumThreeSquares (n : ℕ) : Prop :=
  ∃ a b c : ℕ, a ^ 2 + b ^ 2 + c ^ 2 = n

/-! ## Level A: named small-n witnesses (not labelled Legendre) -/

/-- `1 = 1² + 0² + 0²`. Glue; **not** labelled Legendre. -/
theorem three_squares_one : IsSumThreeSquares 1 :=
  ⟨1, 0, 0, by simp [Nat.pow_two]⟩

/-- `2 = 1² + 1² + 0²`. Glue; **not** labelled Legendre. -/
theorem three_squares_two : IsSumThreeSquares 2 :=
  ⟨1, 1, 0, by simp [Nat.pow_two]⟩

/-- `3 = 1² + 1² + 1²`. Glue; **not** labelled Legendre. -/
theorem three_squares_three : IsSumThreeSquares 3 :=
  ⟨1, 1, 1, by simp [Nat.pow_two]⟩

lemma three_sq_bounds {a b c n : ℕ}
    (h : a ^ 2 + b ^ 2 + c ^ 2 = n) :
    a ^ 2 ≤ n ∧ b ^ 2 ≤ n ∧ c ^ 2 ≤ n := by
  refine ⟨?ha, ?hb, ?hc⟩
  · have h1 : a ^ 2 ≤ a ^ 2 + b ^ 2 := Nat.le_add_right _ _
    have h2 : a ^ 2 + b ^ 2 ≤ a ^ 2 + b ^ 2 + c ^ 2 := Nat.le_add_right _ _
    have : a ^ 2 ≤ a ^ 2 + b ^ 2 + c ^ 2 := le_trans h1 h2
    rwa [h] at this
  · have h1 : b ^ 2 ≤ a ^ 2 + b ^ 2 := Nat.le_add_left _ _
    have h2 : a ^ 2 + b ^ 2 ≤ a ^ 2 + b ^ 2 + c ^ 2 := Nat.le_add_right _ _
    have : b ^ 2 ≤ a ^ 2 + b ^ 2 + c ^ 2 := le_trans h1 h2
    rwa [h] at this
  · have : c ^ 2 ≤ a ^ 2 + b ^ 2 + c ^ 2 := Nat.le_add_left _ _
    rwa [h] at this

lemma le_two_of_sq_le_seven {a : ℕ} (h : a ^ 2 ≤ 7) : a ≤ 2 := by
  by_contra hgt
  have ha3 : 3 ≤ a := Nat.succ_le_of_lt (lt_of_not_ge hgt)
  have : 9 ≤ a * a := Nat.mul_le_mul ha3 ha3
  have hsq : a ^ 2 = a * a := Nat.pow_two a
  omega

/-- `7` is not a sum of three nonnegative squares.
Load-bearing; **not** labelled Legendre. Exhaustive `0²..2²`. -/
theorem three_squares_seven_not : ¬ IsSumThreeSquares 7 := by
  rintro ⟨a, b, c, h⟩
  obtain ⟨ha2, hb2, hc2⟩ := three_sq_bounds h
  have ha : a ≤ 2 := le_two_of_sq_le_seven ha2
  have hb : b ≤ 2 := le_two_of_sq_le_seven hb2
  have hc : c ≤ 2 := le_two_of_sq_le_seven hc2
  interval_cases a <;> interval_cases b <;> interval_cases c <;> cases h

/-- Optional extra: `6 = 2² + 1² + 1²`. Glue; **not** labelled
Legendre. -/
theorem three_squares_six : IsSumThreeSquares 6 :=
  ⟨2, 1, 1, by simp [Nat.pow_two]⟩

lemma le_three_of_sq_le_fifteen {a : ℕ} (h : a ^ 2 ≤ 15) : a ≤ 3 := by
  by_contra hgt
  have ha4 : 4 ≤ a := Nat.succ_le_of_lt (lt_of_not_ge hgt)
  have : 16 ≤ a * a := Nat.mul_le_mul ha4 ha4
  have hsq : a ^ 2 = a * a := Nat.pow_two a
  omega

/-- Optional extra: `15` is not a sum of three nonnegative squares.
Glue; **not** labelled Legendre. Exhaustive `0²..3²`. -/
theorem three_squares_fifteen_not : ¬ IsSumThreeSquares 15 := by
  rintro ⟨a, b, c, h⟩
  obtain ⟨ha2, hb2, hc2⟩ := three_sq_bounds h
  have ha : a ≤ 3 := le_three_of_sq_le_fifteen ha2
  have hb : b ≤ 3 := le_three_of_sq_le_fifteen hb2
  have hc : c ≤ 3 := le_three_of_sq_le_fifteen hc2
  interval_cases a <;> interval_cases b <;> interval_cases c <;> cases h

/-
Residual (Level B, **out of this ticket**, not sorry-ed):
`legendre_three_squares` — every natural number is a sum of three
integer squares iff it is not of the form `4^a (8b + 7)`
(Legendre 1797/98). Do **not** sorry the namesake. Do **not**
label theorems `legendre_*`. Gauss Eureka / three triangular
numbers remain residual of this id; do **not** expand them as
extra namesakes.
Do **not** prove `Nat.sum_four_squares` as namesake /
`Nat.Prime.sq_add_sq` as namesake / `IsSquare` as namesake /
Gauss Eureka / three triangular numbers / langford-pairing /
Skolem sequences / jordan-canonical-form /
`aeval_self_charpoly` as namesake /
`exists_isNilpotent_isSemisimple` as namesake / `IsJordan` as
namesake / orthogonal-latin-squares / `ProjectivePlane` as
namesake / `Equiv.Perm` as namesake / alcuin-integer-triangles /
integerTriangle / Heron leftover-revivals /
cannonball-square-pyramid / Lucas uniqueness / Watson / Faulhaber.
Leave OPE-403 alone. Leave OPE-1195 alone.
Do **not** label theorems `legendre_*`.
-/

end ProofLab.LegendreThreeSquares
