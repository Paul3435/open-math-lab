/-
Euclidean-algorithm step counter — Level A only
(zero / self / 2,1 / Fibonacci pair).
**Not labelled Lamé.**

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 has `Nat.fib` / `Nat.gcd` / `gcd_rec` /
`Nat.gcd.induction` / `fib_gcd` and ZERO named Lamé theorem /
`lame_theorem` / `Lame` / `euclidSteps` / `euclid_steps` /
`gcd_steps`. Completing the Level A zero / self / `2,1` /
Fibonacci-pair glue is the gap this ticket lands. The
Level B namesake `lame` (`a ≥ F_{n+2}`, `b ≥ F_{n+1}` after
`n` steps) is **out of this ticket** and is **not** sorry-ed.
Cassini / digit-count extras are residual of this id.

Pin: `catalog/problems/lame-euclid/STATEMENT.md` (OPE-1195;
Scout OPE-1189 leftover; board keep-going after OPE-1194).
Encoding: well-founded step counter on `Nat.mod`, not a new
gcd theory. Zero `sorry`. Do not import `Archive.*`.

This is **not** `Nat.fib_gcd` (`Data/Nat/Fib/Basic.lean` L235:
`fib (gcd m n) = gcd (fib m) (fib n)`) — already Mathlib;
that is the strong-divisibility identity, a different
Fibonacci theorem. **USE `Nat.fib` / `Nat.gcd` / `gcd_rec` as
glue; do not re-prove `fib_gcd`; do not cite as Lamé.**
This is **not** Euclid–Euler even perfect numbers
(`ProofLab/EuclidEulerPerfect.lean`, consumed). Different
Euclid. This is **not** Zeckendorf
(`Data/Nat/Fib/Zeckendorf.lean`, already-in). This is **not**
Binet / `GoldenRatio.lean` (already-in). This is **not**
Cassini / Catalan-Fibonacci. This is **not** Farey (#127) /
Gale–Shapley (#126) / Schur product (OPE-1194 / PR #129).
Do not re-prime the consumed mill. Leave OPE-403 alone.

v1 is the Fibonacci worst-case bound on Euclidean division
steps. Finite `ℕ` is load-bearing. Step-count pin:
`euclidSteps a 0 = 0`; each `%` with `b > 0` counts `+ 1`;
the terminal `b = 0` is **not** an extra step. With this
pin, `gcd(8,5)` takes 4 steps and saturates
`fib (4+2) = fib 6 = 8`.

Level A: `b = 0` is 0 steps. `a = a > 0` gives one step
`a % a = 0`. `2,1` is one step. The pair
`(F_6, F_5) = (8,5)` expands to four mods. **Not** labelled
Lamé.

Transcribed classical argument (G. Lamé, *Note sur la limite
du nombre des divisions dans la recherche du plus grand
commun diviseur*, Comptes rendus 19 (1844) 867–870).
Textbook: Knuth TAOCP vol. 2; Hardy–Wright Fibonacci worst
case. Compact form: Wikipedia *Euclidean algorithm* /
*Lamé's theorem*. Type pin: `Nat.fib` / `euclidSteps` via
`%`. `fib_gcd` is a different already-in theorem.
Euclid–Euler is a different consumed theorem. No novelty
claim. Default no claim.
-/
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

set_option linter.unusedVariables false

namespace ProofLab.LameEuclid

/-! ## Level A: zero / self / 2,1 / Fibonacci pair
(not labelled Lamé) -/

/-- Number of Euclidean division steps. Terminal `b = 0` is
**not** a step. Each `%` with `b > 0` counts `+ 1`.
Well-founded on the second argument via `Nat.mod_lt`.
Encoding; **not** labelled Lamé. Does **not** re-prove
`Nat.gcd` / `gcd_rec` / `fib_gcd`. -/
def euclidSteps (a b : ℕ) : ℕ :=
  if h : b = 0 then 0
  else
    have : a % b < b := Nat.mod_lt a (Nat.pos_of_ne_zero h)
    euclidSteps b (a % b) + 1

/-- Zero remainder: no division step. Glue; **not** labelled
Lamé. -/
theorem euclidSteps_zero (a : ℕ) : euclidSteps a 0 = 0 := by
  simp [euclidSteps]

/-- Recurrence when `b > 0`. Glue; **not** labelled Lamé.
Uses `Nat.mod_lt` (already in the definition); does **not**
re-prove `gcd_rec`. -/
theorem euclidSteps_of_pos (a b : ℕ) (hb : 0 < b) :
    euclidSteps a b = euclidSteps b (a % b) + 1 := by
  nth_rw 1 [euclidSteps]
  simp [hb.ne']

/-- `a = a > 0` is one step (`a % a = 0`). Glue; **not**
labelled Lamé. -/
theorem euclidSteps_self {a : ℕ} (ha : 0 < a) :
    euclidSteps a a = 1 := by
  rw [euclidSteps_of_pos a a ha, Nat.mod_self, euclidSteps_zero]

/-- Pair `2,1`: one step. Glue; **not** labelled Lamé. -/
theorem euclidSteps_two_one : euclidSteps 2 1 = 1 := by
  rw [euclidSteps_of_pos 2 1 (by decide : 0 < 1)]
  simp [euclidSteps_zero]

/-- Mathlib Fibonacci values used by the Level A pair.
Uses `fib_add_two`; does **not** re-prove `Nat.fib`. -/
lemma fib_three : Nat.fib 3 = 2 := by
  simp [Nat.fib_add_two]

lemma fib_four : Nat.fib 4 = 3 := by
  simp [Nat.fib_add_two, fib_three]

lemma fib_five : Nat.fib 5 = 5 := by
  simp [Nat.fib_add_two, fib_three, fib_four]

lemma fib_six : Nat.fib 6 = 8 := by
  simp [Nat.fib_add_two, fib_four, fib_five]

/-- Pair `(F_6, F_5) = (8,5)` takes 4 steps and saturates
`fib (4+2) = fib 6 = 8`. Glue; **not** labelled Lamé. -/
theorem euclidSteps_fib_six_five :
    euclidSteps (Nat.fib 6) (Nat.fib 5) = 4 := by
  rw [fib_six, fib_five]
  have h5 : 0 < 5 := by decide
  have h3 : 0 < 3 := by decide
  have h2 : 0 < 2 := by decide
  have h1 : 0 < 1 := by decide
  rw [euclidSteps_of_pos 8 5 h5]
  -- 8 % 5 = 3
  rw [euclidSteps_of_pos 5 3 h3]
  -- 5 % 3 = 2
  rw [euclidSteps_of_pos 3 2 h2]
  -- 3 % 2 = 1
  rw [euclidSteps_of_pos 2 1 h1, euclidSteps_zero]

/-- Second explicit Fibonacci pair `(F_5, F_4) = (5,3)`
takes 3 steps. Glue; **not** labelled Lamé. -/
theorem euclidSteps_fib_five_four :
    euclidSteps (Nat.fib 5) (Nat.fib 4) = 3 := by
  rw [fib_five, fib_four]
  have h3 : 0 < 3 := by decide
  have h2 : 0 < 2 := by decide
  have h1 : 0 < 1 := by decide
  rw [euclidSteps_of_pos 5 3 h3]
  rw [euclidSteps_of_pos 3 2 h2]
  rw [euclidSteps_of_pos 2 1 h1, euclidSteps_zero]

/-
Residual (Level B, **out of this ticket**, not sorry-ed):
  theorem lame {a b n : ℕ} (hba : b ≤ a) (hb : 0 < b)
      (h : euclidSteps a b = n) :
      Nat.fib (n + 2) ≤ a ∧ Nat.fib (n + 1) ≤ b
Backwards induction: a worst-case predecessor of
`(F_{k+1}, F_k)` is `(F_{k+2}, F_{k+1})`.
Do not sorry the namesake. Cassini / digit-count form
`n ≤ 5 * #decimal digits of b` remain residual of this id.
Do not re-prove `Nat.fib` / `Nat.gcd` / `gcd_rec` /
`Nat.gcd.induction` / `fib_gcd`. Do not prove Cassini /
Zeckendorf / Binet / Euclid–Euler / `schur_product` /
`gale_shapley` / `farey_adjacent`.
-/

end ProofLab.LameEuclid
