/-
Reduced fractions of bounded denominator — Level A only
(F_1 two-term adjacency / mediant of 0/1 and 1/1 / F_2 three-term list).
**Not labelled Farey.**

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 has `Nat.Coprime` / `Nat.totient` /
`totient_eq_card_coprime` / Rat coprime-pair encoding
(`Data/Rat/Denumerable.lean`) and ZERO named Farey /
`fareySequence` / `IsFarey` / `fareyAdjacent`. Completing the
Level A F_1 / mediant / F_2 glue is the gap this ticket lands.
The Level B namesake `farey_adjacent` (adjacent ⇒ bc − ad = 1)
is **out of this ticket** and is **not** sorry-ed. Count
`|F_n| = 1 + ∑_{k≤n} φ(k)` / Stern–Brocot / Calkin–Wilf /
Ford circles extras are residual of this id.

Pin: `catalog/problems/farey-sequence/STATEMENT.md` (OPE-1184;
Scout OPE-1173 leftover; Director OPE-1183). Encoding: coprime
pairs (`Nat.Coprime`), not a new `Rat` theory. Zero `sorry`.
Do not import `Archive.*`.

This is **not** `Nat.sum_totient` (`n.divisors.sum φ = n`,
Totient.lean L153) — already Mathlib; that is a different
totient identity. **USE `Nat.Coprime` as glue; do not re-prove
`sum_totient` / `totient_eq_card_coprime`; do not cite as Farey.**
This is **not** Pick's theorem (no lattice-polygon area infra).
This is **not** Stern–Brocot / Calkin–Wilf / Ford circles.
This is **not** Gale–Shapley (`ProofLab/GaleShapley.lean`, #126).
This is **not** Birkhoff–von Neumann (#123) / Nash–Williams
arboricity (#124) / Singleton (#120) / hook-length (#121) /
Cauchy–Binet (#117) / Bollobás (#118). Do not re-prime the
consumed mill. Leave OPE-403 alone.

v1 of the catalog id is adjacency-determinant on reduced
fractions of order `n`. Finite `n` is load-bearing. Reduced
(`Nat.Coprime`) is load-bearing. The interval is `[0,1]`
(nonnegative numerators).

Level A: order 1 is `{0/1, 1/1}` adjacent with det 1. The
mediant is `(0+1)/(1+1) = 1/2`, strictly between, and is the
unique new term of order 2. **Not** labelled Farey.

Transcribed classical argument (J. Farey, *On a curious
property of vulgar fractions*, Phil. Mag. 47 (1816) 385–386;
A.-L. Cauchy, *Démonstration d'un théorème sur les nombres*,
Bulletin de la Société Philomathique (1816) 133–135).
Textbook: Hardy–Wright, *An Introduction to the Theory of
Numbers*, Ch. III. Compact form: Wikipedia *Farey sequence*.
Type pin: `Nat.Coprime` / coprime pairs. `sum_totient` is a
different already-in theorem. No novelty claim. Default no claim.
-/
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic

set_option linter.unusedVariables false

namespace ProofLab.FareySequence

/-! ## Encoding: coprime pairs of bounded denominator (not labelled Farey) -/

/-- A reduced fraction `num/den` in `[0,1]` with `den ≤ n`.
Finite `n` and `Nat.Coprime` are load-bearing. Encoding;
**not** labelled Farey. Reuses Mathlib `Nat.Coprime`; does
**not** re-prove `sum_totient` / `totient_eq_card_coprime`. -/
structure FareyFrac (n : ℕ) where
  num : ℕ
  den : ℕ
  den_pos : 0 < den
  den_le : den ≤ n
  num_le : num ≤ den
  coprime : Nat.Coprime num den

/-- Cross-multiplication order `x < y` as rationals.
Encoding; **not** labelled Farey. -/
def FareyLt {n : ℕ} (x y : FareyFrac n) : Prop :=
  x.num * y.den < y.num * x.den

instance {n : ℕ} (x y : FareyFrac n) : Decidable (FareyLt x y) :=
  inferInstanceAs (Decidable (x.num * y.den < y.num * x.den))

/-- No reduced fraction of order `n` lies strictly between `x` and `y`.
Encoding; **not** labelled Farey. -/
def Adjacent {n : ℕ} (x y : FareyFrac n) : Prop :=
  FareyLt x y ∧ ∀ z : FareyFrac n, ¬ (FareyLt x z ∧ FareyLt z y)

/-- Numerator of the mediant `(x.num + y.num)/(x.den + y.den)`.
Glue; **not** labelled Farey. Not a Stern–Brocot tree. -/
def mediantNum {n : ℕ} (x y : FareyFrac n) : ℕ :=
  x.num + y.num

/-- Denominator of the mediant. Glue; **not** labelled Farey. -/
def mediantDen {n : ℕ} (x y : FareyFrac n) : ℕ :=
  x.den + y.den

/-- Lift a reduced fraction of order `n` to any larger order.
Glue; **not** labelled Farey. -/
def ofLe {n m : ℕ} (h : n ≤ m) (x : FareyFrac n) : FareyFrac m where
  num := x.num
  den := x.den
  den_pos := x.den_pos
  den_le := le_trans x.den_le h
  num_le := x.num_le
  coprime := x.coprime

/-! ## Level A: F_1 = {0/1, 1/1} (not labelled Farey) -/

/-- The fraction `0/1` of order 1. Glue; **not** labelled Farey. -/
def zeroOverOne : FareyFrac 1 where
  num := 0
  den := 1
  den_pos := by decide
  den_le := by decide
  num_le := by decide
  coprime := Nat.coprime_one_right 0

/-- The fraction `1/1` of order 1. Glue; **not** labelled Farey. -/
def oneOverOne : FareyFrac 1 where
  num := 1
  den := 1
  den_pos := by decide
  den_le := by decide
  num_le := by decide
  coprime := Nat.coprime_one_right 1

/-- Every reduced fraction of order 1 is `0/1` or `1/1`.
Glue; **not** labelled Farey. -/
theorem mem_order_one (z : FareyFrac 1) :
    z.num = 0 ∧ z.den = 1 ∨ z.num = 1 ∧ z.den = 1 := by
  have hden : z.den = 1 := by
    have := z.den_pos
    have := z.den_le
    omega
  have hnum : z.num = 0 ∨ z.num = 1 := by
    have := z.num_le
    omega
  rcases hnum with hnum | hnum
  · exact Or.inl ⟨hnum, hden⟩
  · exact Or.inr ⟨hnum, hden⟩

/-- `0/1 < 1/1` under cross-multiplication. Glue; **not** labelled Farey. -/
theorem lt_zero_one_order_one : FareyLt zeroOverOne oneOverOne := by
  decide

/-- Order 1 is two adjacent terms. Glue; **not** labelled Farey. -/
theorem adjacent_zero_one_order_one : Adjacent zeroOverOne oneOverOne := by
  refine ⟨lt_zero_one_order_one, ?_⟩
  intro z h
  rcases mem_order_one z with ⟨hn, hd⟩ | ⟨hn, hd⟩
  · have : (0 : ℕ) < z.num := by
      simpa [FareyLt, zeroOverOne] using h.1
    omega
  · have : z.num < z.den := by
      simpa [FareyLt, oneOverOne] using h.2
    omega

/-- Adjacent pair of order 1 has determinant 1: `1·1 − 0·1 = 1`.
Glue; **not** labelled Farey. Not the Level B namesake. -/
theorem det_zero_one_order_one :
    oneOverOne.num * zeroOverOne.den - zeroOverOne.num * oneOverOne.den = 1 := by
  decide

/-! ## Level A: mediant of 0/1 and 1/1 is 1/2 (not labelled Farey) -/

/-- Mediant numerator of `0/1` and `1/1` is `1`. Glue; **not** labelled Farey. -/
theorem mediantNum_zero_one : mediantNum zeroOverOne oneOverOne = 1 := by
  decide

/-- Mediant denominator of `0/1` and `1/1` is `2`. Glue; **not** labelled Farey. -/
theorem mediantDen_zero_one : mediantDen zeroOverOne oneOverOne = 2 := by
  decide

/-- The fraction `1/2` of order 2 (the mediant). Glue; **not** labelled Farey. -/
def oneOverTwo : FareyFrac 2 where
  num := 1
  den := 2
  den_pos := by decide
  den_le := by decide
  num_le := by decide
  coprime := Nat.coprime_one_left 2

/-- `0/1` of order 2. Glue; **not** labelled Farey. -/
def zeroOverOneTwo : FareyFrac 2 :=
  ofLe (by decide : 1 ≤ 2) zeroOverOne

/-- `1/1` of order 2. Glue; **not** labelled Farey. -/
def oneOverOneTwo : FareyFrac 2 :=
  ofLe (by decide : 1 ≤ 2) oneOverOne

/-- The order-2 term `1/2` is the mediant of `0/1` and `1/1`.
Glue; **not** labelled Farey. Not a Stern–Brocot tree. -/
theorem oneOverTwo_eq_mediant :
    oneOverTwo.num = mediantNum zeroOverOne oneOverOne ∧
      oneOverTwo.den = mediantDen zeroOverOne oneOverOne := by
  exact ⟨mediantNum_zero_one.symm, mediantDen_zero_one.symm⟩

/-- `0/1 < 1/2` under cross-multiplication. Glue; **not** labelled Farey. -/
theorem lt_zero_half_order_two : FareyLt zeroOverOneTwo oneOverTwo := by
  decide

/-- `1/2 < 1/1` under cross-multiplication. Glue; **not** labelled Farey. -/
theorem lt_half_one_order_two : FareyLt oneOverTwo oneOverOneTwo := by
  decide

/-! ## Level A: F_2 = {0/1, 1/2, 1/1} (not labelled Farey) -/

/-- `0/2` is not reduced. Glue; **not** labelled Farey. Uses Mathlib
`Nat.Coprime`; does not re-prove totient identities. -/
theorem not_coprime_zero_two : ¬ Nat.Coprime 0 2 := by
  decide

/-- `2/2` is not reduced. Glue; **not** labelled Farey. -/
theorem not_coprime_two_two : ¬ Nat.Coprime 2 2 := by
  decide

/-- Every reduced fraction of order 2 is `0/1`, `1/2`, or `1/1`.
The unique new term versus order 1 is the mediant `1/2`.
Glue; **not** labelled Farey. -/
theorem mem_order_two (z : FareyFrac 2) :
    z.num = 0 ∧ z.den = 1 ∨
      z.num = 1 ∧ z.den = 2 ∨
      z.num = 1 ∧ z.den = 1 := by
  have hden : z.den = 1 ∨ z.den = 2 := by
    have := z.den_pos
    have := z.den_le
    omega
  rcases hden with hden | hden
  · have hnum : z.num = 0 ∨ z.num = 1 := by
      have := z.num_le
      omega
    rcases hnum with hnum | hnum
    · exact Or.inl ⟨hnum, hden⟩
    · exact Or.inr (Or.inr ⟨hnum, hden⟩)
  · have hnum : z.num = 0 ∨ z.num = 1 ∨ z.num = 2 := by
      have := z.num_le
      omega
    rcases hnum with hnum | hnum | hnum
    · exact False.elim (not_coprime_zero_two (by simpa [hnum, hden] using z.coprime))
    · exact Or.inr (Or.inl ⟨hnum, hden⟩)
    · exact False.elim (not_coprime_two_two (by simpa [hnum, hden] using z.coprime))

/-- The unique order-2 term that is not already in order 1 is `1/2`.
Glue; **not** labelled Farey. -/
theorem unique_new_order_two (z : FareyFrac 2)
    (h0 : ¬ (z.num = 0 ∧ z.den = 1))
    (h1 : ¬ (z.num = 1 ∧ z.den = 1)) :
    z.num = 1 ∧ z.den = 2 := by
  rcases mem_order_two z with h | h | h
  · exact False.elim (h0 h)
  · exact h
  · exact False.elim (h1 h)

/-- `0/1` and `1/2` are adjacent in order 2. Glue; **not** labelled Farey. -/
theorem adjacent_zero_half_order_two : Adjacent zeroOverOneTwo oneOverTwo := by
  refine ⟨lt_zero_half_order_two, ?_⟩
  intro z h
  rcases mem_order_two z with ⟨hn, hd⟩ | ⟨hn, hd⟩ | ⟨hn, hd⟩
  · -- z = 0/1: not strictly after 0/1
    have : (0 : ℕ) < z.num := by
      simpa [FareyLt, zeroOverOneTwo, ofLe, zeroOverOne] using h.1
    omega
  · -- z = 1/2: not strictly before 1/2
    have : z.num * 2 < 1 * z.den := by
      simpa [FareyLt, oneOverTwo] using h.2
    omega
  · -- z = 1/1: not strictly before 1/2
    have : z.num * 2 < 1 * z.den := by
      simpa [FareyLt, oneOverTwo] using h.2
    omega

/-- `1/2` and `1/1` are adjacent in order 2. Glue; **not** labelled Farey. -/
theorem adjacent_half_one_order_two : Adjacent oneOverTwo oneOverOneTwo := by
  refine ⟨lt_half_one_order_two, ?_⟩
  intro z h
  rcases mem_order_two z with ⟨hn, hd⟩ | ⟨hn, hd⟩ | ⟨hn, hd⟩
  · -- z = 0/1: not strictly after 1/2
    have : (1 : ℕ) * z.den < z.num * 2 := by
      simpa [FareyLt, oneOverTwo] using h.1
    omega
  · -- z = 1/2: not strictly after 1/2
    have : (1 : ℕ) * z.den < z.num * 2 := by
      simpa [FareyLt, oneOverTwo] using h.1
    omega
  · -- z = 1/1: not strictly before 1/1
    have : z.num < z.den := by
      simpa [FareyLt, oneOverOneTwo, ofLe, oneOverOne] using h.2
    omega

/-- Adjacent pair `0/1`, `1/2` of order 2 has determinant 1.
Glue; **not** labelled Farey. Not the Level B namesake. -/
theorem det_zero_half_order_two :
    oneOverTwo.num * zeroOverOneTwo.den -
      zeroOverOneTwo.num * oneOverTwo.den = 1 := by
  decide

/-- Adjacent pair `1/2`, `1/1` of order 2 has determinant 1.
Glue; **not** labelled Farey. Not the Level B namesake. -/
theorem det_half_one_order_two :
    oneOverOneTwo.num * oneOverTwo.den -
      oneOverTwo.num * oneOverOneTwo.den = 1 := by
  decide

/-
Residual (Level B, **out of this ticket**, not sorry-ed):
  theorem farey_adjacent {n : ℕ}
      (x y : FareyFrac n) (h : Adjacent x y) :
      y.num * x.den - x.num * y.den = 1
If `a/b < c/d` are adjacent in order `n` and `bc − ad = k > 1`,
the mediant `(a+c)/(b+d)` would sit strictly between them once
its denominator is `≤ n`, contradicting adjacency; equivalently,
adjacent reduced fractions are unimodular SL(2,ℤ) pairs.
Do not sorry the namesake. Count `|F_n| = 1 + ∑_{k≤n} φ(k)` /
Stern–Brocot / Calkin–Wilf / Ford circles / Pick remain residual
of this id. Do not re-prove `sum_totient` / `totient_eq_card_coprime`
/ gale_shapley / rural hospitals / Hall / Gale–Ryser /
birkhoff_von_neumann / nash_williams.
-/

end ProofLab.FareySequence
