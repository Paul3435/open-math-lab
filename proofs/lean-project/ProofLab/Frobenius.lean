/-
Frobenius coin problem (two denominations) — Level B formalization.

status: informal-to-computational
- `representable` is defined via a *computable* boolean decision procedure
  (bounded search x,y in [0, n]), so it carries a real `Decidable` instance and
  small certificate examples close with `native_decide` (sorry-free).
- The bounded search is equivalent to the unbounded a*x+b*y existential whenever
  a, b >= 1 (x > n forces a*x > n).
- Small sorry-free certificate examples match the Level A Python certificate.
- The full general theorem (forall n > ab-a-b, representable) is NOT yet
  Lean-checked; it remains a goal (Level C, optional).

Definition source: catalog/problems/frobenius-coin-problem/STATEMENT.md
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Nat.Defs
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic

namespace ProofLab.Frobenius

/-! ## Main definitions -/

/-- Decidable (boolean) decision procedure: is `n` representable as a*x + b*y
with x, y in [0, n]? Bounded search — exact when a,b >= 1. -/
def representableBool (a b n : ℕ) : Bool :=
  (List.range (n + 1)).any
    (fun x => (List.range (n + 1)).any (fun y => n == a * x + b * y))

/-- `n` is representable as a non-negative combination of `a` and `b`.
Prop version backed by the computable decision procedure. -/
abbrev representable (a b n : ℕ) : Prop :=
  representableBool a b n = true

/-- The claimed Frobenius number for two denominations: g(a,b) = ab - a - b. -/
def frobenius_number (a b : ℕ) : ℕ :=
  a * b - a - b

/-! ## Level B certificate: sorry-free small examples

For each coprime pair we machine-check with `native_decide` (sorry-free, real
`Decidable` instances):
  1. the claimed Frobenius value equals a*b - a - b,
  2. that value (and selected smaller gaps) is NOT representable,
  3. a finite window just above it IS fully representable — the machine-checked
     "tail covering" that the Chicken-McNugget argument uses before closing the
     tail by eventual periodicity (closure under +a and +b).
-/

-- (3,5): g = 15-3-5 = 7
example : frobenius_number 3 5 = 7 := by decide
example : frobenius_number 3 5 = 3 * 5 - 3 - 5 := by decide
example : ¬ representable 3 5 (frobenius_number 3 5) := by decide
example : ¬ representable 3 5 7 := by decide
example : ¬ representable 3 5 4 := by decide
example : ¬ representable 3 5 1 := by decide
example : ¬ representable 3 5 2 := by decide
example : representable 3 5 8 := by decide
example : representable 3 5 9 := by decide
example : representable 3 5 10 := by decide
example : representable 3 5 15 := by decide
-- every n in (7, 15] representable (finite tail covering window)
example : ∀ n ∈ Finset.Icc 8 15, representable 3 5 n := by decide

-- (2,3): g = 6-2-3 = 1
example : frobenius_number 2 3 = 1 := by decide
example : ¬ representable 2 3 (frobenius_number 2 3) := by decide
example : ¬ representable 2 3 1 := by decide
example : representable 2 3 2 := by decide
example : representable 2 3 3 := by decide
example : ∀ n ∈ Finset.Icc 2 6, representable 2 3 n := by decide

-- (3,4): g = 12-3-4 = 5
example : frobenius_number 3 4 = 5 := by decide
example : ¬ representable 3 4 (frobenius_number 3 4) := by decide
example : ¬ representable 3 4 5 := by decide
example : ¬ representable 3 4 1 := by decide
example : ¬ representable 3 4 2 := by decide
example : representable 3 4 6 := by decide
example : representable 3 4 7 := by decide
example : representable 3 4 8 := by decide
example : ∀ n ∈ Finset.Icc 6 12, representable 3 4 n := by decide

-- (2,5): g = 10-2-5 = 3
example : frobenius_number 2 5 = 3 := by decide
example : ¬ representable 2 5 (frobenius_number 2 5) := by decide
example : ¬ representable 2 5 3 := by decide
example : ¬ representable 2 5 1 := by decide
example : representable 2 5 4 := by decide
example : representable 2 5 5 := by decide
example : ∀ n ∈ Finset.Icc 4 10, representable 2 5 n := by decide

-- (4,5): g = 20-4-5 = 11
example : frobenius_number 4 5 = 11 := by decide
example : ¬ representable 4 5 (frobenius_number 4 5) := by decide
example : ¬ representable 4 5 11 := by decide
example : ¬ representable 4 5 6 := by decide
example : representable 4 5 12 := by decide
example : representable 4 5 15 := by decide
example : representable 4 5 20 := by decide
example : ∀ n ∈ Finset.Icc 12 20, representable 4 5 n := by decide

-- (2,7): g = 14-2-7 = 5
example : frobenius_number 2 7 = 5 := by decide
example : ¬ representable 2 7 (frobenius_number 2 7) := by decide
example : representable 2 7 6 := by decide
example : representable 2 7 7 := by decide
example : ∀ n ∈ Finset.Icc 6 14, representable 2 7 n := by decide

-- (3,7): g = 21-3-7 = 11
example : frobenius_number 3 7 = 11 := by decide
example : ¬ representable 3 7 (frobenius_number 3 7) := by decide
example : ¬ representable 3 7 11 := by decide
example : ¬ representable 3 7 5 := by decide
example : representable 3 7 12 := by decide
example : representable 3 7 13 := by decide
example : representable 3 7 21 := by decide
example : ∀ n ∈ Finset.Icc 12 21, representable 3 7 n := by decide

/-! ## Level C goal (optional; not yet proved)

The full two-direction theorem for arbitrary coprime a, b. Intentionally left as
a goal so the Formalist / a future specialist can formalize it. The finite
certificate pieces above already machine-check, sorry-free, the instance-level
versions of both directions on sample pairs.
-/
-- Direction 1 + 2 (general): left open.
#check Nat.Coprime

end ProofLab.Frobenius
