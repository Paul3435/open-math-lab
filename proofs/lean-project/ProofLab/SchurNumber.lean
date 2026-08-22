import Mathlib.Tactic

/-!
# Schur numbers S(2) = 4, S(3) = 13  (formalize-only, OPE-46)

Schur's theorem: every finite colouring of the positive integers has a
monochromatic solution to `x + y = z`.  The **Schur number** `S(k)` is the
largest `n` such that `{1, …, n}` admits a `k`-colouring with **no**
monochromatic `x + y = z`; equivalently `S(k) + 1` is the least `N` such that
*every* `k`-colouring of `{1, …, N}` has a monochromatic solution.

**Convention pinned here (matches `S(2)=4`, `S(3)=13` and the classical
literature):** a colour class is *sum-free* when it contains no `x, y, z`
with `x + y = z` — `x = y` is **allowed**, so `1 + 1 = 2` already forces
colours `1` and `2` apart.  (The issue brief's phrase "distinct `x, y`" would
weaken the predicate and change the values — under the distinct-only reading
`[1,14]` is *not* 3-Schur-forcing — so the standard convention is used and
this divergence is flagged in `problems/schur-number/ATTACK_LOG.md`.)

A `k`-colouring of `{1, …, n}` is `f : Fin n → Fin k` where position `i`
carries the colour of the integer `i + 1`.  A monochromatic solution to
`x + y = z` inside the interval is a pair of positions `x, y` whose sum
`(x.val + 1) + (y.val + 1)` still lies in the interval.

## Main results (zero `sorry`, `native_decide` certified)

* `schur2_lower`: `Fin 4` has a 2-colouring with no monochromatic `x+y=z`
  (`{1,4}` / `{2,3}`), i.e. `S(2) ≥ 4` (in the "largest such `n`" reading).
* `schur2_le_4`: every 2-colouring of `Fin 5` has a monochromatic solution,
  i.e. the least-forcing `N` is `5`; combined: `S(2) = 4`.
* `schur3_lower`: `Fin 13` has a 3-colouring with no monochromatic solution,
  i.e. `S(3) ≥ 13`.
* `schur3_le_13`: every 3-colouring of `Fin 14` has a monochromatic solution,
  i.e. the least-forcing `N` is `14`; combined: `S(3) = 13`.
-/
namespace ProofLab.SchurNumber

set_option synthInstance.maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- The colouring `f : Fin n → Fin k` of `{1,…,n}` has a monochromatic
solution to `x + y = z`: positions `x, y` (values `x.val+1`, `y.val+1`) with
`x = y` allowed, whose sum value still lies inside the interval, all sharing
one colour. -/
def HasMonoSchur (f : Fin n → Fin k) : Prop :=
  ∃ (x y : Fin n) (h : x.val + y.val + 1 < n),
    f x = f y ∧ f x = f ⟨x.val + y.val + 1, h⟩

/-- Decidability of `HasMonoSchur` for a fixed colouring: the existential
ranges over finite `Fin n × Fin n` and every conjunct is decidable. -/
instance {k n : ℕ} (f : Fin n → Fin k) : Decidable (HasMonoSchur f) := by
  unfold HasMonoSchur
  infer_instance

/-- **S(2) ≥ 4**: the 2-colouring of `{1,2,3,4}` with classes `{1,4}` and
`{2,3}` has no monochromatic `x+y=z`.  Certified by decision.  Zero `sorry`. -/
def witnessS2 : Fin 4 → Fin 2 :=
  fun i => match i.val with
    | 0 | 3 => 0
    | _ => 1

/-- **S(2) ≥ 4**. -/
theorem schur2_lower : ¬ HasMonoSchur (witnessS2 : Fin 4 → Fin 2) := by
  native_decide

/-- **S(2) < 5**: every 2-colouring of `{1,…,5}` has a monochromatic
`x+y=z` (all `2^5` colourings checked).  Zero `sorry`. -/
theorem schur2_le_4 : ∀ f : Fin 5 → Fin 2, HasMonoSchur f := by
  native_decide

/-- **S(3) ≥ 13**: the 3-colouring of `{1,…,13}` with classes
`{1,4,7,10,13}`, `{2,3,11,12}`, `{5,6,8,9}` has no monochromatic `x+y=z`.
Certified by decision.  Zero `sorry`. -/
def witnessS3 : Fin 13 → Fin 3 :=
  fun i => match i.val with
    | 0 | 3 | 6 | 9 | 12 => 0
    | 1 | 2 | 10 | 11 => 1
    | _ => 2

/-- **S(3) ≥ 13**. -/
theorem schur3_lower : ¬ HasMonoSchur (witnessS3 : Fin 13 → Fin 3) := by
  native_decide

/-- **S(3) < 14**: every 3-colouring of `{1,…,14}` has a monochromatic
`x+y=z`.  Exhaustive decision over all `3^14` colourings; the check counts a
colour-class sum-free only when *no* `x+y=z` (with `x=y` allowed) is
monochromatic.  Zero `sorry`. -/
theorem schur3_le_13 : ∀ f : Fin 14 → Fin 3, HasMonoSchur f := by
  native_decide

end ProofLab.SchurNumber