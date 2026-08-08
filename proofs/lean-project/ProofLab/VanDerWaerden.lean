import Mathlib.Tactic

/-!
# Finite Van der Waerden number W(2,3) = 9  (formalize-only, OPE-45)

A 2-colouring of the integer interval `[0, n)` (represented as
`f : Fin n → Bool`) is called **monochromatic-3-AP-containing** when there is a
3-term arithmetic progression `(a, a+d, a+2d)` with `d > 0` lying entirely in
the interval and all of the same colour.

`W(2,3)` is the least `n` such that *every* 2-colouring of `[0, n)` contains a
monochromatic 3-term AP.  The classical value is `W(2,3) = 9`.

## Main results (zero `sorry`, `native_decide` certified)

* `vdw_le_9`: every 2-colouring of `Fin 9` has a monochromatic 3-term AP.
* `vdw_gt_8`: the 2-colouring `witness8` of `Fin 8` (`1 1 0 0 1 1 0 0`) has
  none; any colouring of `Fin n` (n ≤ 8) restricts of `Fin 8`, so this is the
  tightness of the bound.
-/
namespace ProofLab.VanDerWaerden

set_option synthInstance.maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- Colour at integer position `p` under `f : Fin n → Bool`, with a
decidable fallback colour outside `[0, n)` (irrelevant once `p < n` holds).
Used to keep the monochromatic-AP predicate plainly decidable for
`native_decide`. -/
def colorAt (f : Fin n → Bool) (p : ℕ) : Bool :=
  if h : p < n then f ⟨p, h⟩ else false

/-- A colouring `f : Fin n → Bool` contains a monochromatic 3-term arithmetic
progression: there exist `a` and a positive step `d` with `a+2d < n` and all
three positions `a`, `a+d`, `a+2d` sharing one colour. -/
def HasMono3 (f : Fin n → Bool) : Prop :=
  ∃ (a : Fin n) (d : Fin n),
    0 < d.val ∧ a.val + 2 * d.val < n ∧
      (colorAt f a.val = colorAt f (a.val + d.val) ∧
       colorAt f a.val = colorAt f (a.val + 2 * d.val))

/-- Decidability of `HasMono3` for a fixed colouring: the existential
ranges over the finite types `Fin n × Fin n` and every conjunct is decidable. -/
instance {n : ℕ} (f : Fin n → Bool) : Decidable (HasMono3 f) := by
  unfold HasMono3 colorAt
  infer_instance

/-- **W(2,3) ≤ 9**: every one of the `2^9` 2-colourings of `[0,9)` has a
monochromatic 3-term AP.  Certified by exhaustive decision.  Zero `sorry`. -/
theorem vdw_le_9 : ∀ f : Fin 9 → Bool, HasMono3 f := by
  native_decide

/-- A 2-colouring of `[0,8)` with no monochromatic 3-term AP:
`1 1 0 0 1 1 0 0`. -/
def witness8 : Fin 8 → Bool :=
  fun i =>
    match i.val with
    | 0 | 1 | 4 | 5 => true
    | _ => false

/-- **W(2,3) > 8**: the colouring `witness8` of `Fin 8` avoids monochromatic
3-term APs.  Certified by decision.  Zero `sorry`. -/
theorem vdw_gt_8 : ¬ HasMono3 (witness8 : Fin 8 → Bool) := by
  native_decide

end ProofLab.VanDerWaerden
