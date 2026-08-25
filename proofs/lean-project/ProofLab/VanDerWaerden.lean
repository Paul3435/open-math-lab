import Mathlib.Tactic

/-!
# Finite Van der Waerden numbers W(2,3) = 9 and W(2,4) > 34

A 2-colouring of the integer interval `[0, n)` (represented as
`f : Fin n → Bool`) is called **monochromatic-k-AP-containing** when there is a
k-term arithmetic progression with positive common difference lying entirely in
the interval and all of the same colour.

`W(2,k)` is the least `n` such that *every* 2-colouring of `[0, n)` contains a
monochromatic k-term AP.

## W(2,3) = 9  (OPE-45, closed)

* `vdw_le_9`: every 2-colouring of `Fin 9` has a monochromatic 3-term AP.
* `vdw_gt_8`: the 2-colouring `witness8` of `Fin 8` (`1 1 0 0 1 1 0 0`) has
  none.

## W(2,4) lower bound  (OPE-455, partial ladder)

Classical value `W(2,4) = 35` (Chvátal 1979, computer-assisted upper bound).
This module certifies the **lower half** only:

* `vdw24_gt_34`: the 2-colouring `witness34` of `Fin 34` has no monochromatic
  4-term AP, so `W(2,4) > 34`.

The matching upper bound `W(2,4) ≤ 35` is **not** proved here: exhaustive
`native_decide` cannot scale to `2^35` colourings, and a hand case-analysis /
certificate import was timeboxed out. See `problems/van-der-waerden-w24/STATEMENT.md`.

Zero `sorry` / `admit` / custom axioms in this file.
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

/-! ## 3-term APs — W(2,3) -/

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

/-! ## 4-term APs — W(2,4) lower bound (OPE-455) -/

/-- A colouring `f : Fin n → Bool` contains a monochromatic 4-term arithmetic
progression: there exist `a` and a positive step `d` with `a+3d < n` and all
four positions `a`, `a+d`, `a+2d`, `a+3d` sharing one colour. -/
def HasMono4 (f : Fin n → Bool) : Prop :=
  ∃ (a : Fin n) (d : Fin n),
    0 < d.val ∧ a.val + 3 * d.val < n ∧
      (colorAt f a.val = colorAt f (a.val + d.val) ∧
       colorAt f a.val = colorAt f (a.val + 2 * d.val) ∧
       colorAt f a.val = colorAt f (a.val + 3 * d.val))

/-- Decidability of `HasMono4` for a fixed colouring. -/
instance {n : ℕ} (f : Fin n → Bool) : Decidable (HasMono4 f) := by
  unfold HasMono4 colorAt
  infer_instance

/-- Bit-mask for a 2-colouring of `[0,34)` with no monochromatic 4-AP.
Bit `i` is the colour of position `i` (`true` = 1).  Explicit string
(index 0 left):

`0010001110100100011101001000111011`

Found by offline pruned backtrack; re-checked by exhaustive 4-AP scan in Python
and by `native_decide` below.  Not claimed original — existence is classical. -/
def witness34Mask : ℕ := 14783751620

/-- The colouring of `Fin 34` encoded by `witness34Mask`. -/
def witness34 : Fin 34 → Bool :=
  fun i => witness34Mask.testBit i.val

/-- **W(2,4) > 34**: the colouring `witness34` of `Fin 34` avoids monochromatic
4-term APs.  Certified by decision on one fixed colouring (not an enumeration of
`2^34` colourings).  Zero `sorry`. -/
theorem vdw24_gt_34 : ¬ HasMono4 (witness34 : Fin 34 → Bool) := by
  native_decide

end ProofLab.VanDerWaerden
