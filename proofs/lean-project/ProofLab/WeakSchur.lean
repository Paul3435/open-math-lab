import Mathlib.Tactic

/-!
# Weak Schur number WS(2) = 8  (formalize-only, OPE-462)

The **weak Schur number** `WS(k)` is the largest `n` such that `{1, …, n}`
admits a `k`-colouring with **no monochromatic weakly Schur triple**: there are
no **distinct** `x, y` (and automatically distinct `z = x + y`) with
`x + y = z ≤ n` and all three the same colour.

This is strictly weaker than the classical (strong) Schur predicate used in
`ProofLab/SchurNumber.lean`, where `x = y` is allowed and `1 + 1 = 2` already
forces colours of `1` and `2` apart.  Under the weak reading the classical
values diverge: `S(2) = 4` vs `WS(2) = 8`.

**Convention pinned (matches Abbott–Wang / Exoo weak-Schur literature and
Scout OPE-458 dossier `weak-schur-ws2`):**

* Distinctness requirement is **`x ≠ y` only**.  Since `x, y ≥ 1`, the sum
  `z = x + y` automatically differs from both, so the triple is pairwise
  distinct once `x ≠ y`.
* Domain is the integer interval **`{1, …, n}`**, encoded as `f : Fin n → Fin k`
  where position `i` carries the colour of the integer **`i.val + 1`**
  (the usual Fin-offset landmine — do not treat `Fin n` as `{0, …, n-1}`
  equations directly).
* A monochromatic weak triple inside the interval is a pair of positions
  `x, y` with `x ≠ y` whose sum value still lies in the interval
  (`x.val + y.val + 1 < n`) and shares one colour with both summands.
* Do **not** conflate with closed `schur-partition` (partition identity) or
  strong Schur `S(k)` scopes.

## Main results (zero `sorry`, `native_decide` certified)

* `ws2_gt_7`: `Fin 8` has a 2-colouring with no monochromatic weak Schur
  triple (classes `{1,2,4,8}` / `{3,5,6,7}`), i.e. `WS(2) ≥ 8`.
* `ws2_le_8`: every 2-colouring of `Fin 9` has a monochromatic weak Schur
  triple (all `2^9 = 512` colourings checked), i.e. `WS(2) ≤ 8`.
* `ws2_eq_8`: combining both bounds, `WS(2) = 8`.

Known-classical only (Abbott & Wang; Exoo).  No novelty claim.
-/
namespace ProofLab.WeakSchur

set_option synthInstance.maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- The colouring `f : Fin n → Fin k` of `{1,…,n}` has a monochromatic
**weak** Schur triple: positions `x, y` with **`x ≠ y`** (values
`x.val+1`, `y.val+1`) whose sum value still lies inside the interval, all
sharing one colour.  The sum position is `⟨x.val + y.val + 1, _⟩`, i.e. the
integer `(x.val+1)+(y.val+1)`. -/
def HasMonoWeakSchur (f : Fin n → Fin k) : Prop :=
  ∃ (x y : Fin n) (h : x.val + y.val + 1 < n),
    x ≠ y ∧ f x = f y ∧ f x = f ⟨x.val + y.val + 1, h⟩

/-- Decidability of `HasMonoWeakSchur` for a fixed colouring: the existential
ranges over finite `Fin n × Fin n` and every conjunct is decidable. -/
instance {k n : ℕ} (f : Fin n → Fin k) : Decidable (HasMonoWeakSchur f) := by
  unfold HasMonoWeakSchur
  infer_instance

/-- **WS(2) ≥ 8**: the 2-colouring of `{1,…,8}` with classes
`{1,2,4,8}` (colour 0) and `{3,5,6,7}` (colour 1) has no monochromatic weak
Schur triple.  Bitstring on positions `0..7` (integers `1..8`): `00101110`.
One of exactly two complementary valid colourings of length 8 (exhaustive
Scout/Attack probe).  Certified by decision.  Zero `sorry`. -/
def witnessWS2 : Fin 8 → Fin 2 :=
  fun i => match i.val with
    | 2 | 4 | 5 | 6 => 1
    | _ => 0

/-- **WS(2) ≥ 8** (equivalently `WS(2) > 7`). -/
theorem ws2_gt_7 : ¬ HasMonoWeakSchur (witnessWS2 : Fin 8 → Fin 2) := by
  native_decide

/-- **WS(2) ≤ 8**: every 2-colouring of `{1,…,9}` has a monochromatic weak
Schur triple (all `2^9 = 512` colourings checked by exhaustive decision).
Zero `sorry`.  No heuristic search. -/
theorem ws2_le_8 : ∀ f : Fin 9 → Fin 2, HasMonoWeakSchur f := by
  native_decide

/-- **WS(2) = 8**: lower bound via explicit witness on `{1,…,8}`, upper bound
via exhaustive forcing on `{1,…,9}`. -/
theorem ws2_eq_8 :
    (¬ HasMonoWeakSchur (witnessWS2 : Fin 8 → Fin 2)) ∧
      (∀ f : Fin 9 → Fin 2, HasMonoWeakSchur f) :=
  ⟨ws2_gt_7, ws2_le_8⟩

end ProofLab.WeakSchur
