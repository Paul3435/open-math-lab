/-
Fine–Wilf periodicity lemma — Level A only (empty / constant
period 1 / `[0,1,0,1,0]` periods 2 and 4). **Not labelled
Fine–Wilf / Lyndon–Schützenberger / Kraft.**

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 pin `a719ba5c3115` has `List.get` / `GetElem` /
`Nat.gcd` / `List.replicate` as **infra**. ZERO named Fine–Wilf /
`fineWilf` / `fine_wilf` / `FineWilf` / word `IsPeriod` under
`Mathlib/` or `Archive/` or `ProofLab/`. Unrelated Calkin–Wilf /
GNW / Wilf-χ hits only (Farey / hook-length / expander leftovers).
Completing the Level A empty / replicate period 1 / length-5
binary glue is the gap this ticket lands. The Level B namesake
`fine_wilf` (every finite word with periods `p,q` long enough
has period `gcd(p,q)`) is **out of this ticket** and is **not**
sorry-ed. Lyndon–Schützenberger commuting words / critical
factorization / Thue–Morse cube-free extras are residual of
this id.

Pin: `catalog/problems/fine-wilf/STATEMENT.md`
(OPE-1268; Scout OPE-1263 RECOMMENDED PRIME; Director OPE-1267).
Encoding: linear `IsPeriod` on `List` via Mathlib `GetElem` /
`Nat.gcd` / `List.replicate`. Zero `sorry`. Do not import
`Archive.*`.

This is **not** `List.get` / `GetElem` (`Data/List`) — already
Mathlib. **USE, do not re-prove; do not cite as Fine–Wilf.**
This is **not** `Nat.gcd` (`Data/Nat/GCD/Basic.lean` L12) —
already Mathlib. **USE, do not re-prove.**
This is **not** `List.replicate` — already Mathlib. **USE, do
not re-prove.**
This is **not** `List.rotate` / `List.IsRotated` (`Rotate.lean`
L18) — DIFFERENT cyclic glue; a linear period is not a
rotation. **USE only as optional extra glue; do not re-prove;
do not cite as Fine–Wilf.**
This is **not** `List.IsPrefix` / `<+:` (`Infix.lean` L12) —
Kraft glue, a different consumed theorem (PR #138). **USE if
needed; do not re-prove; do not cite as Fine–Wilf.**
This is **not** Kraft / McMillan / Huffman / Shannon
(`ProofLab/KraftInequality.lean`, PR #138).
This is **not** Calkin–Wilf (`ProofLab/FareySequence.lean`,
PR #127).
This is **not** Greene–Nijenhuis–Wilf (`ProofLab/HookLength.lean`,
PR #121).
This is **not** Wilf `χ ≤ 1+λ_max` (`ProofLab/ExpanderMixing.lean`).
This is **not** Dynamics `IsPeriodicPt` (function-iterate period,
not word period).
This is **not** Sherman–Morrison (`ProofLab/ShermanMorrison.lean`,
PR #141) / Woodbury.
This is **not** Graham–Pollak (`ProofLab/GrahamPollak.lean`,
PR #142) / biclique cover / Zarankiewicz.
This is **not** British flag / parallelogram_law as namesake.
Do not re-prime the consumed mill. Leave OPE-403 alone.
Leave OPE-1195 alone. Do **not** prove british-flag here
(leftover, unassigned this tick).

v1 is the period predicate on named finite lists: empty `[]`,
a constant (period-1) word, and the length-5 binary word
`[0,1,0,1,0]` with periods 2 and 4, **not labelled Fine–Wilf**.
`p ≠ 0` is load-bearing. Linear (not cyclic) period is
load-bearing. `Nat.gcd` is load-bearing.

Level A: empty list vacuously satisfies the period predicate
for any `p ≠ 0` (no indices in range). Constant `replicate n a`
is period 1. Binary `[0,1,0,1,0]` has `w[i] = w[i+2]` and
`w[i] = w[i+4]` on in-range indices, and `Nat.gcd 2 4 = 2`
so the gcd period is the period-2 fact. Optional extra: a
sharpness witness of length `p+q−gcd−1` that fails the gcd
period. **Not** labelled Fine–Wilf.

Transcribed classical argument (N. J. Fine, H. S. Wilf,
*Uniqueness theorems for periodic functions*, Proc. Amer.
Math. Soc. 16 (1965) 109–114). Compact form: Wikipedia
*Fine and Wilf's theorem*. Type pin: linear `IsPeriod` /
`Nat.gcd` / `List.get`. Kraft is a different consumed
prefix-free theorem. `List.rotate` is a different cyclic
predicate. Lyndon–Schützenberger is a different residual
commuting-words identity. No novelty claim. Default no claim.
-/
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic

set_option linter.unusedVariables false

namespace List

/-- Linear (not cyclic) period: `p ≠ 0` and `w[i] = w[i+p]`
whenever both indices are in range. Uses Mathlib `GetElem`;
does **not** re-prove list get. Encoding; **not** labelled
Fine–Wilf. A linear period is not `List.rotate` / `IsRotated`. -/
def IsPeriod {α : Type*} (w : List α) (p : ℕ) : Prop :=
  p ≠ 0 ∧ ∀ (i) (h : i + p < w.length),
    w[i]'(Nat.lt_of_le_of_lt (Nat.le_add_right i p) h) = w[i + p]'h

end List

namespace ProofLab.FineWilf

open List

/-! ## Level A: empty / constant period 1 / `[0,1,0,1,0]`
periods 2 and 4 (not labelled Fine–Wilf) -/

/-- Empty list: no in-range pair, so vacuously period `p`
for any `p ≠ 0`. Glue; **not** labelled Fine–Wilf. -/
theorem isPeriod_nil (p : ℕ) (hp : p ≠ 0) :
    ([] : List ℕ).IsPeriod p := by
  refine ⟨hp, ?_⟩
  intro i h
  simp at h

/-- Constant `replicate n a` is period 1. Uses
`List.getElem_replicate`; does **not** re-prove replicate.
Glue; **not** labelled Fine–Wilf. `0 < n` is the pin. -/
theorem isPeriod_replicate_one (n : ℕ) (a : ℕ) (hn : 0 < n) :
    (List.replicate n a).IsPeriod 1 := by
  refine ⟨one_ne_zero, ?_⟩
  intro i h
  have hi : i + 1 < n := by simpa [length_replicate] using h
  have _ := hn
  simp [getElem_replicate]

/-- Length-5 binary word `[0,1,0,1,0]`. Glue; **not** labelled
Fine–Wilf. -/
def fineWilfBinary : List (Fin 2) := [0, 1, 0, 1, 0]

theorem fineWilfBinary_length : fineWilfBinary.length = 5 := rfl

/-- `[0,1,0,1,0]` has period 2. Glue; **not** labelled Fine–Wilf. -/
theorem isPeriod_fineWilfBinary_two : fineWilfBinary.IsPeriod 2 := by
  refine ⟨by decide, ?_⟩
  intro i h
  have : i < 3 := by
    have hi : i + 2 < 5 := by simpa [fineWilfBinary] using h
    omega
  interval_cases i
  · rfl
  · rfl
  · rfl

/-- `[0,1,0,1,0]` has period 4. Glue; **not** labelled Fine–Wilf. -/
theorem isPeriod_fineWilfBinary_four : fineWilfBinary.IsPeriod 4 := by
  refine ⟨by decide, ?_⟩
  intro i h
  have : i < 1 := by
    have hi : i + 4 < 5 := by simpa [fineWilfBinary] using h
    omega
  interval_cases i
  · rfl

/-- `Nat.gcd 2 4 = 2`. Uses Mathlib `Nat.gcd`; does **not**
re-prove gcd. Glue; **not** labelled Fine–Wilf. -/
theorem gcd_two_four : Nat.gcd 2 4 = 2 := rfl

/-- `[0,1,0,1,0]` has period `Nat.gcd 2 4`. Glue; **not**
labelled Fine–Wilf. -/
theorem isPeriod_fineWilfBinary_gcd :
    fineWilfBinary.IsPeriod (Nat.gcd 2 4) := by
  rw [gcd_two_four]
  exact isPeriod_fineWilfBinary_two

/-- Optional extra: length `p+q−gcd(p,q)−1 = 6` word
`[0,1,0,0,1,0]` has periods 3 and 5 but not period
`gcd 3 5 = 1`. Sharpness witness; **not** labelled Fine–Wilf. -/
def fineWilfSharpness : List (Fin 2) := [0, 1, 0, 0, 1, 0]

theorem isPeriod_fineWilfSharpness_three : fineWilfSharpness.IsPeriod 3 := by
  refine ⟨by decide, ?_⟩
  intro i h
  have : i < 3 := by
    have hi : i + 3 < 6 := by simpa [fineWilfSharpness] using h
    omega
  interval_cases i
  · rfl
  · rfl
  · rfl

theorem isPeriod_fineWilfSharpness_five : fineWilfSharpness.IsPeriod 5 := by
  refine ⟨by decide, ?_⟩
  intro i h
  have : i < 1 := by
    have hi : i + 5 < 6 := by simpa [fineWilfSharpness] using h
    omega
  interval_cases i
  · rfl

theorem gcd_three_five : Nat.gcd 3 5 = 1 := rfl

theorem not_isPeriod_fineWilfSharpness_one :
    ¬ fineWilfSharpness.IsPeriod 1 := by
  intro h
  have h01 := h.2 0 (by decide : (0 : ℕ) + 1 < fineWilfSharpness.length)
  exact Fin.zero_ne_one h01

theorem not_isPeriod_fineWilfSharpness_gcd :
    ¬ fineWilfSharpness.IsPeriod (Nat.gcd 3 5) := by
  rw [gcd_three_five]
  exact not_isPeriod_fineWilfSharpness_one

/-
Level B namesake OUT of this ticket (do not sorry):

theorem fine_wilf {α} [DecidableEq α] (w : List α) (p q : ℕ)
    (hp : w.IsPeriod p) (hq : w.IsPeriod q)
    (h : p + q - Nat.gcd p q ≤ w.length) :
    w.IsPeriod (Nat.gcd p q)

Residual of this id (comment only, not sorry):
Lyndon–Schützenberger commuting words / critical factorization /
Thue–Morse cube-free. Do not expand this ticket. Do not prove
Kraft / McMillan / Huffman / Shannon / List.rotate as namesake /
List.IsRotated as namesake / Calkin–Wilf / GNW / Wilf-χ /
Dynamics IsPeriodicPt as namesake / sherman-morrison / Woodbury /
graham-pollak / british-flag.
-/

end ProofLab.FineWilf
