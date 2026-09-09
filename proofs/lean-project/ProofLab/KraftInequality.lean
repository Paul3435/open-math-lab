/-
Kraft inequality — Level A only (empty Finset / singleton /
binary `{[0],[1,0],[1,1]}` Kraft sum `1`). **Not labelled Kraft /
Huffman.**

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 pin `a719ba5c3115` has `List.IsPrefix` / notation
`<+:` / `Finset.sum` / `Fintype.card` as **infra**. ZERO named
Kraft inequality / `PrefixFree` / `kraftSum` / `McMillan` /
`Huffman` / `uniquelyDecodable` under `Mathlib/` or `Archive/` or
`ProofLab/`. InformationTheory/ contains **only** `Hamming.lean`
(metric). Completing the Level A empty / singleton / binary
`{0,10,11}` glue is the gap this ticket lands. The Level B
namesake `kraft_inequality` (every finite prefix-free code over
`r ≥ 2` has Kraft sum `≤ 1`) is **out of this ticket** and is
**not** sorry-ed. McMillan uniquely-decodable / Huffman
optimality / Shannon source-coding extras are residual of this
id.

Pin: `catalog/problems/kraft-inequality/STATEMENT.md`
(OPE-1238; Scout OPE-1233 RECOMMENDED PRIME; Director OPE-1237).
Encoding: Mathlib `List.IsPrefix` / `<+:` / `Finset.sum` /
`Fintype.card` on `Finset (List α)`, Kraft sum in `ℚ`. Zero
`sorry`. Do not import `Archive.*`.

This is **not** `List.IsPrefix` / `<+:` (`Data/List/Infix.lean`
L12 / L23) — already Mathlib. **USE, do not re-prove; do not
cite as Kraft.**
This is **not** `hammingDist` (`InformationTheory/Hamming.lean`
L38) — Singleton glue, a different error-correcting theorem
(consumed #120). Do **not** revive `singleton_bound` /
Hamming-bound / Plotkin / MDS. OPE-1147: "This is not Kraft /
Shannon / Huffman".
This is **not** McMillan uniquely-decodable (residual of this
id; do **not** sorry McMillan; do **not** take McMillan as
namesake).
This is **not** Huffman / Shannon / Fano.
This is **not** Singleton (`ProofLab/SingletonBound.lean`,
PR #120).
This is **not** Petersen 1-factor (`ProofLab/PetersenOneFactor.lean`,
PR #135).
This is **not** Lagrange CF (`ProofLab/LagrangeQuadraticCf.lean`,
PR #136).
Do not re-prime the consumed mill. Leave OPE-403 alone.
Leave OPE-1195 alone. Do **not** prove sabidussi-boxprod here
(leftover, unassigned this tick).

v1 is prefix-free + Kraft sum on named codes over `Fin 2`:
empty `Finset`, singleton, and the binary tree
`{[0],[1,0],[1,1]}` with Kraft sum `1`, **not labelled Kraft**.
Count in `ℚ`. Alphabet cardinality `r = 2` is load-bearing for
the explicit example. Prefix-free (`¬ <+:`) is load-bearing.
Kraft sum in `ℚ` is load-bearing.

Level A: empty `Finset` is vacuously prefix-free with Kraft
sum `0`. A singleton has no distinct pair, so is prefix-free.
Binary `{[0],[1,0],[1,1]}` over `Fin 2` is prefix-free (the
length-1 word `[0]` is not a prefix of the two length-2 words
starting with `1`, and those two do not prefix each other) and
Kraft sum `2^{-1} + 2^{-2} + 2^{-2} = 1`. Optional extra:
singleton empty-word Kraft `1`. **Not** labelled Kraft.

Transcribed classical argument (L. G. Kraft, *A device for
quantizing, grouping, and coding amplitude-modulated pulses*,
M.S. thesis, MIT, 1949). Compact form: Wikipedia
*Kraft–McMillan inequality* (prefix-free half). Type pin:
`Finset (List α)` / `List.IsPrefix` / `ℚ` Kraft sum. McMillan
uniquely-decodable is a different residual theorem. Singleton /
`hammingDist` is a different consumed theorem. No novelty
claim. Default no claim.
-/
import Mathlib.Data.List.Infix
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Tactic

set_option linter.unusedVariables false

open List Finset
open scoped BigOperators

namespace ProofLab.KraftInequality

/-! ## Level A: empty Finset / singleton / binary {0, 10, 11}
(not labelled Kraft / Huffman) -/

/-- Distinct words in `C` are pairwise non-prefixes (`¬ <+:`).
Uses Mathlib `List.IsPrefix` / `<+:`; does **not** re-prove
prefix. Encoding; **not** labelled Kraft. -/
def PrefixFree {α : Type*} (C : Finset (List α)) : Prop :=
  ∀ u ∈ C, ∀ v ∈ C, u ≠ v → ¬ u <+: v

/-- Kraft sum `∑_w r^{-|w|}` in `ℚ`, `r = Fintype.card α`.
Uses Mathlib `Finset.sum` / `Fintype.card`; does **not**
re-prove them. Encoding; **not** labelled Kraft. -/
def kraftSum {α : Type*} [Fintype α] [DecidableEq α]
    (C : Finset (List α)) : ℚ :=
  C.sum fun w => ((Fintype.card α : ℚ)⁻¹) ^ w.length

/-- Empty code: vacuously prefix-free. Glue; **not** labelled
Kraft. -/
theorem prefixFree_empty {α : Type*} :
    PrefixFree (∅ : Finset (List α)) := by
  intro u hu
  exact (not_mem_empty u hu).elim

/-- Empty code: Kraft sum `0`. Uses `Finset.sum_empty`; does
**not** re-prove summation. Glue; **not** labelled Kraft. -/
theorem kraftSum_empty {α : Type*} [Fintype α] [DecidableEq α] :
    kraftSum (∅ : Finset (List α)) = 0 := by
  simp [kraftSum]

/-- A singleton has no distinct pair, so is prefix-free. Glue;
**not** labelled Kraft. -/
theorem prefixFree_singleton {α : Type*} [DecidableEq α]
    (w : List α) : PrefixFree {w} := by
  intro u hu v hv hne
  simp only [Finset.mem_singleton] at hu hv
  exact (hne (hu.trans hv.symm)).elim

/-- Binary example `{[0], [1,0], [1,1]}` over `Fin 2`. Alphabet
cardinality `r = 2` is load-bearing. Glue; **not** labelled
Kraft. -/
def kraftBinaryExample : Finset (List (Fin 2)) :=
  { [0], [1, 0], [1, 1] }

theorem mem_kraftBinaryExample {w : List (Fin 2)} :
    w ∈ kraftBinaryExample ↔ w = [0] ∨ w = [1, 0] ∨ w = [1, 1] := by
  simp [kraftBinaryExample]

/-- `[0]` is not a prefix of `[1,0]`. Uses `cons_prefix_iff`;
does **not** re-prove `<+:`. -/
theorem not_prefix_zero_of_one_zero :
    ¬ ([0] : List (Fin 2)) <+: [1, 0] := by
  intro h
  rw [cons_prefix_iff] at h
  exact Fin.zero_ne_one h.1

/-- `[0]` is not a prefix of `[1,1]`. Uses `cons_prefix_iff`;
does **not** re-prove `<+:`. -/
theorem not_prefix_zero_of_one_one :
    ¬ ([0] : List (Fin 2)) <+: [1, 1] := by
  intro h
  rw [cons_prefix_iff] at h
  exact Fin.zero_ne_one h.1

/-- Length-2 `[1,0]` cannot prefix length-1 `[0]`. Uses
`IsPrefix.length_le`; does **not** re-prove `<+:`. -/
theorem not_prefix_one_zero_of_zero :
    ¬ ([1, 0] : List (Fin 2)) <+: [0] := by
  intro h
  have := h.length_le
  simp at this

/-- Length-2 `[1,1]` cannot prefix length-1 `[0]`. -/
theorem not_prefix_one_one_of_zero :
    ¬ ([1, 1] : List (Fin 2)) <+: [0] := by
  intro h
  have := h.length_le
  simp at this

/-- Same-length siblings `[1,0]` and `[1,1]` do not prefix
each other. Uses `cons_prefix_iff`. -/
theorem not_prefix_one_zero_of_one_one :
    ¬ ([1, 0] : List (Fin 2)) <+: [1, 1] := by
  intro h
  rw [cons_prefix_iff, cons_prefix_iff] at h
  exact Fin.zero_ne_one h.2.1

theorem not_prefix_one_one_of_one_zero :
    ¬ ([1, 1] : List (Fin 2)) <+: [1, 0] := by
  intro h
  rw [cons_prefix_iff, cons_prefix_iff] at h
  exact (Fin.zero_ne_one h.2.1.symm)

/-- Binary `{[0],[1,0],[1,1]}` is prefix-free. Glue; **not**
labelled Kraft. -/
theorem prefixFree_kraftBinaryExample :
    PrefixFree kraftBinaryExample := by
  intro u hu v hv hne
  rw [mem_kraftBinaryExample] at hu hv
  rcases hu with (rfl | rfl | rfl) <;> rcases hv with (rfl | rfl | rfl)
  · exact (hne rfl).elim
  · exact not_prefix_zero_of_one_zero
  · exact not_prefix_zero_of_one_one
  · exact not_prefix_one_zero_of_zero
  · exact (hne rfl).elim
  · exact not_prefix_one_zero_of_one_one
  · exact not_prefix_one_one_of_zero
  · exact not_prefix_one_one_of_one_zero
  · exact (hne rfl).elim

theorem kraftBinaryExample_ne_zero_one_zero :
    ([0] : List (Fin 2)) ∉ ({[1, 0], [1, 1]} : Finset (List (Fin 2))) := by
  simp

theorem kraftBinaryExample_ne_one_zero_one_one :
    ([1, 0] : List (Fin 2)) ∉ ({[1, 1]} : Finset (List (Fin 2))) := by
  simp

/-- Binary example Kraft sum `2^{-1} + 2^{-2} + 2^{-2} = 1`.
Uses `Finset.sum_insert` / `Fintype.card_fin`; does **not**
re-prove them. Glue; **not** labelled Kraft. -/
theorem kraftSum_kraftBinaryExample :
    kraftSum kraftBinaryExample = 1 := by
  have hcard : (Fintype.card (Fin 2) : ℚ) = 2 := by
    simp [Fintype.card_fin]
  unfold kraftSum kraftBinaryExample
  rw [Finset.sum_insert kraftBinaryExample_ne_zero_one_zero,
    Finset.sum_insert kraftBinaryExample_ne_one_zero_one_one,
    Finset.sum_singleton]
  simp [hcard]
  norm_num

/-- Optional extra: the singleton empty word has Kraft sum `1`
when the alphabet is nonempty. Glue; **not** labelled Kraft. -/
theorem kraftSum_singleton_nil {α : Type*} [Fintype α] [DecidableEq α]
    (hα : 0 < Fintype.card α) :
    kraftSum ({[]} : Finset (List α)) = 1 := by
  have : (Fintype.card α : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hα)
  simp [kraftSum, pow_zero]

/- Residual of this id (comment, **not** `sorry`):
Level B namesake `kraft_inequality` — every finite prefix-free
code over `r ≥ 2` has Kraft sum `≤ 1`. McMillan uniquely-
decodable / Huffman optimality / Shannon source-coding / Fano /
Kraft-equality complete trees / infinite / σ-finite Kraft are
residual, not extra namesakes. Out of this ticket. Do **not**
prove McMillan / Huffman / Shannon / Hamming-bound / Plotkin /
MDS / singleton_bound / hammingDist as namesake /
petersen-1-factor / Tutte / lagrange-quadratic-cf /
terminates_iff_rat as namesake / sabidussi-boxprod. -/

end ProofLab.KraftInequality
