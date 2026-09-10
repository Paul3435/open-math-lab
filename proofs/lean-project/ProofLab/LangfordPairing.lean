/-
Named small-order pairing witnesses — Level A only
(order 1 none / order 2 none / order 3 `[2,3,1,2,1,3]`).
**Not labelled Langford / Skolem.**

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 pin `a719ba5c3115` has `List` / `List.length` /
`GetElem` / `List.get` / `List.filter` as **infra**. ZERO named
Langford / `langford` / `Langford` / `LangfordPairing` /
`skolemSequence` / `SkolemSequence` under `Mathlib/` or
`Archive/` or `ProofLab/` (this run; ProofLab hits are comments
in `LegendreThreeSquares.lean` saying do not prove Langford
there). Completing the Level A named small-order witnesses is
the gap this ticket lands. The Level B namesake
`langford_pairing` (exists iff `n ≡ 0 or 3 (mod 4)`) is **out
of this ticket** and is **not** sorry-ed. Skolem sequences /
hooked Langford / Nickerson variants are residual of this id.
Do **not** label theorems `skolem_*` (Skolem–Mahler–Lech /
Skolemization already-in name collision).

Pin: `catalog/problems/langford-pairing/STATEMENT.md`
(OPE-1352; Scout OPE-1342 leftover; Director OPE-1351).
Encoding: `IsLangford` via Mathlib `List` / `GetElem` /
`List.filter`. Zero `sorry`. Do not import `Archive.*`.

This is **not** `List` / `List.length` / `GetElem` / `List.get`
/ `List.filter` / `List.count` — already Mathlib. **USE, do
not re-prove; do not cite as Langford.**
This is **not** `Mathlib/ModelTheory/Skolem.lean` —
Skolemization, NOT Skolem sequences / Langford. Do **not**
import; do **not** cite as this gap.
This is **not** Fine–Wilf (`ProofLab/FineWilf.lean`, consumed
#144). Periods ≠ between-counts. Do **not** revive
Lyndon–Schützenberger. Do **not** define this namesake via
`List.IsPeriod`.
This is **not** orthogonal Latin squares
(`ProofLab/OrthogonalLatinSquares.lean`, consumed #157).
Latin ≠ Langford. Do **not** revive Euler officers / `n≠2,6`
/ Lo Shu.
This is **not** Legendre three-square
(`ProofLab/LegendreThreeSquares.lean`, consumed #159).
Do **not** revive Gauss Eureka / three triangular numbers.
This is **not** Jordan canonical form
(`ProofLab/JordanCanonicalForm.lean`, consumed #156).
Do not re-prime the consumed mill. Leave OPE-403 alone.
Leave OPE-1195 alone.

v1 is named small-order pairing witnesses: order 1 has none,
order 2 has none, and order 3 has `[2,3,1,2,1,3]`, **not
labelled Langford / Skolem**. Between-count `k` (indices
differ by `k+1`) is load-bearing. `langford_one_none` /
`langford_two_none` are load-bearing (so Level A is **not**
"some sequences exist").

Level A: order-1 none / order-2 none / order-3 witness.
Optional extra: one order-4 witness. **Not** labelled
Langford / Skolem.

Transcribed classical argument (C. Dudley Langford 1958
pairings; small-order exhaustive placement). Compact form:
Wikipedia *Langford pairing*. Type pin: `IsLangford` /
`List ℕ`. Fine–Wilf periods are a different consumed mill.
Skolem sequences are a different residual. No novelty claim.
Default no claim.
-/
import Mathlib.Tactic

set_option linter.unusedVariables false

namespace ProofLab.LangfordPairing

/-! ## Encoding: between-count pairings (not labelled Langford / Skolem) -/

/-- A list of length `2n` containing each `k ∈ {1,…,n}` twice,
with exactly `k` entries strictly between the two copies of
`k`. Encoding; **not** labelled Langford / Skolem.
Load-bearing: between-count `k` (indices differ by `k+1`).
Does **not** re-prove `List` / `GetElem` / `List.filter`. -/
def IsLangford (w : List ℕ) (n : ℕ) : Prop :=
  w.length = 2 * n ∧
  (∀ k, 1 ≤ k ∧ k ≤ n → (w.filter (· = k)).length = 2) ∧
  (∀ k, 1 ≤ k ∧ k ≤ n →
    ∃ i j : ℕ, i < j ∧ j = i + k + 1 ∧
      w[i]? = some k ∧ w[j]? = some k)

/-- `GetElem?` glue: a `some` readout is in range.
Does **not** re-prove `GetElem`. -/
lemma getElem?_some_lt {α : Type*} {w : List α} {i : ℕ} {a : α}
    (h : w[i]? = some a) : i < w.length := by
  by_contra hnot
  have hle : w.length ≤ i := Nat.le_of_not_lt hnot
  have hnone : w[i]? = none := List.getElem?_eq_none hle
  simp [hnone] at h

/-! ## Level A: named small-order witnesses (not labelled Langford / Skolem) -/

/-- Order 1 has no pairing: length 2 cannot place two `1`s with
`1` between. Glue; **not** labelled Langford.
Load-bearing: `langford_one_none` (so Level A is **not**
"some sequences exist"). -/
theorem langford_one_none : ¬ ∃ w, IsLangford w 1 := by
  rintro ⟨w, hlen, _hcount, hpos⟩
  obtain ⟨i, j, hij, hj, _hiw, hjw⟩ :=
    hpos 1 ⟨Nat.le_refl 1, Nat.le_refl 1⟩
  have hjlt : j < w.length := getElem?_some_lt hjw
  omega

/-- Order 2 has no pairing (`n ≡ 2 (mod 4)`). Glue; **not**
labelled Langford. Load-bearing: the two `2`s occupy the only
distance-`3` slot, which collides with every distance-`2`
slot for the `1`s. -/
theorem langford_two_none : ¬ ∃ w, IsLangford w 2 := by
  rintro ⟨w, hlen, _hcount, hpos⟩
  obtain ⟨i2, j2, _hij2, hj2eq, hi2w, hj2w⟩ :=
    hpos 2 ⟨by omega, Nat.le_refl 2⟩
  have hj2lt : j2 < w.length := getElem?_some_lt hj2w
  have hi2z : i2 = 0 := by omega
  have hj2z : j2 = 3 := by omega
  obtain ⟨i1, j1, _hij1, hj1eq, hi1w, hj1w⟩ :=
    hpos 1 ⟨Nat.le_refl 1, by omega⟩
  have hi1lt : i1 < w.length := getElem?_some_lt hi1w
  have hj1lt : j1 < w.length := getElem?_some_lt hj1w
  have hi1alt : i1 = 0 ∨ i1 = 1 := by omega
  rcases hi1alt with hi10 | hi11
  · have h1 : w[0]? = some 1 := by simpa [hi10] using hi1w
    have h2 : w[0]? = some 2 := by simpa [hi2z] using hi2w
    simp [h1] at h2
  · have hj13 : j1 = 3 := by omega
    have h1 : w[3]? = some 1 := by simpa [hj13] using hj1w
    have h2 : w[3]? = some 2 := by simpa [hj2z] using hj2w
    simp [h1] at h2

/-- Order 3 witness `[2, 3, 1, 2, 1, 3]`.
`1`s at indices 2,4 (one between); `2`s at 0,3; `3`s at 1,5.
Glue; **not** labelled Langford / Skolem. -/
theorem langford_three : IsLangford [2, 3, 1, 2, 1, 3] 3 := by
  refine ⟨rfl, ?count, ?pos⟩
  · intro k hk
    have : k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases this with rfl | rfl | rfl <;> rfl
  · intro k hk
    have : k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases this with rfl | rfl | rfl
    · exact ⟨2, 4, by omega, rfl, rfl, rfl⟩
    · exact ⟨0, 3, by omega, rfl, rfl, rfl⟩
    · exact ⟨1, 5, by omega, rfl, rfl, rfl⟩

/-- Optional extra: one order-4 witness
`[4, 1, 3, 1, 2, 4, 3, 2]`. Glue; **not** labelled Langford. -/
theorem langford_four : IsLangford [4, 1, 3, 1, 2, 4, 3, 2] 4 := by
  refine ⟨rfl, ?count, ?pos⟩
  · intro k hk
    have : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
    rcases this with rfl | rfl | rfl | rfl <;> rfl
  · intro k hk
    have : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
    rcases this with rfl | rfl | rfl | rfl
    · exact ⟨1, 3, by omega, rfl, rfl, rfl⟩
    · exact ⟨4, 7, by omega, rfl, rfl, rfl⟩
    · exact ⟨2, 6, by omega, rfl, rfl, rfl⟩
    · exact ⟨0, 5, by omega, rfl, rfl, rfl⟩

/-
Level B namesake OUT of this ticket (do not sorry):
  theorem langford_pairing :
      ∀ n : ℕ, (∃ w, IsLangford w n) ↔ n % 4 = 0 ∨ n % 4 = 3
Skolem sequences (distance `k`, `n ≡ 0 or 1 (mod 4)`) are
residual of this id — do not expand; do not label theorems
`skolem_*`.
-/

end ProofLab.LangfordPairing
