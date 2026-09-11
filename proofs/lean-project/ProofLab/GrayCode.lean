/-
Named small-length Hamming listings — Level A only
(length-1 two vectors / length-2 `00,01,11,10` / length-3
binary-reflected listing). **Not labelled Gray / Ore /
Singleton.**

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 pin `a719ba5c3115` has `hammingDist` /
`hammingDist_self` / `hammingDist_comm` / `Fin` / `List` /
`List.Nodup` as **infra**. ZERO named Gray-code theorem /
`GrayCode` / `grayCode` / `gray_code` / `binaryReflected` /
`reflectedGray` under `Mathlib/` or `Archive/` or `ProofLab/`
(this run). Completing the Level A named small-length listings
is the gap this ticket lands. The Level B namesake `gray_code`
(exists a Hamming-adjacent listing of all `n`-bit strings for
every `n`) is **out of this ticket** and is **not** sorry-ed.
Hypercube Hamiltonian / Ore-on-the-cube / Beckett–Gray extras
are residual of this id. Do **not** label theorems `ore_*` /
`hamiltonian_*` / `singleton_*` as this listing. Do **not**
define the namesake via `Walk.IsHamiltonian` or `cubeGraph`.

Pin: `catalog/problems/gray-code/STATEMENT.md`
(OPE-1369; Scout OPE-1357 leftover slot #2; Director OPE-1368).
Encoding: `IsGrayCode` via Mathlib `hammingDist` / `List.Nodup`.
Zero `sorry`. Do not import `Archive.*`.

This is **not** `hammingDist` / `hammingDist_self` /
`hammingDist_comm` (`InformationTheory/Hamming.lean` L38 / L43 /
L52) — already Mathlib. **USE, do not re-prove; do not cite as
Gray.**
This is **not** the Singleton bound (`ProofLab/SingletonBound.lean`,
consumed #120). Min-distance cardinality bound ≠ adjacent-distance-1
listing of the whole space. USE `hammingDist`; do **not** re-prove;
do **not** cite as Gray; do **not** revive Hamming-bound / Plotkin /
MDS.
This is **not** Ore Hamiltonian (`ProofLab/OreHamiltonian.lean`,
consumed #111). Undirected degree-sum Ham cycle ≠ Hamming listing.
Do **not** use `Walk.IsHamiltonian` as namesake; do **not** define
`cubeGraph` as this theorem; do **not** revive Bondy–Chvátal.
This is **not** Kraft (`ProofLab/KraftInequality.lean`, consumed
#138). Prefix-free codes ≠ Gray listings. Do **not** revive
McMillan / Huffman / Shannon.
This is **not** Fine–Wilf (`ProofLab/FineWilf.lean`, consumed
#144). Periods ≠ adjacent bit-flips. Do **not** revive
Lyndon–Schützenberger.
This is **not** Myhill–Nerode (`ProofLab/MyhillNerode.lean`,
consumed #162). Nerode classes ≠ Gray listings. Do **not** prove
Nerode here; do **not** revive Kleene regex iff DFA.
This is **not** Langford pairing (`ProofLab/LangfordPairing.lean`,
consumed #160). Do **not** revive Skolem sequences.
This is **not** Legendre three-square
(`ProofLab/LegendreThreeSquares.lean`, consumed #159).
Do **not** revive Gauss Eureka / three triangular numbers.
Do not re-prime the consumed mill. Leave OPE-403 alone.
Leave OPE-1195 alone.

v1 is named small-length listings: length 1 is `![0], ![1]`,
length 2 is `00,01,11,10`, and length 3 is the reflected
listing, **not labelled Gray / Ore / Singleton**. Adjacent
`hammingDist = 1` plus full cover of `Fin n → Fin 2` are
load-bearing (so Level A is **not** "some binary lists exist").

Level A: length-1 / length-2 / length-3 listings. Optional
extra: `n = 0` unique empty-domain function, list length 1.
**Not** labelled Gray / Ore / Singleton.

Transcribed classical argument (Frank Gray 1953 reflected
binary code; Émile Baudot). Compact form: Wikipedia *Gray
code*. Type pin: `IsGrayCode` / `Fin n → Fin 2` / `hammingDist`.
Singleton min-distance is a different consumed mill. Ore
Hamiltonian is a different consumed mill. Myhill–Nerode is
the consumed prime of this shortlist. No novelty claim.
Default no claim.
-/
import Mathlib.InformationTheory.Hamming
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option linter.unusedVariables false

open Finset Function

namespace ProofLab.GrayCode

/-! ## Encoding: Hamming-adjacent full listings (not labelled Gray / Ore / Singleton) -/

/-- A listing of all `Fin n → Fin 2` in which consecutive
codewords have Hamming distance 1. Encoding; **not** labelled
Gray / Ore / Singleton. Load-bearing: length `2^n`, `Nodup`,
full cover, adjacent `hammingDist = 1`. Does **not** re-prove
`hammingDist` / `List.Nodup`. -/
def IsGrayCode {n : ℕ} (cs : List (Fin n → Fin 2)) : Prop :=
  cs.length = 2 ^ n ∧
  cs.Nodup ∧
  (∀ x, x ∈ cs) ∧
  ∀ i, i + 1 < cs.length → hammingDist (cs[i]!) (cs[i + 1]!) = 1

/-- Card of the word space. Glue; **not** labelled Gray.
Does **not** re-prove `Fintype.card`. -/
lemma card_word (n : ℕ) : Fintype.card (Fin n → Fin 2) = 2 ^ n := by
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

/-- A nodup list whose length is `|α|` contains every `x : α`.
Glue; **not** labelled Gray. Does **not** re-prove `List.Nodup`. -/
lemma mem_of_nodup_length_eq_card {α : Type*} [Fintype α] [DecidableEq α]
    {l : List α} (hnd : l.Nodup) (hlen : l.length = Fintype.card α) :
    ∀ x, x ∈ l := by
  intro x
  have hcard : l.toFinset.card = Fintype.card α := by
    rw [List.toFinset_card_of_nodup hnd, hlen]
  have heq : l.toFinset = univ := eq_univ_of_card _ hcard
  have : x ∈ l.toFinset := by
    rw [heq]
    exact mem_univ x
  exact List.mem_toFinset.mp this

/-- Adjacent Hamming distance 1 from a single differing
coordinate. **USE** Mathlib `hammingDist`; do **not** re-prove
the metric. Glue; **not** labelled Gray / Singleton. -/
lemma hammingDist_of_single {n : ℕ} {x y : Fin n → Fin 2} {i : Fin n}
    (hdiff : x i ≠ y i) (hsame : ∀ j, j ≠ i → x j = y j) :
    hammingDist x y = 1 := by
  unfold hammingDist
  have : univ.filter (fun j => x j ≠ y j) = {i} := by
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · intro hj
      by_contra hne
      exact hj (hsame j hne)
    · intro hj
      rwa [hj]
  rw [this, card_singleton]

/-! ## Level A: named small-length listings (not labelled Gray / Ore / Singleton) -/

/-- Length-1 listing `![0], ![1]`. Glue; **not** labelled Gray. -/
def grayOne : List (Fin 1 → Fin 2) := [![0], ![1]]

/-- Length-2 listing `00, 01, 11, 10` (MSB at index 0).
Glue; **not** labelled Gray. -/
def grayTwo : List (Fin 2 → Fin 2) :=
  [![0, 0], ![0, 1], ![1, 1], ![1, 0]]

/-- Binary-reflected length-3 listing
`000,001,011,010,110,111,101,100` (MSB at index 0).
Glue; **not** labelled Gray. -/
def grayThree : List (Fin 3 → Fin 2) :=
  [![0, 0, 0], ![0, 0, 1], ![0, 1, 1], ![0, 1, 0],
   ![1, 1, 0], ![1, 1, 1], ![1, 0, 1], ![1, 0, 0]]

/-- Optional extra: `n = 0` unique empty-domain function,
list length 1. Glue; **not** labelled Gray. -/
def grayZero : List (Fin 0 → Fin 2) := [fun _ => 0]

/-- Length-1 listing of the two functions `Fin 1 → Fin 2`.
Adjacent `hammingDist` 1. Glue; **not** labelled Gray / Ore /
Singleton. Load-bearing (so Level A is **not** "some binary
lists exist"). -/
theorem gray_one : IsGrayCode grayOne := by
  have hnd : grayOne.Nodup := by
    unfold grayOne
    decide
  refine ⟨rfl, hnd, ?cover, ?adj⟩
  · intro x
    exact mem_of_nodup_length_eq_card hnd (by simp [grayOne, card_word]) x
  · intro i hi
    have : i = 0 := by simp [grayOne] at hi; omega
    subst this
    exact hammingDist_of_single (i := (0 : Fin 1))
      (by simp [grayOne])
      (fun j hj => (hj (Subsingleton.elim j 0)).elim)

/-- Length-2 listing `00, 01, 11, 10`. Each adjacent step
flips one bit; all four vectors appear. Glue; **not** labelled
Gray / Ore / Singleton. Load-bearing. -/
theorem gray_two : IsGrayCode grayTwo := by
  have hnd : grayTwo.Nodup := by
    unfold grayTwo
    decide
  refine ⟨rfl, hnd, ?cover, ?adj⟩
  · intro x
    exact mem_of_nodup_length_eq_card hnd (by simp [grayTwo, card_word]) x
  · intro i hi
    have : i = 0 ∨ i = 1 ∨ i = 2 := by simp [grayTwo] at hi; omega
    rcases this with rfl | rfl | rfl
    · exact hammingDist_of_single (i := (1 : Fin 2))
        (by simp [grayTwo])
        (fun j hj => by fin_cases j <;> simp [grayTwo] at hj ⊢)
    · exact hammingDist_of_single (i := (0 : Fin 2))
        (by simp [grayTwo])
        (fun j hj => by fin_cases j <;> simp [grayTwo] at hj ⊢)
    · exact hammingDist_of_single (i := (1 : Fin 2))
        (by simp [grayTwo])
        (fun j hj => by fin_cases j <;> simp [grayTwo] at hj ⊢)

/-- Binary-reflected length-3 listing
`000,001,011,010,110,111,101,100`. Glue; **not** labelled
Gray / Ore / Singleton. Load-bearing. -/
theorem gray_three : IsGrayCode grayThree := by
  have hnd : grayThree.Nodup := by
    -- `decide` on `List.Nodup` of functions is kernel-decidable here
    -- (8 words, 3 bits); no `native_decide` / `ofReduceBool`.
    unfold grayThree
    decide
  refine ⟨rfl, hnd, ?cover, ?adj⟩
  · intro x
    exact mem_of_nodup_length_eq_card hnd (by simp [grayThree, card_word]) x
  · intro i hi
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by
      simp [grayThree] at hi; omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hammingDist_of_single (i := (2 : Fin 3))
        (by simp [grayThree])
        (fun j hj => by fin_cases j <;> simp [grayThree] at hj ⊢)
    · exact hammingDist_of_single (i := (1 : Fin 3))
        (by simp [grayThree])
        (fun j hj => by fin_cases j <;> simp [grayThree] at hj ⊢)
    · exact hammingDist_of_single (i := (2 : Fin 3))
        (by simp [grayThree])
        (fun j hj => by fin_cases j <;> simp [grayThree] at hj ⊢)
    · exact hammingDist_of_single (i := (0 : Fin 3))
        (by simp [grayThree])
        (fun j hj => by fin_cases j <;> simp [grayThree] at hj ⊢)
    · exact hammingDist_of_single (i := (2 : Fin 3))
        (by simp [grayThree])
        (fun j hj => by fin_cases j <;> simp [grayThree] at hj ⊢)
    · exact hammingDist_of_single (i := (1 : Fin 3))
        (by simp [grayThree])
        (fun j hj => by fin_cases j <;> simp [grayThree] at hj ⊢)
    · exact hammingDist_of_single (i := (2 : Fin 3))
        (by simp [grayThree])
        (fun j hj => by fin_cases j <;> simp [grayThree] at hj ⊢)

/-- Optional extra: `n = 0` unique empty-domain function,
list length 1. Adjacent condition vacuous. Glue; **not**
labelled Gray. -/
theorem gray_zero : IsGrayCode grayZero := by
  refine ⟨rfl, ?nodup, ?cover, ?adj⟩
  · simp [grayZero]
  · intro x
    exact mem_of_nodup_length_eq_card
      (by simp [grayZero])
      (by simp [grayZero, card_word])
      x
  · intro i hi
    simp [grayZero] at hi

/-
Level B namesake OUT of this ticket (do not sorry):
  theorem gray_code :
      ∀ n : ℕ, ∃ cs, IsGrayCode (n := n) cs
Hypercube Hamiltonian / Ore on the cube / Beckett–Gray extras
are residual of this id — do not expand; do not label theorems
`ore_*` / `hamiltonian_*` / `singleton_*`; do not define
`cubeGraph` / use `Walk.IsHamiltonian` as namesake.
-/

end ProofLab.GrayCode
