/-
Bollobás two-families — Level A only (empty / singleton / a=0 / b=0 / one-pair).
**Not labelled Bollobás.**

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 has `Nat.choose` / `choose_pos` / `Finset` / `Disjoint` /
`Fintype.card` and ZERO named Bollobás two-families theorem (book citations
only in `Data/{Set,Finset}/Sups.lean`). Completing the Level A empty /
singleton / `a=0` / `b=0` / one-pair glue is the gap this ticket lands.
The Level B namesake `bollobas` (permutation counting
`|ι| · a! · b! ≤ (a+b)!`) is **out of this ticket** and is **not** sorry-ed.
Weighted `ℚ` / Hilton–Milner / Eventown / Fisher extras are residual.

Pin: `catalog/problems/bollobas-two-families/STATEMENT.md` (OPE-1135; Scout
OPE-1125 leftover slot #2; Director OPE-1134). Encoding: Mathlib `Finset` +
`Nat.choose`. Zero `sorry`. Do not import `Archive.*`.

This is **not** Sperner / LYM (`IsAntichain.sperner`, `LYM.lean` L214) —
already Mathlib; antichain middle-binomial bound. **USE `Nat.choose`; do
not re-prove; do not cite as Bollobás.** This is **not** Kruskal–Katona
(`ProofLab/KruskalKatona.lean`, PR #67) — colex shadows. This is **not**
EKR (`ProofLab/ErdosKoRado.lean`, #39+#41). This is **not** Oddtown (#68)
/ sunflower (#70) / Sauer–Shelah (already `SetFamily/Shatter.lean`).
This is **not** Cauchy–Binet (`ProofLab/CauchyBinet.lean`, PR #117) —
different consumed theorem; do not revive Level B / Kirchhoff. This is
**not** Hadamard / Schwartz–Zippel Level B. Do not re-prime the consumed
mill. Leave OPE-403 alone. Do **not** prove weighted Q / Hilton–Milner /
Eventown / Fisher here.

v1 is the uniform integer form. `Disjoint (A i) (B i)` is load-bearing.
Cross intersections `i ≠ j → A_i ∩ B_j nonempty` are load-bearing.
Uniform `a, b` is load-bearing for this pin (weighted Q residual).
`Fintype α` is load-bearing for the permutation universe (even if Level A
does not need the permutation count).

Level A: empty family `card = 0 ≤ C(a+b, a)`. One pair:
`1 ≤ C(a+b, a)` via `choose_pos` once `a ≤ a+b`. If `a = 0` then each
`A_i` is empty; the cross condition says `∅ ∩ B_j nonempty` for `i ≠ j`,
which is false, so `|ι| ≤ 1 = C(b, 0)`. `b = 0` symmetric.
**Not** labelled Bollobás.

Transcribed classical argument (B. Bollobás, *On generalized graphs*,
Acta Math. Acad. Sci. Hungar. 16 (1965) 447–452). Compact form:
Wikipedia *Bollobás theorem (combinatorics)* / two-families theorem.
Sperner / LYM / KK / EKR / Oddtown are different already-in / consumed
theorems, not this claim. No novelty claim. Default no claim.
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option linter.unusedVariables false

open Finset

namespace ProofLab.BollobasTwoFamilies

/-- Pair-family encoding: pairwise disjoint within each pair, and every
left set meets every other right set. **Not** labelled Bollobás. -/
def IsSetPairFamily {α ι : Type*} [DecidableEq α]
    (A B : ι → Finset α) : Prop :=
  (∀ i, Disjoint (A i) (B i)) ∧
  (∀ i j, i ≠ j → ((A i) ∩ (B j)).Nonempty)

/-! ## Level A: empty ι (not labelled Bollobás) -/

/-- Empty index type: `card = 0 ≤ C(a+b, a)`. Glue; **not** labelled
Bollobás. -/
theorem card_eq_zero_le_choose {α ι : Type*} [Fintype α] [Fintype ι]
    [IsEmpty ι] [DecidableEq α] (A B : ι → Finset α) (a b : ℕ) :
    Fintype.card ι ≤ Nat.choose (a + b) a := by
  simp [Fintype.card_eq_zero]

/-- `Fin 0` specialisation of the empty case. Glue; **not** labelled
Bollobás. -/
theorem card_eq_zero_le_choose_fin_zero {α : Type*} [Fintype α]
    [DecidableEq α] (A B : Fin 0 → Finset α) (a b : ℕ) :
    Fintype.card (Fin 0) ≤ Nat.choose (a + b) a :=
  card_eq_zero_le_choose (ι := Fin 0) A B a b

/-! ## Level A: one pair / singleton (not labelled Bollobás) -/

/-- `1 ≤ C(a+b, a)` via `choose_pos` once `a ≤ a+b`. Glue; **not**
labelled Bollobás. -/
theorem one_le_choose (a b : ℕ) : 1 ≤ Nat.choose (a + b) a :=
  Nat.succ_le_of_lt (Nat.choose_pos (Nat.le_add_right a b))

/-- Singleton index: `card = 1 ≤ C(a+b, a)`. Glue; **not** labelled
Bollobás. -/
theorem card_one_le_choose {α ι : Type*} [Fintype α] [Fintype ι]
    [Unique ι] [DecidableEq α] (A B : ι → Finset α) (a b : ℕ)
    (hA : ∀ i, (A i).card = a) (hB : ∀ i, (B i).card = b) :
    Fintype.card ι ≤ Nat.choose (a + b) a := by
  simpa [Fintype.card_unique] using one_le_choose a b

/-- `Fin 1` specialisation of the singleton case. Glue; **not** labelled
Bollobás. -/
theorem card_one_le_choose_fin_one {α : Type*} [Fintype α] [DecidableEq α]
    (A B : Fin 1 → Finset α) (a b : ℕ)
    (hA : ∀ i, (A i).card = a) (hB : ∀ i, (B i).card = b) :
    Fintype.card (Fin 1) ≤ Nat.choose (a + b) a :=
  card_one_le_choose (ι := Fin 1) A B a b hA hB

/-- One pair with `A ∩ B = ∅`: `1 ≤ C(a+b, a)`. Glue; **not** labelled
Bollobás. `Disjoint` is load-bearing in the pin (unused in this
inequality). -/
theorem one_le_choose_of_disjoint {α : Type*} [Fintype α] [DecidableEq α]
    (A B : Finset α) (a b : ℕ) (_h : Disjoint A B)
    (_hA : A.card = a) (_hB : B.card = b) :
    1 ≤ Nat.choose (a + b) a :=
  one_le_choose a b

/-! ## Level A: a = 0 (not labelled Bollobás) -/

/-- If every `A i` is empty, the cross condition forbids two distinct
indices, so `|ι| ≤ 1`. Glue; **not** labelled Bollobás. -/
theorem card_le_one_of_left_card_eq_zero {α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq α] (A B : ι → Finset α)
    (h : IsSetPairFamily A B) (hA : ∀ i, (A i).card = 0) :
    Fintype.card ι ≤ 1 := by
  rw [Fintype.card_le_one_iff]
  intro i j
  by_contra hij
  have hne : ((A i) ∩ (B j)).Nonempty := h.2 i j hij
  have hAi : A i = ∅ := Finset.card_eq_zero.mp (hA i)
  rw [hAi, empty_inter] at hne
  exact Finset.not_nonempty_empty hne

/-- Packaged `a = 0`: `|ι| ≤ C(b, 0) = 1`. Glue; **not** labelled
Bollobás. -/
theorem card_le_choose_of_left_card_eq_zero {α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq α] (A B : ι → Finset α)
    (h : IsSetPairFamily A B) (b : ℕ) (hA : ∀ i, (A i).card = 0)
    (_hB : ∀ i, (B i).card = b) :
    Fintype.card ι ≤ Nat.choose (0 + b) 0 := by
  have hcard : Fintype.card ι ≤ 1 :=
    card_le_one_of_left_card_eq_zero A B h hA
  simpa [Nat.choose_zero_right] using hcard

/-! ## Level A: b = 0 (not labelled Bollobás) -/

/-- If every `B i` is empty, the cross condition forbids two distinct
indices, so `|ι| ≤ 1`. Glue; **not** labelled Bollobás. -/
theorem card_le_one_of_right_card_eq_zero {α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq α] (A B : ι → Finset α)
    (h : IsSetPairFamily A B) (hB : ∀ i, (B i).card = 0) :
    Fintype.card ι ≤ 1 := by
  rw [Fintype.card_le_one_iff]
  intro i j
  by_contra hij
  have hne : ((A i) ∩ (B j)).Nonempty := h.2 i j hij
  have hBj : B j = ∅ := Finset.card_eq_zero.mp (hB j)
  rw [hBj, inter_empty] at hne
  exact Finset.not_nonempty_empty hne

/-- Packaged `b = 0`: `|ι| ≤ C(a, a) = 1`. Glue; **not** labelled
Bollobás. -/
theorem card_le_choose_of_right_card_eq_zero {α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq α] (A B : ι → Finset α)
    (h : IsSetPairFamily A B) (a : ℕ) (hA : ∀ i, (A i).card = a)
    (hB : ∀ i, (B i).card = 0) :
    Fintype.card ι ≤ Nat.choose (a + 0) a := by
  have hcard : Fintype.card ι ≤ 1 :=
    card_le_one_of_right_card_eq_zero A B h hB
  simpa [Nat.add_zero, Nat.choose_self] using hcard

/-
Residual (Level B, **out of this ticket**, not sorry-ed):
  theorem bollobas
      {α ι : Type*} [Fintype α] [Fintype ι]
      [DecidableEq α] [DecidableEq ι]
      (A B : ι → Finset α)
      (h : IsSetPairFamily A B)
      (a b : ℕ)
      (hA : ∀ i, (A i).card = a)
      (hB : ∀ i, (B i).card = b) :
      Fintype.card ι ≤ Nat.choose (a + b) a
Permutation counting on `A_i ∪ B_i` (or on `univ`): a permutation of the
ground set witnesses at most one pair (all of `A_i` before all of `B_i`),
hence `|ι| · a! · b! ≤ (a+b)!`. Do not sorry the namesake. Weighted `ℚ`
form `∑ 1/C(|A_i|+|B_i|, |A_i|) ≤ 1` is residual of this id. Hilton–Milner /
Eventown / Fisher remain residual. Do not re-prove `Nat.choose` / Sperner /
LYM / `kruskal_katona` / `erdos_ko_rado` / `oddtown` / `erdos_rado_sunflower`
/ Sauer–Shelah / `cauchy_binet` / Kirchhoff / `hadamard_det` /
`schwartz_zippel`.
-/

end ProofLab.BollobasTwoFamilies
