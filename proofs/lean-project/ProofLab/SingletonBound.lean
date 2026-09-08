/-
Singleton bound — Level A only (empty / singleton / d=1 / whole-space
min-dist / binary repetition). **Not labelled Singleton.**

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 has `hammingDist` / `hammingNorm` / `Fintype.card` /
`Fin n` and ZERO named Singleton bound / `minimumDistance` /
`LinearCode`. Completing the Level A empty / singleton / `d = 1` /
whole-space min-dist / binary-repetition glue is the gap this ticket
lands. The Level B namesake `singleton_bound` (puncture of `d-1`
coordinates is injective on `C`) is **out of this ticket** and is
**not** sorry-ed. Hamming sphere-packing / Plotkin / MDS /
Reed–Solomon extras are residual.

Pin: `catalog/problems/singleton-bound/STATEMENT.md` (OPE-1147;
Scout OPE-1142 prime; Director OPE-1146). Encoding: Mathlib
`hammingDist` on `Fin n → α`. Zero `sorry`. Do not import `Archive.*`.

This is **not** the Hamming metric (`InformationTheory/Hamming.lean`
L38 / L137) — already Mathlib. **USE `hammingDist`; do not re-prove;
do not cite as Singleton.** This is **not** the Hamming sphere-packing
bound (volume of balls; residual of this id). This is **not** Plotkin /
Gilbert–Varshamov / MacWilliams / Reed–Solomon / Hamming codes.
This is **not** Kraft / Shannon / Huffman. This is **not** a
`LinearCode` library. This is **not** Cauchy–Binet
(`ProofLab/CauchyBinet.lean`, PR #117) — different consumed theorem;
do not revive Level B / Kirchhoff. This is **not** Bollobás
(`ProofLab/BollobasTwoFamilies.lean`, PR #118). Do not re-prime the
consumed mill. Leave OPE-403 alone. Do **not** prove Hamming-bound /
Plotkin / MDS / Reed–Solomon here.

v1 is the combinatorial Singleton inequality only. `1 ≤ d` is
load-bearing (`n + 1 - d` in `ℕ` subtraction). Finite `α` and
`Fin n` are load-bearing. Distinct-pair quantification is
load-bearing (a singleton is allowed and must not crash).

Level A: empty `C`, card `0`. Singleton: vacuous min-dist, bound
holds for any `d`. `d = 1`: right-hand side `|α|^n` is the whole
space. Whole space over `α` with `|α| > 1` and `n > 0` has min-dist
`1` via a one-coordinate flip. Binary repetition of length `n`
over `Fin 2` has min-dist `n`. **Not** labelled Singleton.

Transcribed classical argument (R. C. Singleton, *Maximum distance
q-nary codes*, IEEE Trans. Inform. Theory 10 (1964) 116–118).
Textbook: MacWilliams–Sloane, *The Theory of Error-Correcting Codes*,
Ch. 1. Compact form: Wikipedia *Singleton bound*. Type pin: Mathlib
`hammingDist`. The Hamming metric is a different already-in
definition, not this claim. No novelty claim. Default no claim.
-/
import Mathlib.InformationTheory.Hamming
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic

set_option linter.unusedVariables false

open Finset Function

namespace ProofLab.SingletonBound

/-! ## Encoding (not labelled Singleton) -/

/-- Infimum of `hammingDist` over distinct pairs in `C`. Convention
`n + 1` when `|C| ≤ 1` (no distinct pair). **Not** labelled
Singleton. Reuses Mathlib `hammingDist`; does **not** re-prove the
Hamming metric. -/
def minDist {n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (C : Finset (Fin n → α)) : ℕ :=
  if h : C.card ≤ 1 then n + 1
  else
    (C.offDiag.image fun p => hammingDist p.1 p.2).min' <| by
      have hC : 1 < C.card := Nat.lt_of_not_le h
      obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hC
      refine (image_nonempty).2 ?_
      exact ⟨(x, y), mem_offDiag.2 ⟨hx, hy, hxy⟩⟩

/-- Binary repetition code of length `n` over `Fin 2`: the two
constant words. Glue; **not** labelled Singleton. -/
def binaryRepetition (n : ℕ) : Finset (Fin n → Fin 2) :=
  {fun _ => 0, fun _ => 1}

/-! ## Level A: empty / singleton (not labelled Singleton) -/

/-- Vacuous min-dist convention: `|C| ≤ 1` ⇒ `minDist = n + 1`.
Glue; **not** labelled Singleton. -/
theorem minDist_of_card_le_one {n : ℕ} {α : Type*} [Fintype α]
    [DecidableEq α] (C : Finset (Fin n → α)) (hC : C.card ≤ 1) :
    minDist C = n + 1 :=
  dif_pos hC

/-- Empty code: `minDist = n + 1`. Glue; **not** labelled Singleton. -/
theorem minDist_empty {n : ℕ} {α : Type*} [Fintype α] [DecidableEq α] :
    minDist (∅ : Finset (Fin n → α)) = n + 1 :=
  minDist_of_card_le_one _ (by simp)

/-- Singleton code: `minDist = n + 1`. Glue; **not** labelled
Singleton. Distinct-pair quantification does not crash. -/
theorem minDist_singleton {n : ℕ} {α : Type*} [Fintype α]
    [DecidableEq α] (x : Fin n → α) :
    minDist ({x} : Finset (Fin n → α)) = n + 1 :=
  minDist_of_card_le_one _ (by simp)

/-- Empty `C`: card `0` is ≤ any power. Glue; **not** labelled
Singleton. -/
theorem card_empty_le_pow {n : ℕ} {α : Type*} [Fintype α]
    [DecidableEq α] {d : ℕ} (_hd : 1 ≤ d) :
    (∅ : Finset (Fin n → α)).card ≤ Fintype.card α ^ (n + 1 - d) := by
  simp

/-- If a codeword exists, `|α|^(n+1-d) ≥ 1`. Empty alphabet is
possible only for `n = 0`, where the exponent collapses to `0`.
Glue; **not** labelled Singleton. -/
theorem one_le_pow_of_nonempty {n : ℕ} {α : Type*} [Fintype α]
    [DecidableEq α] (C : Finset (Fin n → α)) {d : ℕ} (hd : 1 ≤ d)
    (hC : C.Nonempty) : 1 ≤ Fintype.card α ^ (n + 1 - d) := by
  by_cases hα : Fintype.card α = 0
  · have hn : n = 0 := by
      by_contra hn0
      have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
      haveI : IsEmpty α := Fintype.card_eq_zero_iff.mp hα
      obtain ⟨x, _hx⟩ := hC
      exact isEmptyElim (x ⟨0, hnpos⟩)
    subst hn
    have : 0 + 1 - d = 0 := Nat.sub_eq_zero_of_le hd
    rw [this, pow_zero]
  · exact Nat.one_le_pow (n + 1 - d) _ (Nat.pos_of_ne_zero hα)

/-- `|C| ≤ 1` (vacuous min-dist): the bound holds for any `d ≥ 1`.
Glue; **not** labelled Singleton. -/
theorem card_le_pow_of_card_le_one {n : ℕ} {α : Type*} [Fintype α]
    [DecidableEq α] (C : Finset (Fin n → α)) {d : ℕ} (hd : 1 ≤ d)
    (hC : C.card ≤ 1) :
    C.card ≤ Fintype.card α ^ (n + 1 - d) := by
  rcases Nat.eq_zero_or_pos C.card with h0 | hpos
  · simp [h0]
  · have h1 : C.card = 1 := le_antisymm hC (Nat.succ_le_of_lt hpos)
    have hne : C.Nonempty := card_pos.mp hpos
    have hpow := one_le_pow_of_nonempty C hd hne
    rw [h1]
    exact hpow

/-- Singleton: vacuous min-dist, bound holds for any `d ≥ 1`. Glue;
**not** labelled Singleton. -/
theorem card_singleton_le_pow {n : ℕ} {α : Type*} [Fintype α]
    [DecidableEq α] (x : Fin n → α) {d : ℕ} (hd : 1 ≤ d) :
    ({x} : Finset (Fin n → α)).card ≤ Fintype.card α ^ (n + 1 - d) :=
  card_le_pow_of_card_le_one _ hd (by simp)

/-- Vacuous min-dist hypothesis on `|C| ≤ 1`: every distinct pair
(there are none) has distance ≥ `d`. Glue; **not** labelled
Singleton. -/
theorem min_dist_hyp_of_card_le_one {n : ℕ} {α : Type*} [Fintype α]
    [DecidableEq α] (C : Finset (Fin n → α)) {d : ℕ}
    (hC : C.card ≤ 1) :
    ∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ hammingDist x y := by
  intro x hx y hy hxy
  have : x = y := card_le_one_iff.mp hC hx hy
  exact (hxy this).elim

/-! ## Level A: d = 1 (not labelled Singleton) -/

/-- `d = 1`: right-hand side is `|α|^n`, the whole space. Every
finite code embeds into `Fin n → α`. Glue; **not** labelled
Singleton. The min-dist hypothesis is automatic (`hammingDist_pos`). -/
theorem card_le_pow_of_d_eq_one {n : ℕ} {α : Type*} [Fintype α]
    [DecidableEq α] (C : Finset (Fin n → α))
    (_hmin : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → 1 ≤ hammingDist x y) :
    C.card ≤ Fintype.card α ^ (n + 1 - 1) := by
  rw [Nat.add_sub_cancel]
  have hle : C.card ≤ Fintype.card (Fin n → α) := card_le_univ C
  have hfun : Fintype.card (Fin n → α) = Fintype.card α ^ n := by
    rw [Fintype.card_fun, Fintype.card_fin]
  rwa [← hfun]

/-- Automatic `d = 1` min-dist hypothesis (Mathlib `hammingDist_pos`).
**USE** the metric; do **not** re-prove it. Glue; **not** labelled
Singleton. -/
theorem one_le_hammingDist_of_ne {n : ℕ} {α : Type*} [DecidableEq α]
    {x y : Fin n → α} (h : x ≠ y) : 1 ≤ hammingDist x y :=
  Nat.succ_le_of_lt (hammingDist_pos.mpr h)

/-- Packaged `d = 1` bound with the automatic hypothesis. Glue;
**not** labelled Singleton. -/
theorem card_le_pow_d_one {n : ℕ} {α : Type*} [Fintype α]
    [DecidableEq α] (C : Finset (Fin n → α)) :
    C.card ≤ Fintype.card α ^ (n + 1 - 1) :=
  card_le_pow_of_d_eq_one C fun _ _ _ _ hxy =>
    one_le_hammingDist_of_ne hxy

/-! ## Level A: whole-space min-dist (not labelled Singleton) -/

/-- Flipping one coordinate where the letters differ yields Hamming
distance 1. **USE** Mathlib `hammingDist`; do **not** re-prove the
metric. Glue; **not** labelled Singleton. -/
theorem hammingDist_update_single {n : ℕ} {α : Type*} [DecidableEq α]
    (x : Fin n → α) (i : Fin n) (b : α) (h : x i ≠ b) :
    hammingDist x (update x i b) = 1 := by
  unfold hammingDist
  have : (univ.filter fun j => x j ≠ update x i b j) = {i} := by
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · intro hj
      by_contra hji
      rw [update_noteq hji] at hj
      exact hj rfl
    · intro hji
      rw [hji, update_same]
      exact h
  rw [this, card_singleton]

/-- Whole space over `α` with `|α| > 1` and `n > 0` has min-dist 1
via a one-coordinate flip. Glue; **not** labelled Singleton. -/
theorem minDist_univ_eq_one {n : ℕ} {α : Type*} [Fintype α]
    [DecidableEq α] (hα : 1 < Fintype.card α) (hn : 0 < n) :
    minDist (univ : Finset (Fin n → α)) = 1 := by
  haveI : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.mp hα
  obtain ⟨a, b, hab⟩ := exists_pair_ne α
  have i : Fin n := ⟨0, hn⟩
  let x : Fin n → α := fun _ => a
  let y : Fin n → α := update x i b
  have hxy : x ≠ y := by
    intro h
    have : x i = y i := congrFun h i
    simp [x, y, update_same] at this
    exact hab this
  have hdist : hammingDist x y = 1 := by
    simpa [x, y] using hammingDist_update_single x i b (by simp [x, hab])
  have hcard : 1 < (univ : Finset (Fin n → α)).card := by
    have hfun : (univ : Finset (Fin n → α)).card = Fintype.card α ^ n := by
      rw [card_univ, Fintype.card_fun, Fintype.card_fin]
    rw [hfun]
    exact one_lt_pow hα (Nat.pos_iff_ne_zero.mp hn)
  set s := (univ : Finset (Fin n → α)).offDiag.image fun p => hammingDist p.1 p.2
  have hs : s.Nonempty := by
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hcard
    exact (image_nonempty).2 ⟨(u, v), mem_offDiag.2 ⟨hu, hv, huv⟩⟩
  have hmin : minDist (univ : Finset (Fin n → α)) = s.min' hs := by
    unfold minDist
    rw [dif_neg (not_le.mpr hcard)]
  rw [hmin]
  apply le_antisymm
  · exact Finset.min'_le s 1
      (mem_image.2 ⟨(x, y), mem_offDiag.2 ⟨mem_univ x, mem_univ y, hxy⟩, hdist⟩)
  · exact Finset.le_min' s hs 1 (fun d hd => by
      obtain ⟨⟨u, v⟩, huv, rfl⟩ := mem_image.mp hd
      exact one_le_hammingDist_of_ne (mem_offDiag.mp huv).2.2)

/-! ## Level A: binary repetition (not labelled Singleton) -/

/-- Constant words over distinct letters differ in every coordinate.
**USE** Mathlib `hammingDist`. Glue; **not** labelled Singleton. -/
theorem hammingDist_const_ne {n : ℕ} {α : Type*} [DecidableEq α]
    {a b : α} (h : a ≠ b) :
    hammingDist (fun _ : Fin n => a) (fun _ => b) = n := by
  unfold hammingDist
  have : (univ.filter fun _ : Fin n => a ≠ b) = univ := by
    exact filter_true_of_mem fun _ _ => h
  rw [this, card_univ, Fintype.card_fin]

/-- The two binary constants are distinct for `n > 0`. Glue; **not**
labelled Singleton. -/
theorem binaryRepetition_const_ne {n : ℕ} (hn : 0 < n) :
    (fun _ : Fin n => (0 : Fin 2)) ≠ (fun _ => 1) := by
  intro h
  have : (0 : Fin 2) = 1 := congrFun h ⟨0, hn⟩
  exact zero_ne_one this

/-- Binary repetition of length `n > 0` has two codewords. Glue;
**not** labelled Singleton. -/
theorem binaryRepetition_card {n : ℕ} (hn : 0 < n) :
    (binaryRepetition n).card = 2 := by
  simp [binaryRepetition, card_insert_of_not_mem, binaryRepetition_const_ne hn]

/-- Binary repetition of length `n > 0` has min-dist `n`. Glue;
**not** labelled Singleton. -/
theorem minDist_binaryRepetition {n : ℕ} (hn : 0 < n) :
    minDist (binaryRepetition n) = n := by
  have hne := binaryRepetition_const_ne hn
  have hcard : 1 < (binaryRepetition n).card := by
    rw [binaryRepetition_card hn]
    exact Nat.one_lt_succ_succ 0
  have hdist :
      hammingDist (fun _ : Fin n => (0 : Fin 2)) (fun _ => 1) = n :=
    hammingDist_const_ne (by decide : (0 : Fin 2) ≠ 1)
  set s := (binaryRepetition n).offDiag.image fun p => hammingDist p.1 p.2
  have hs : s.Nonempty := by
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hcard
    exact (image_nonempty).2 ⟨(u, v), mem_offDiag.2 ⟨hu, hv, huv⟩⟩
  have hmin' : minDist (binaryRepetition n) = s.min' hs := by
    unfold minDist
    rw [dif_neg (not_le.mpr hcard)]
  rw [hmin']
  have hx : (fun _ : Fin n => (0 : Fin 2)) ∈ binaryRepetition n := by
    simp [binaryRepetition]
  have hy : (fun _ : Fin n => (1 : Fin 2)) ∈ binaryRepetition n := by
    simp [binaryRepetition]
  apply le_antisymm
  · exact Finset.min'_le s n
      (mem_image.2 ⟨(fun _ => 0, fun _ => 1), mem_offDiag.2 ⟨hx, hy, hne⟩, hdist⟩)
  · exact Finset.le_min' s hs n (fun d hd => by
      obtain ⟨⟨u, v⟩, huv, rfl⟩ := mem_image.mp hd
      have huv' := mem_offDiag.mp huv
      have hu := huv'.1
      have hv := huv'.2.1
      have hne' : u ≠ v := huv'.2.2
      have hu' : u = (fun _ => 0) ∨ u = (fun _ => 1) := by
        simpa [binaryRepetition, mem_insert, mem_singleton] using hu
      have hv' : v = (fun _ => 0) ∨ v = (fun _ => 1) := by
        simpa [binaryRepetition, mem_insert, mem_singleton] using hv
      rcases hu' with hu0 | hu1 <;> rcases hv' with hv0 | hv1
      · exact (hne' (hu0.trans hv0.symm)).elim
      · subst hu0; subst hv1
        rw [hdist]
      · subst hu1; subst hv0
        rw [hammingDist_comm, hdist]
      · exact (hne' (hu1.trans hv1.symm)).elim)

/-
Residual (Level B, **out of this ticket**, not sorry-ed):
  theorem singleton_bound
      {n : ℕ} {α : Type*}
      [Fintype α] [DecidableEq α]
      (C : Finset (Fin n → α))
      {d : ℕ} (hd : 1 ≤ d)
      (hmin : ∀ x ∈ C, ∀ y ∈ C, x ≠ y →
        d ≤ hammingDist x y) :
      C.card ≤ Fintype.card α ^ (n + 1 - d)
Puncturing `d-1` coordinates is injective on `C` (two distinct
codewords differ in ≥ `d` places, so they still differ after dropping
`d-1` coordinates). Hence `|C| ≤ |α|^{n-(d-1)}`. Do not sorry the
namesake. Hamming sphere-packing / Plotkin / MDS / Reed–Solomon /
MacWilliams remain residual of this id. Do not re-prove `hammingDist`
/ `hammingNorm` / `Fintype.card`. Do not prove Hamming-bound /
Plotkin / GV / `cauchy_binet` / Kirchhoff / `bollobas` /
`hadamard_det` / `schwartz_zippel` / hook-length.
-/

end ProofLab.SingletonBound
