/-
Hook-length formula — Level A only (empty / one-cell / one-row /
one-column). **Not labelled FRT / hook-length.**

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 has `YoungDiagram` / `rowLen` / `colLen` /
`SemistandardYoungTableau` / `Nat.factorial` and ZERO named
hook-length / `hookLength` / `HookLength`. Completing the Level A
empty / one-cell / one-row / one-column glue is the gap this ticket
lands. The Level B namesake `hook_length` (FRT / hook-walk / GNW)
is **out of this ticket** and is **not** sorry-ed. Catalan 2-row /
RSK / hook-content extras are residual.

Pin: `catalog/problems/hook-length/STATEMENT.md` (OPE-1152;
Scout OPE-1142 leftover; Director OPE-1151). Encoding: Mathlib
`YoungDiagram` + SSYT special case + `factorial`. Zero `sorry`.
Do not import `Archive.*`.

This is **not** `YoungDiagram` / `rowLen` / `colLen`
(`Combinatorics/Young/YoungDiagram.lean`) — already Mathlib.
**USE them as glue; do not re-prove; do not cite as hook-length.**
This is **not** `SemistandardYoungTableau` (already the filling
type; SYT is the bijective-`1..n` special case, encoded not
re-proved). This is **not** Catalan
(`catalan_eq_centralBinom_div`); the 2-row `(n,n)` corollary is
**out of this ticket**. This is **not** RSK / Schensted /
Littlewood–Richardson / Jacobi–Trudi / hook-content. This is
**not** Singleton (`ProofLab/SingletonBound.lean`, PR #120).
This is **not** Cauchy–Binet (#117) / Bollobás (#118) /
Stirling-B leftover. Do not re-prime the consumed mill. Leave
OPE-403 alone. Do **not** prove Catalan / RSK / hook-content /
singleton_bound / Hamming-bound / Plotkin here.

v1 is the SYT count identity only. `c ∈ μ` is load-bearing for
the hook (`ℕ` subtraction). `rowLen` / `colLen` anti-monotonicity
is load-bearing for `hook ≥ 1` on cells. Finite `μ.card` is
load-bearing.

Level A: empty `μ`, `0! = 1`, empty product `1`, one empty
tableau. One cell: hook `1`, `1!/1 = 1`. One-row `(n)`: cells
`(0,j)` have hook `n-j`; product `n!`; unique SYT is `1,2,…,n`
left to right. One-column symmetric. **Not** labelled
hook-length.

Transcribed classical argument (J. S. Frame, G. de B. Robinson,
R. M. Thrall, *The hook graphs of the symmetric group*, Canad. J.
Math. 6 (1954) 316–324). Textbook: Stanley, *Enumerative
Combinatorics* vol. 2, §7.21. Compact form: Wikipedia *Hook
length formula*. Type pin: Mathlib `YoungDiagram` / `rowLen` /
`colLen` / `factorial`. Catalan is a different already-in
theorem, not this claim. No novelty claim. Default no claim.
-/
import Mathlib.Combinatorics.Young.SemistandardTableau
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Tactic

set_option linter.unusedVariables false

open Finset
open YoungDiagram

namespace ProofLab.HookLength

/-! ## Encoding (not labelled hook-length) -/

/-- Hook of a cell `(i, j)`: arm + leg + 1. Membership is
load-bearing (`ℕ` subtraction underflows off the diagram).
**Not** labelled hook-length. Reuses Mathlib `rowLen` / `colLen`;
does **not** re-prove Young diagrams. -/
def hook (μ : YoungDiagram) (c : ℕ × ℕ) (_hc : c ∈ μ) : ℕ :=
  (μ.rowLen c.1 - c.2) + (μ.colLen c.2 - c.1) - 1

/-- Product of hooks over the cells of `μ`. Glue; **not** labelled
hook-length. -/
def hookProduct (μ : YoungDiagram) : ℕ :=
  μ.cells.prod fun c => if hc : c ∈ μ then hook μ c hc else 1

/-- SYT = SSYT whose entries on `μ.cells` are a bijection onto
`Finset.Icc 1 μ.card`. Encode; do **not** re-prove SSYT.
**Not** labelled hook-length. -/
def IsStandard {μ : YoungDiagram} (T : SemistandardYoungTableau μ) : Prop :=
  μ.cells.image (fun c => T c.1 c.2) = Icc 1 μ.card

/-- Standard Young tableau of shape `μ`. Glue; **not** labelled
hook-length. -/
structure StandardYoungTableau (μ : YoungDiagram) extends
    SemistandardYoungTableau μ where
  standard : IsStandard toSemistandardYoungTableau

namespace StandardYoungTableau

theorem eq_of_ssyt_eq {μ : YoungDiagram} {T T' : StandardYoungTableau μ}
    (h : T.toSemistandardYoungTableau = T'.toSemistandardYoungTableau) :
    T = T' := by
  cases T
  cases T'
  congr

@[ext]
theorem ext {μ : YoungDiagram} {T T' : StandardYoungTableau μ}
    (h : ∀ i j, T.entry i j = T'.entry i j) : T = T' :=
  eq_of_ssyt_eq (SemistandardYoungTableau.ext h)

end StandardYoungTableau

/-- One-row diagram of length `n` (empty when `n = 0`). Glue;
**not** labelled hook-length. -/
def oneRow (n : ℕ) : YoungDiagram :=
  ofRowLens [n] (by simp [List.Sorted, List.Pairwise])

/-- One-column diagram of height `n` (transpose of one-row). Glue;
**not** labelled hook-length. -/
def oneCol (n : ℕ) : YoungDiagram := (oneRow n).transpose

/-- One-cell diagram. Glue; **not** labelled hook-length. -/
abbrev oneCell : YoungDiagram := oneRow 1

/-! ## Hook positivity (anti-monotonicity is load-bearing) -/

/-- On a cell, arm ≥ 1 and leg ≥ 1, so hook ≥ 1. Glue; **not**
labelled hook-length. -/
theorem one_le_hook (μ : YoungDiagram) (c : ℕ × ℕ) (hc : c ∈ μ) :
    1 ≤ hook μ c hc := by
  have hj : c.2 < μ.rowLen c.1 := mem_iff_lt_rowLen.mp hc
  have hi : c.1 < μ.colLen c.2 := mem_iff_lt_colLen.mp hc
  have ha : 1 ≤ μ.rowLen c.1 - c.2 := Nat.succ_le_iff.mpr (Nat.sub_pos_of_lt hj)
  have hb : 1 ≤ μ.colLen c.2 - c.1 := Nat.succ_le_iff.mpr (Nat.sub_pos_of_lt hi)
  unfold hook
  have h2 : 2 ≤ (μ.rowLen c.1 - c.2) + (μ.colLen c.2 - c.1) :=
    add_le_add ha hb
  exact Nat.le_sub_of_add_le (by simpa using h2)

/-! ## Shape lemmas (one-row / one-column) -/

theorem mem_oneRow {n i j : ℕ} : (i, j) ∈ oneRow n ↔ i = 0 ∧ j < n := by
  constructor
  · intro h
    obtain ⟨hi, hj⟩ := mem_ofRowLens.mp h
    have hi0 : i = 0 := Nat.lt_one_iff.mp (by simpa using hi)
    subst hi0
    refine ⟨rfl, ?_⟩
    simpa using hj
  · rintro ⟨rfl, hj⟩
    refine mem_ofRowLens.mpr ⟨?_, ?_⟩
    · simp
    · simpa using hj

theorem oneRow_cells (n : ℕ) :
    (oneRow n).cells = ({0} : Finset ℕ) ×ˢ range n := by
  ext ⟨i, j⟩
  constructor
  · intro h
    have h' : (i, j) ∈ oneRow n := by rwa [mem_cells] at h
    have h'' := mem_oneRow.mp h'
    simp [mem_product, mem_singleton, mem_range, h''.1, h''.2]
  · intro h
    simp only [mem_product, mem_singleton, mem_range] at h
    rwa [mem_cells, mem_oneRow]

theorem oneRow_card (n : ℕ) : (oneRow n).card = n := by
  simp [card, oneRow_cells]

theorem oneRow_rowLen (n : ℕ) : (oneRow n).rowLen 0 = n := by
  simpa using rowLen_ofRowLens (w := [n]) (hw := by simp [List.Sorted, List.Pairwise])
    (⟨0, by simp⟩ : Fin [n].length)

theorem oneRow_colLen {n j : ℕ} (hj : j < n) : (oneRow n).colLen j = 1 := by
  have hmem : (0, j) ∈ oneRow n := mem_oneRow.2 ⟨rfl, hj⟩
  have hpos : 0 < (oneRow n).colLen j := mem_iff_lt_colLen.mp hmem
  have hnmem : (1, j) ∉ oneRow n := by
    intro h
    exact one_ne_zero (mem_oneRow.mp h).1
  have hle : (oneRow n).colLen j ≤ 1 := by
    exact Nat.not_lt.mp (mt mem_iff_lt_colLen.mpr hnmem)
  exact le_antisymm hle (Nat.succ_le_of_lt hpos)

theorem mem_oneCol {n i j : ℕ} : (i, j) ∈ oneCol n ↔ j = 0 ∧ i < n := by
  simp [oneCol, mem_transpose, mem_oneRow, and_comm]

theorem oneCol_cells (n : ℕ) :
    (oneCol n).cells = range n ×ˢ ({0} : Finset ℕ) := by
  ext ⟨i, j⟩
  constructor
  · intro h
    have h' : (i, j) ∈ oneCol n := by rwa [mem_cells] at h
    have h'' := mem_oneCol.mp h'
    simp [mem_product, mem_singleton, mem_range, h''.1, h''.2]
  · intro h
    simp only [mem_product, mem_singleton, mem_range] at h
    rw [mem_cells, mem_oneCol]
    exact ⟨h.2, h.1⟩

theorem oneCol_card (n : ℕ) : (oneCol n).card = n := by
  simp [card, oneCol_cells]

theorem oneCol_rowLen {n i : ℕ} (hi : i < n) : (oneCol n).rowLen i = 1 := by
  have hmem : (i, 0) ∈ oneCol n := mem_oneCol.2 ⟨rfl, hi⟩
  have hpos : 0 < (oneCol n).rowLen i := mem_iff_lt_rowLen.mp hmem
  have hnmem : (i, 1) ∉ oneCol n := by
    intro h
    exact one_ne_zero (mem_oneCol.mp h).1
  have hle : (oneCol n).rowLen i ≤ 1 :=
    Nat.not_lt.mp (mt mem_iff_lt_rowLen.mpr hnmem)
  exact le_antisymm hle (Nat.succ_le_of_lt hpos)

theorem oneCol_colLen (n : ℕ) : (oneCol n).colLen 0 = n := by
  simpa [oneCol, colLen_transpose] using oneRow_rowLen n

/-! ## Level A: empty diagram (not labelled hook-length) -/

theorem card_bot : (⊥ : YoungDiagram).card = 0 := by
  simp [card, cells_bot]

theorem hookProduct_bot : hookProduct (⊥ : YoungDiagram) = 1 := by
  simp [hookProduct, cells_bot]

theorem factorial_card_bot :
    Nat.factorial (⊥ : YoungDiagram).card = 1 := by
  simp [card_bot]

theorem ssyt_bot_eq (T : SemistandardYoungTableau (⊥ : YoungDiagram)) :
    T = SemistandardYoungTableau.highestWeight (⊥ : YoungDiagram) := by
  ext i j
  have h : (i, j) ∉ (⊥ : YoungDiagram) := not_mem_bot _
  simp [T.zeros h]

theorem isStandard_bot (T : SemistandardYoungTableau (⊥ : YoungDiagram)) :
    IsStandard T := by
  unfold IsStandard
  simp [cells_bot, card, Icc_eq_empty_iff]

def emptyStandard : StandardYoungTableau (⊥ : YoungDiagram) where
  toSemistandardYoungTableau := SemistandardYoungTableau.highestWeight ⊥
  standard := isStandard_bot _

noncomputable instance : Unique (StandardYoungTableau (⊥ : YoungDiagram)) where
  default := emptyStandard
  uniq T := by
    apply StandardYoungTableau.eq_of_ssyt_eq
    exact ssyt_bot_eq _

noncomputable instance {μ : YoungDiagram} [Unique (StandardYoungTableau μ)] :
    Fintype (StandardYoungTableau μ) :=
  Fintype.ofSubsingleton default

theorem card_syt_bot :
    Fintype.card (StandardYoungTableau (⊥ : YoungDiagram)) = 1 :=
  Fintype.card_unique

/-- Empty diagram: `1 * 1 = 0!`. Glue; **not** labelled hook-length. -/
theorem card_mul_hookProduct_bot :
    Fintype.card (StandardYoungTableau (⊥ : YoungDiagram)) *
      hookProduct (⊥ : YoungDiagram) =
    Nat.factorial (⊥ : YoungDiagram).card := by
  simp [card_syt_bot, hookProduct_bot, factorial_card_bot]

/-! ## Hook values on one-row / one-column -/

theorem hook_oneRow {n j : ℕ} (hj : j < n) (hc : (0, j) ∈ oneRow n) :
    hook (oneRow n) (0, j) hc = n - j := by
  unfold hook
  simp [oneRow_rowLen, oneRow_colLen hj]

theorem hook_oneCol {n i : ℕ} (hi : i < n) (hc : (i, 0) ∈ oneCol n) :
    hook (oneCol n) (i, 0) hc = n - i := by
  unfold hook
  simp [oneCol_rowLen hi, oneCol_colLen]

/-- `(range n).prod (n - ·) = n!`. Glue; **not** labelled hook-length. -/
theorem prod_range_sub_eq_factorial (n : ℕ) :
    (range n).prod (fun j => n - j) = n.factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [prod_range_succ']
    simp_rw [Nat.succ_sub_succ]
    simp [ih, Nat.factorial_succ, mul_comm]

theorem hookProduct_oneRow (n : ℕ) :
    hookProduct (oneRow n) = n.factorial := by
  unfold hookProduct
  rw [oneRow_cells, prod_product, prod_singleton]
  have hfun : ∀ j ∈ range n,
      (if hc : (0, j) ∈ oneRow n then hook (oneRow n) (0, j) hc else 1) =
        n - j := by
    intro j hj
    have hmem : (0, j) ∈ oneRow n := mem_oneRow.2 ⟨rfl, mem_range.mp hj⟩
    rw [dif_pos hmem]
    exact hook_oneRow (mem_range.mp hj) hmem
  rw [prod_congr rfl hfun]
  exact prod_range_sub_eq_factorial n

theorem hookProduct_oneCol (n : ℕ) :
    hookProduct (oneCol n) = n.factorial := by
  unfold hookProduct
  rw [oneCol_cells, prod_product]
  simp_rw [prod_singleton]
  have hfun : ∀ i ∈ range n,
      (if hc : (i, 0) ∈ oneCol n then hook (oneCol n) (i, 0) hc else 1) =
        n - i := by
    intro i hi
    have hmem : (i, 0) ∈ oneCol n := mem_oneCol.2 ⟨rfl, mem_range.mp hi⟩
    rw [dif_pos hmem]
    exact hook_oneCol (mem_range.mp hi) hmem
  rw [prod_congr rfl hfun]
  exact prod_range_sub_eq_factorial n

/-! ## Level A: one-cell (not labelled hook-length) -/

theorem oneCell_card : oneCell.card = 1 := oneRow_card 1

theorem hook_oneCell (hc : (0, 0) ∈ oneCell) :
    hook oneCell (0, 0) hc = 1 :=
  hook_oneRow (by decide : 0 < 1) hc

theorem hookProduct_oneCell : hookProduct oneCell = 1 := by
  simpa using hookProduct_oneRow 1

/-! ## Standard fillings of one-row / one-column -/

/-- Unique increasing filling of a one-row diagram: `1,2,…,n` left
to right. Glue; **not** labelled hook-length. -/
def oneRowTableau (n : ℕ) : SemistandardYoungTableau (oneRow n) where
  entry i j := if (i, j) ∈ oneRow n then j + 1 else 0
  row_weak' := by
    intro i j1 j2 hj hcell
    have ⟨hi, hj2⟩ := mem_oneRow.mp hcell
    subst hi
    have hj1 : j1 < n := hj.trans hj2
    have hmem1 : (0, j1) ∈ oneRow n := mem_oneRow.2 ⟨rfl, hj1⟩
    simp [hcell, hmem1, Nat.succ_le_succ (le_of_lt hj)]
  col_strict' := by
    intro i1 i2 j hi hcell
    have ⟨hi2, _⟩ := mem_oneRow.mp hcell
    exact (Nat.not_lt_zero i1 (hi2 ▸ hi)).elim
  zeros' := fun h => if_neg h

@[simp]
theorem oneRowTableau_apply (n i j : ℕ) :
    oneRowTableau n i j = if (i, j) ∈ oneRow n then j + 1 else 0 :=
  rfl

theorem oneRowTableau_standard (n : ℕ) : IsStandard (oneRowTableau n) := by
  unfold IsStandard
  rw [oneRow_cells, oneRow_card]
  ext x
  constructor
  · intro hx
    rcases mem_image.mp hx with ⟨⟨i, j⟩, hj, rfl⟩
    simp only [mem_product, mem_singleton, mem_range] at hj
    rw [oneRowTableau_apply, if_pos (mem_oneRow.2 ⟨hj.1, hj.2⟩)]
    exact mem_Icc.2 ⟨Nat.succ_le_succ (Nat.zero_le j), Nat.succ_le_of_lt hj.2⟩
  · intro hx
    rcases mem_Icc.mp hx with ⟨hx1, hx2⟩
    have hj : x - 1 < n := by omega
    refine mem_image.2 ⟨(0, x - 1), ?_, ?_⟩
    · simp [mem_product, mem_singleton, mem_range, hj]
    · rw [oneRowTableau_apply, if_pos (mem_oneRow.2 ⟨rfl, hj⟩), Nat.sub_add_cancel hx1]

def oneRowStandard (n : ℕ) : StandardYoungTableau (oneRow n) where
  toSemistandardYoungTableau := oneRowTableau n
  standard := oneRowTableau_standard n

/-- Unique increasing filling of a one-column diagram: `1,2,…,n`
top to bottom. Glue; **not** labelled hook-length. -/
def oneColTableau (n : ℕ) : SemistandardYoungTableau (oneCol n) where
  entry i j := if (i, j) ∈ oneCol n then i + 1 else 0
  row_weak' := by
    intro i j1 j2 hj hcell
    have ⟨hj2, _⟩ := mem_oneCol.mp hcell
    exact (Nat.not_lt_zero j1 (hj2 ▸ hj)).elim
  col_strict' := by
    intro i1 i2 j hi hcell
    have ⟨hj0, hi2⟩ := mem_oneCol.mp hcell
    subst hj0
    have hi1 : i1 < n := hi.trans hi2
    have hmem1 : (i1, 0) ∈ oneCol n := mem_oneCol.2 ⟨rfl, hi1⟩
    simp [hcell, hmem1, hi]
  zeros' := fun h => if_neg h

@[simp]
theorem oneColTableau_apply (n i j : ℕ) :
    oneColTableau n i j = if (i, j) ∈ oneCol n then i + 1 else 0 :=
  rfl

theorem oneColTableau_standard (n : ℕ) : IsStandard (oneColTableau n) := by
  unfold IsStandard
  rw [oneCol_cells, oneCol_card]
  ext x
  constructor
  · intro hx
    rcases mem_image.mp hx with ⟨⟨i, j⟩, hj, rfl⟩
    simp only [mem_product, mem_singleton, mem_range] at hj
    rw [oneColTableau_apply, if_pos (mem_oneCol.2 ⟨hj.2, hj.1⟩)]
    exact mem_Icc.2 ⟨Nat.succ_le_succ (Nat.zero_le i), Nat.succ_le_of_lt hj.1⟩
  · intro hx
    rcases mem_Icc.mp hx with ⟨hx1, hx2⟩
    have hi : x - 1 < n := by omega
    refine mem_image.2 ⟨(x - 1, 0), ?_, ?_⟩
    · simp [mem_product, mem_singleton, mem_range, hi]
    · rw [oneColTableau_apply, if_pos (mem_oneCol.2 ⟨rfl, hi⟩), Nat.sub_add_cancel hx1]

def oneColStandard (n : ℕ) : StandardYoungTableau (oneCol n) where
  toSemistandardYoungTableau := oneColTableau n
  standard := oneColTableau_standard n

/-! ## Uniqueness of one-row / one-column SYT -/

theorem isStandard_injOn {μ : YoungDiagram} {T : SemistandardYoungTableau μ}
    (h : IsStandard T) :
    Set.InjOn (fun c : ℕ × ℕ => T c.1 c.2) μ.cells := by
  have hcard : (μ.cells.image fun c => T c.1 c.2).card = μ.cells.card := by
    rw [h, card]
    simp [Nat.card_Icc]
  exact (card_image_iff).mp hcard

/-- A strictly increasing `n`-tuple in `Icc 1 n` is `1,2,…,n`. Glue;
**not** labelled hook-length. -/
theorem chain_eq_succ (n : ℕ) (a : ℕ → ℕ)
    (hIcc : ∀ j, j < n → a j ∈ Icc 1 n)
    (hlt : ∀ j, j + 1 < n → a j < a (j + 1)) :
    ∀ j, j < n → a j = j + 1 := by
  have hge : ∀ j, j < n → j + 1 ≤ a j := by
    intro j hj
    induction' j with j ih
    · exact (mem_Icc.mp (hIcc 0 hj)).1
    · have hj' : j < n := Nat.lt_of_succ_lt hj
      have hs : j + 1 < n := hj
      exact Nat.succ_le_of_lt <| lt_of_le_of_lt (ih hj') (hlt j hs)
  have hstep : ∀ (j k : ℕ), j + k < n → a j + k ≤ a (j + k) := by
    intro j k
    induction' k with k ih
    · intro; simp
    · intro hjk
      have ih' : a j + k ≤ a (j + k) := ih (Nat.lt_of_succ_lt hjk)
      have hinc : a (j + k) < a (j + k + 1) := hlt (j + k) hjk
      exact Nat.succ_le_of_lt (lt_of_le_of_lt ih' hinc)
  intro j hj
  refine le_antisymm ?_ (hge j hj)
  cases' n with m
  · exact (Nat.not_lt_zero _ hj).elim
  · have hm : m < m + 1 := Nat.lt_succ_self m
    have an : a m ≤ m + 1 := (mem_Icc.mp (hIcc m hm)).2
    have hjle : j ≤ m := Nat.lt_succ_iff.mp hj
    have hk : j + (m - j) < m + 1 := by
      simp [Nat.add_sub_of_le hjle]
    have hsum : a j + (m - j) ≤ a m := by
      simpa [Nat.add_sub_of_le hjle] using hstep j (m - j) hk
    have hsum' : a j + (m - j) ≤ m + 1 := hsum.trans an
    have : a j ≤ (m + 1) - (m - j) := Nat.le_sub_of_add_le hsum'
    have heq : (m + 1) - (m - j) = j + 1 := by omega
    rwa [heq] at this

theorem oneRow_entry_eq {n : ℕ} (T : SemistandardYoungTableau (oneRow n))
    (hT : IsStandard T) {j : ℕ} (hj : j < n) : T 0 j = j + 1 := by
  have hIcc : ∀ j, j < n → T 0 j ∈ Icc 1 n := by
    intro j hj
    have hmem : (0, j) ∈ (oneRow n).cells := by
      rw [mem_cells]; exact mem_oneRow.2 ⟨rfl, hj⟩
    have : T 0 j ∈ (oneRow n).cells.image fun c => T c.1 c.2 :=
      mem_image.2 ⟨(0, j), hmem, rfl⟩
    rwa [hT, oneRow_card] at this
  have hlt : ∀ j, j + 1 < n → T 0 j < T 0 (j + 1) := by
    intro j hj
    have hcell : (0, j + 1) ∈ oneRow n := mem_oneRow.2 ⟨rfl, hj⟩
    have hle : T 0 j ≤ T 0 (j + 1) := T.row_weak (Nat.lt_succ_self j) hcell
    have hne : T 0 j ≠ T 0 (j + 1) := by
      intro heq
      have h1 : (0, j) ∈ (oneRow n).cells := by
        rw [mem_cells]; exact mem_oneRow.2 ⟨rfl, Nat.lt_of_succ_lt hj⟩
      have h2 : (0, j + 1) ∈ (oneRow n).cells := by
        rw [mem_cells]; exact hcell
      have hinj := isStandard_injOn hT h1 h2 heq
      exact (Nat.succ_ne_self j).symm (Prod.mk.inj hinj).2
    exact lt_of_le_of_ne hle hne
  exact chain_eq_succ n (fun j => T 0 j) hIcc hlt j hj

theorem oneRow_ssyt_eq {n : ℕ} (T : SemistandardYoungTableau (oneRow n))
    (hT : IsStandard T) : T = oneRowTableau n := by
  ext i j
  by_cases hmem : (i, j) ∈ oneRow n
  · obtain ⟨hi, hj⟩ := mem_oneRow.mp hmem
    subst hi
    rw [oneRowTableau_apply, if_pos hmem, oneRow_entry_eq T hT hj]
  · rw [oneRowTableau_apply, if_neg hmem, T.zeros hmem]

theorem oneCol_entry_eq {n : ℕ} (T : SemistandardYoungTableau (oneCol n))
    (hT : IsStandard T) {i : ℕ} (hi : i < n) : T i 0 = i + 1 := by
  have hIcc : ∀ i, i < n → T i 0 ∈ Icc 1 n := by
    intro i hi
    have hmem : (i, 0) ∈ (oneCol n).cells := by
      rw [mem_cells]; exact mem_oneCol.2 ⟨rfl, hi⟩
    have : T i 0 ∈ (oneCol n).cells.image fun c => T c.1 c.2 :=
      mem_image.2 ⟨(i, 0), hmem, rfl⟩
    rwa [hT, oneCol_card] at this
  have hlt : ∀ i, i + 1 < n → T i 0 < T (i + 1) 0 := by
    intro i hi
    have hcell : (i + 1, 0) ∈ oneCol n := mem_oneCol.2 ⟨rfl, hi⟩
    exact T.col_strict (Nat.lt_succ_self i) hcell
  exact chain_eq_succ n (fun i => T i 0) hIcc hlt i hi

theorem oneCol_ssyt_eq {n : ℕ} (T : SemistandardYoungTableau (oneCol n))
    (hT : IsStandard T) : T = oneColTableau n := by
  ext i j
  by_cases hmem : (i, j) ∈ oneCol n
  · obtain ⟨hj, hi⟩ := mem_oneCol.mp hmem
    subst hj
    rw [oneColTableau_apply, if_pos hmem, oneCol_entry_eq T hT hi]
  · rw [oneColTableau_apply, if_neg hmem, T.zeros hmem]

noncomputable instance (n : ℕ) : Unique (StandardYoungTableau (oneRow n)) where
  default := oneRowStandard n
  uniq T := by
    apply StandardYoungTableau.eq_of_ssyt_eq
    exact oneRow_ssyt_eq T.toSemistandardYoungTableau T.standard

noncomputable instance (n : ℕ) : Unique (StandardYoungTableau (oneCol n)) where
  default := oneColStandard n
  uniq T := by
    apply StandardYoungTableau.eq_of_ssyt_eq
    exact oneCol_ssyt_eq T.toSemistandardYoungTableau T.standard

theorem card_syt_oneRow (n : ℕ) :
    Fintype.card (StandardYoungTableau (oneRow n)) = 1 :=
  Fintype.card_unique

theorem card_syt_oneCol (n : ℕ) :
    Fintype.card (StandardYoungTableau (oneCol n)) = 1 :=
  Fintype.card_unique

/-- One-row `(n)`: unique SYT, product of hooks `n!`. Glue; **not**
labelled hook-length. -/
theorem card_mul_hookProduct_oneRow (n : ℕ) :
    Fintype.card (StandardYoungTableau (oneRow n)) * hookProduct (oneRow n) =
    Nat.factorial (oneRow n).card := by
  simp [card_syt_oneRow, hookProduct_oneRow, oneRow_card]

/-- One-column of height `n`: unique SYT, product of hooks `n!`. Glue;
**not** labelled hook-length. -/
theorem card_mul_hookProduct_oneCol (n : ℕ) :
    Fintype.card (StandardYoungTableau (oneCol n)) * hookProduct (oneCol n) =
    Nat.factorial (oneCol n).card := by
  simp [card_syt_oneCol, hookProduct_oneCol, oneCol_card]

/-- One-cell: unique SYT, hook `1`, `1! / 1 = 1`. Glue; **not**
labelled hook-length. -/
theorem card_mul_hookProduct_oneCell :
    Fintype.card (StandardYoungTableau oneCell) * hookProduct oneCell =
    Nat.factorial oneCell.card :=
  card_mul_hookProduct_oneRow 1

/-
Residual (Level B, **out of this ticket**, not sorry-ed):
  theorem hook_length (μ : YoungDiagram) :
      Fintype.card (StandardYoungTableau μ) * hookProduct μ
        = Nat.factorial μ.card
Engine classically: hook-walk / Greene–Nijenhuis–Wilf / RSK.
Do not sorry the namesake. Catalan 2-row `(n,n)` / hook-content /
Schensted / Littlewood–Richardson / Jacobi–Trudi remain residual
of this id. Do not re-prove `YoungDiagram` / `rowLen` / `colLen` /
`SemistandardYoungTableau` / `Nat.factorial` / Catalan. Do not
prove `catalan` / RSK / hook-content / `singleton_bound` /
Hamming-bound / Plotkin / `cauchy_binet` / Kirchhoff / `bollobas`.
-/

end ProofLab.HookLength
