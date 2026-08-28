import Mathlib.Data.List.Sort
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Lattice
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic

/-!
# Finite Erdős–Szekeres monotone subsequence theorem (formalize-only, OPE-433)

Any sequence of length at least `(r-1)*(s-1)+1` in a linear order contains a
**weakly increasing** subsequence of length `r` or a **weakly decreasing**
subsequence of length `s`.

Convention pin (STATEMENT.md): **weak** monotonicity via `List.Sorted (· ≤ ·)` /
`List.Sorted (· ≥ ·)`. Subsequences are realized as the value-lists of index-sets
ordered by `Finset.sort (· ≤ ·)` (strictly increasing indices). Distinctness of
values is **not** required for the weak form.

Classical proof: label each index `i` by
`(incLen i, decLen i)` = lengths of longest weak-inc / weak-dec subsequences
ending at `i`; the label map is injective into `{1..r-1} × {1..s-1}` when no
monotone run of the target lengths exists; pigeonhole then forces
`n ≤ (r-1)*(s-1)`.

Known-classical (Erdős–Szekeres 1935). **No novelty claim.** Genuine Mathlib gap
under the pinned v4.10.0 snapshot (only infinitary ES lemmas exist upstream).
-/

namespace ProofLab.ErdosSzekeres

open Finset

variable {α : Type*} [LinearOrder α]
variable {n : ℕ}

/-! ## Ending index-sets for weak monotone subsequences -/

/-- `t` is the index-set of a weakly increasing subsequence of `f` that ends at
`i` (every index in `t` is `≤ i`, `i ∈ t`, and `f` is nondecreasing along the
order of indices). -/
def IsIncEnding (f : Fin n → α) (i : Fin n) (t : Finset (Fin n)) : Prop :=
  i ∈ t ∧ (∀ x ∈ t, x ≤ i) ∧ ∀ x ∈ t, ∀ y ∈ t, x < y → f x ≤ f y

/-- Dual: weakly decreasing subsequence ending at `i`. -/
def IsDecEnding (f : Fin n → α) (i : Fin n) (t : Finset (Fin n)) : Prop :=
  i ∈ t ∧ (∀ x ∈ t, x ≤ i) ∧ ∀ x ∈ t, ∀ y ∈ t, x < y → f y ≤ f x

lemma isIncEnding_singleton (f : Fin n → α) (i : Fin n) : IsIncEnding f i {i} := by
  refine ⟨mem_singleton_self i, ?_, ?_⟩
  · intro x hx
    exact (mem_singleton.mp hx) ▸ le_rfl
  · intro x hx y hy hlt
    exact absurd hlt ((mem_singleton.mp hx) ▸ (mem_singleton.mp hy) ▸ lt_irrefl _)

lemma isDecEnding_singleton (f : Fin n → α) (i : Fin n) : IsDecEnding f i {i} := by
  refine ⟨mem_singleton_self i, ?_, ?_⟩
  · intro x hx
    exact (mem_singleton.mp hx) ▸ le_rfl
  · intro x hx y hy hlt
    exact absurd hlt ((mem_singleton.mp hx) ▸ (mem_singleton.mp hy) ▸ lt_irrefl _)

/-! ## Longest ending lengths (classical, via finite sup) -/

/-- Length of a longest weakly increasing subsequence of `f` ending at `i`. -/
noncomputable def incLen (f : Fin n → α) (i : Fin n) : ℕ := by
  classical
  exact ((univ : Finset (Finset (Fin n))).filter (IsIncEnding f i)).sup card

/-- Length of a longest weakly decreasing subsequence of `f` ending at `i`. -/
noncomputable def decLen (f : Fin n → α) (i : Fin n) : ℕ := by
  classical
  exact ((univ : Finset (Finset (Fin n))).filter (IsDecEnding f i)).sup card

lemma exists_isIncEnding_card_eq (f : Fin n → α) (i : Fin n) :
    ∃ t : Finset (Fin n), IsIncEnding f i t ∧ t.card = incLen f i := by
  classical
  set s := (univ : Finset (Finset (Fin n))).filter (IsIncEnding f i)
  have hs : s.Nonempty :=
    ⟨{i}, mem_filter.mpr ⟨mem_univ _, isIncEnding_singleton f i⟩⟩
  obtain ⟨t, ht, hcard⟩ := exists_mem_eq_sup s hs (f := card)
  exact ⟨t, (mem_filter.mp ht).2, hcard.symm⟩

lemma exists_isDecEnding_card_eq (f : Fin n → α) (i : Fin n) :
    ∃ t : Finset (Fin n), IsDecEnding f i t ∧ t.card = decLen f i := by
  classical
  set s := (univ : Finset (Finset (Fin n))).filter (IsDecEnding f i)
  have hs : s.Nonempty :=
    ⟨{i}, mem_filter.mpr ⟨mem_univ _, isDecEnding_singleton f i⟩⟩
  obtain ⟨t, ht, hcard⟩ := exists_mem_eq_sup s hs (f := card)
  exact ⟨t, (mem_filter.mp ht).2, hcard.symm⟩

lemma one_le_incLen (f : Fin n → α) (i : Fin n) : 1 ≤ incLen f i := by
  classical
  have h := isIncEnding_singleton f i
  have hmem : {i} ∈ (univ : Finset (Finset (Fin n))).filter (IsIncEnding f i) := by
    exact mem_filter.mpr ⟨mem_univ _, h⟩
  have : ({i} : Finset (Fin n)).card ≤ incLen f i := by
    simpa [incLen] using
      le_sup (s := (univ : Finset (Finset (Fin n))).filter (IsIncEnding f i))
        (f := card) hmem
  simpa using this

lemma one_le_decLen (f : Fin n → α) (i : Fin n) : 1 ≤ decLen f i := by
  classical
  have h := isDecEnding_singleton f i
  have hmem : {i} ∈ (univ : Finset (Finset (Fin n))).filter (IsDecEnding f i) := by
    exact mem_filter.mpr ⟨mem_univ _, h⟩
  have : ({i} : Finset (Fin n)).card ≤ decLen f i := by
    simpa [decLen] using
      le_sup (s := (univ : Finset (Finset (Fin n))).filter (IsDecEnding f i))
        (f := card) hmem
  simpa using this

lemma card_le_incLen_of_isIncEnding {f : Fin n → α} {i : Fin n} {t : Finset (Fin n)}
    (ht : IsIncEnding f i t) : t.card ≤ incLen f i := by
  classical
  have hmem : t ∈ (univ : Finset (Finset (Fin n))).filter (IsIncEnding f i) :=
    mem_filter.mpr ⟨mem_univ _, ht⟩
  simpa [incLen] using
    le_sup (s := (univ : Finset (Finset (Fin n))).filter (IsIncEnding f i))
      (f := card) hmem

lemma card_le_decLen_of_isDecEnding {f : Fin n → α} {i : Fin n} {t : Finset (Fin n)}
    (ht : IsDecEnding f i t) : t.card ≤ decLen f i := by
  classical
  have hmem : t ∈ (univ : Finset (Finset (Fin n))).filter (IsDecEnding f i) :=
    mem_filter.mpr ⟨mem_univ _, ht⟩
  simpa [decLen] using
    le_sup (s := (univ : Finset (Finset (Fin n))).filter (IsDecEnding f i))
      (f := card) hmem

/-! ## Extension lemmas (the heart of injectivity) -/

lemma isIncEnding_insert {f : Fin n → α} {i apex : Fin n} {t : Finset (Fin n)}
    (ht : IsIncEnding f i t) (hi_lt : i < apex) (hf : f i ≤ f apex) :
    IsIncEnding f apex (insert apex t) := by
  obtain ⟨hi, hle, hmono⟩ := ht
  refine ⟨mem_insert_self apex t, ?_, ?_⟩
  · intro x hx
    cases mem_insert.mp hx with
    | inl hxa => exact hxa ▸ le_rfl
    | inr hxt => exact (hle x hxt).trans hi_lt.le
  · intro x hx y hy hxy
    cases mem_insert.mp hx with
    | inl hxa =>
      -- x = apex; cannot have apex < y with y ≤ i < apex
      cases mem_insert.mp hy with
      | inl hya =>
        rw [hxa, hya] at hxy; exact (lt_irrefl _ hxy).elim
      | inr hyt =>
        have hy_le : y ≤ i := hle y hyt
        have : y < apex := lt_of_le_of_lt hy_le hi_lt
        rw [hxa] at hxy; exact (not_lt_of_gt this hxy).elim
    | inr hxt =>
      cases mem_insert.mp hy with
      | inl hya =>
        -- y = apex: need f x ≤ f apex
        have hx_le_i : x ≤ i := hle x hxt
        cases lt_or_eq_of_le hx_le_i with
        | inl hxi => exact (hmono x hxt i hi hxi).trans (hya ▸ hf)
        | inr hxi => exact hxi ▸ hya ▸ hf
      | inr hyt =>
        exact hmono x hxt y hyt hxy

lemma isDecEnding_insert {f : Fin n → α} {i apex : Fin n} {t : Finset (Fin n)}
    (ht : IsDecEnding f i t) (hi_lt : i < apex) (hf : f apex ≤ f i) :
    IsDecEnding f apex (insert apex t) := by
  obtain ⟨hi, hle, hmono⟩ := ht
  refine ⟨mem_insert_self apex t, ?_, ?_⟩
  · intro x hx
    cases mem_insert.mp hx with
    | inl hxa => exact hxa ▸ le_rfl
    | inr hxt => exact (hle x hxt).trans hi_lt.le
  · intro x hx y hy hxy
    cases mem_insert.mp hx with
    | inl hxa =>
      cases mem_insert.mp hy with
      | inl hya =>
        rw [hxa, hya] at hxy; exact (lt_irrefl _ hxy).elim
      | inr hyt =>
        have hy_le : y ≤ i := hle y hyt
        have : y < apex := lt_of_le_of_lt hy_le hi_lt
        rw [hxa] at hxy; exact (not_lt_of_gt this hxy).elim
    | inr hxt =>
      cases mem_insert.mp hy with
      | inl hya =>
        -- y = apex: need f apex ≤ f x
        have hx_le_i : x ≤ i := hle x hxt
        cases lt_or_eq_of_le hx_le_i with
        | inl hxi => exact (hya ▸ hf).trans (hmono x hxt i hi hxi)
        | inr hxi => exact hxi ▸ hya ▸ hf
      | inr hyt =>
        exact hmono x hxt y hyt hxy

lemma incLen_strict_mono_of_le {f : Fin n → α} {i apex : Fin n}
    (hi_lt : i < apex) (hf : f i ≤ f apex) : incLen f i < incLen f apex := by
  classical
  obtain ⟨t, ht, hcard⟩ := exists_isIncEnding_card_eq f i
  have hins : IsIncEnding f apex (insert apex t) := isIncEnding_insert ht hi_lt hf
  have hnotin : apex ∉ t := fun ha => not_lt_of_le (ht.2.1 apex ha) hi_lt
  have hcard' : (insert apex t).card = t.card + 1 := card_insert_of_not_mem hnotin
  have hle := card_le_incLen_of_isIncEnding hins
  have : incLen f i + 1 ≤ incLen f apex := by
    calc
      incLen f i + 1 = t.card + 1 := by rw [hcard]
      _ = (insert apex t).card := hcard'.symm
      _ ≤ incLen f apex := hle
  exact Nat.lt_of_succ_le this

lemma decLen_strict_mono_of_ge {f : Fin n → α} {i apex : Fin n}
    (hi_lt : i < apex) (hf : f apex ≤ f i) : decLen f i < decLen f apex := by
  classical
  obtain ⟨t, ht, hcard⟩ := exists_isDecEnding_card_eq f i
  have hins : IsDecEnding f apex (insert apex t) := isDecEnding_insert ht hi_lt hf
  have hnotin : apex ∉ t := fun ha => not_lt_of_le (ht.2.1 apex ha) hi_lt
  have hcard' : (insert apex t).card = t.card + 1 := card_insert_of_not_mem hnotin
  have hle := card_le_decLen_of_isDecEnding hins
  have : decLen f i + 1 ≤ decLen f apex := by
    calc
      decLen f i + 1 = t.card + 1 := by rw [hcard]
      _ = (insert apex t).card := hcard'.symm
      _ ≤ decLen f apex := hle
  exact Nat.lt_of_succ_le this

/-! ## From ending sets to `List.Sorted` subsequences -/

/-- Sort an ending index-set into increasing index order and map through `f`. -/
noncomputable def valuesOf (f : Fin n → α) (t : Finset (Fin n)) : List α :=
  (t.sort (· ≤ ·)).map f

lemma valuesOf_length (f : Fin n → α) (t : Finset (Fin n)) :
    (valuesOf f t).length = t.card := by
  simp [valuesOf, List.length_map, length_sort]

lemma valuesOf_sorted_inc {f : Fin n → α} {i : Fin n} {t : Finset (Fin n)}
    (ht : IsIncEnding f i t) : (valuesOf f t).Sorted (· ≤ ·) := by
  classical
  simp only [valuesOf, List.Sorted]
  rw [List.pairwise_map]
  refine List.pairwise_iff_get.mpr ?_
  intro a b hab
  let L := t.sort (fun u v : Fin n => u ≤ v)
  have hlt : L.get a < L.get b := (sort_sorted_lt (α := Fin n) t).rel_get_of_lt hab
  have hmem_a : L.get a ∈ t := (mem_sort (fun u v : Fin n => u ≤ v)).1 (List.get_mem L a.1 a.2)
  have hmem_b : L.get b ∈ t := (mem_sort (fun u v : Fin n => u ≤ v)).1 (List.get_mem L b.1 b.2)
  exact ht.2.2 _ hmem_a _ hmem_b hlt

lemma valuesOf_sorted_dec {f : Fin n → α} {i : Fin n} {t : Finset (Fin n)}
    (ht : IsDecEnding f i t) : (valuesOf f t).Sorted (· ≥ ·) := by
  classical
  simp only [valuesOf, List.Sorted]
  rw [List.pairwise_map]
  refine List.pairwise_iff_get.mpr ?_
  intro a b hab
  let L := t.sort (fun u v : Fin n => u ≤ v)
  have hlt : L.get a < L.get b := (sort_sorted_lt (α := Fin n) t).rel_get_of_lt hab
  have hmem_a : L.get a ∈ t := (mem_sort (fun u v : Fin n => u ≤ v)).1 (List.get_mem L a.1 a.2)
  have hmem_b : L.get b ∈ t := (mem_sort (fun u v : Fin n => u ≤ v)).1 (List.get_mem L b.1 b.2)
  exact ht.2.2 _ hmem_a _ hmem_b hlt

/-! ## Pigeonhole on length labels -/

/-- Core quantitative form: if every ending inc-length is `< r` and every ending
dec-length is `< s`, then `n ≤ (r-1)*(s-1)`. -/
theorem erdosSzekeres_card_bound {f : Fin n → α} {r s : ℕ}
    (hInc : ∀ i : Fin n, incLen f i < r)
    (hDec : ∀ i : Fin n, decLen f i < s) :
    n ≤ (r - 1) * (s - 1) := by
  classical
  cases r with
  | zero =>
    cases n with
    | zero => simp
    | succ _ => exact absurd (hInc 0) (Nat.not_lt_zero _)
  | succ r' =>
    cases s with
    | zero =>
      cases n with
      | zero => simp
      | succ _ => exact absurd (hDec 0) (Nat.not_lt_zero _)
    | succ s' =>
      let φ : Fin n → Fin r' × Fin s' := fun i =>
        (⟨incLen f i - 1, by
            have h1 := one_le_incLen f i
            have h2 : incLen f i ≤ r' := Nat.lt_succ_iff.mp (hInc i)
            exact Nat.sub_lt_left_of_lt_add h1 (by omega)⟩,
         ⟨decLen f i - 1, by
            have h1 := one_le_decLen f i
            have h2 : decLen f i ≤ s' := Nat.lt_succ_iff.mp (hDec i)
            exact Nat.sub_lt_left_of_lt_add h1 (by omega)⟩)
      have hφ : Function.Injective φ := by
        intro a b hab
        by_contra hne
        wlog hlt : a < b generalizing a b
        · cases lt_or_eq_of_le (le_of_not_lt hlt) with
          | inl hlt' => exact this hab.symm (Ne.symm hne) hlt'
          | inr heq => exact hne heq.symm
        have hinc' : incLen f a = incLen f b := by
          have h1 := one_le_incLen f a
          have h2 := one_le_incLen f b
          have : (incLen f a - 1 : ℕ) = incLen f b - 1 := by
            injection hab with p q
            exact Fin.val_eq_of_eq p
          omega
        have hdec' : decLen f a = decLen f b := by
          have h1 := one_le_decLen f a
          have h2 := one_le_decLen f b
          have : (decLen f a - 1 : ℕ) = decLen f b - 1 := by
            injection hab with p q
            exact Fin.val_eq_of_eq q
          omega
        cases le_total (f a) (f b) with
        | inl hf => exact absurd hinc' (ne_of_lt (incLen_strict_mono_of_le hlt hf))
        | inr hf => exact absurd hdec' (ne_of_lt (decLen_strict_mono_of_ge hlt hf))
      have hcard := Fintype.card_le_of_injective φ hφ
      simpa [Fintype.card_fin, Fintype.card_prod] using hcard

/-! ## Main theorem -/

/-- **Finite Erdős–Szekeres (weak monotone form).**

Any sequence `f : Fin n → α` of length `n ≥ (r-1)*(s-1)+1` admits a weakly
increasing subsequence of length `r` (`List.Sorted (· ≤ ·)`) or a weakly
decreasing subsequence of length `s` (`List.Sorted (· ≥ ·)`).

Formalize-only / known-classical (Erdős–Szekeres 1935). No novelty claim. -/
theorem erdosSzekeres_monotone {r s : ℕ}
    (h : (r - 1) * (s - 1) + 1 ≤ n) (f : Fin n → α) :
    (∃ l : List α, r ≤ l.length ∧ l.Sorted (· ≤ ·)) ∨
      (∃ l : List α, s ≤ l.length ∧ l.Sorted (· ≥ ·)) := by
  classical
  by_contra H
  push_neg at H
  have hInc : ∀ i : Fin n, incLen f i < r := by
    intro i
    by_contra hge
    push_neg at hge
    obtain ⟨t, ht, hcard⟩ := exists_isIncEnding_card_eq f i
    exact H.1 (valuesOf f t) (by rw [valuesOf_length, hcard]; exact hge)
      (valuesOf_sorted_inc ht)
  have hDec : ∀ i : Fin n, decLen f i < s := by
    intro i
    by_contra hge
    push_neg at hge
    obtain ⟨t, ht, hcard⟩ := exists_isDecEnding_card_eq f i
    exact H.2 (valuesOf f t) (by rw [valuesOf_length, hcard]; exact hge)
      (valuesOf_sorted_dec ht)
  have hbound := erdosSzekeres_card_bound (f := f) hInc hDec
  exact Nat.not_succ_le_self ((r - 1) * (s - 1)) (h.trans hbound)

/-- Convenience form with the length hypothesis on a free `n` argument. -/
theorem erdosSzekeres_monotone' {r s n : ℕ}
    (h : (r - 1) * (s - 1) + 1 ≤ n) (f : Fin n → α) :
    (∃ l : List α, r ≤ l.length ∧ l.Sorted (· ≤ ·)) ∨
      (∃ l : List α, s ≤ l.length ∧ l.Sorted (· ≥ ·)) :=
  erdosSzekeres_monotone h f

end ProofLab.ErdosSzekeres
