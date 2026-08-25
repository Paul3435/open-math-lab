/-
Glaisher infrastructure for Schur partition theorem (OPE-440).
Builds on ProofLab.Schur. STATEMENT pin 2026-08-04 frozen.

Level A: recursive oddPart/val2, expandPart/collapsePart (sum + residues),
multiset Glaisher maps (sum-preserving), partition-level sum-preserving maps.

formalize-only / known-classical / no novelty / zero sorry.
-/
import ProofLab.Schur
import Mathlib.Data.Nat.Bitwise
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Tactic

open Nat Multiset
open Nat.Partition

namespace ProofLab.Schur

/-! ## Recursive oddPart / val2 -/

/-- Peel factors of 2. -/
def oddPart (n : ℕ) : ℕ :=
  if n = 0 then 0
  else if n % 2 = 0 then oddPart (n / 2) else n
termination_by n
decreasing_by
  exact Nat.div_lt_self (Nat.pos_of_ne_zero ‹n ≠ 0›) (by decide)

/-- 2-adic valuation (count of factors of 2). -/
def val2 (n : ℕ) : ℕ :=
  if n = 0 then 0
  else if n % 2 = 0 then val2 (n / 2) + 1 else 0
termination_by n
decreasing_by
  exact Nat.div_lt_self (Nat.pos_of_ne_zero ‹n ≠ 0›) (by decide)

@[simp] theorem oddPart_zero : oddPart 0 = 0 := by unfold oddPart; simp
@[simp] theorem val2_zero : val2 0 = 0 := by unfold val2; simp

theorem oddPart_mul_pow (n : ℕ) : oddPart n * 2 ^ val2 n = n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    unfold oddPart val2
    split_ifs with h0 heven
    · simp [h0]
    · have hlt : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero h0) (by decide)
      have ih' := ih (n / 2) hlt
      calc
        oddPart (n / 2) * 2 ^ (val2 (n / 2) + 1)
            = oddPart (n / 2) * (2 ^ val2 (n / 2) * 2) := by rw [pow_succ]
        _ = (oddPart (n / 2) * 2 ^ val2 (n / 2)) * 2 := by ring
        _ = (n / 2) * 2 := by rw [ih']
        _ = n := by omega
    · simp

theorem oddPart_pos {n : ℕ} (hn : 0 < n) : 0 < oddPart n := by
  have h := oddPart_mul_pow n
  have : 0 < 2 ^ val2 n := Nat.pow_pos (by decide)
  nlinarith

theorem oddPart_odd {n : ℕ} (hn : n ≠ 0) : oddPart n % 2 = 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    unfold oddPart
    split_ifs with h0 heven
    · exact absurd h0 hn
    · have hlt : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero h0) (by decide)
      have hne : n / 2 ≠ 0 := by
        have := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero heven); omega
      exact ih (n / 2) hlt hne
    · exact Nat.mod_two_ne_zero.mp (by omega)

theorem val2_of_odd {m : ℕ} (hodd : m % 2 = 1) : val2 m = 0 := by
  unfold val2
  split_ifs with h0 heven
  · rfl
  · omega  -- m odd can't be even
  · rfl

theorem val2_two_mul {n : ℕ} (hn : 0 < n) : val2 (2 * n) = val2 n + 1 := by
  have hne : 2 * n ≠ 0 := by omega
  have heven : (2 * n) % 2 = 0 := by omega
  conv_lhs => unfold val2
  simp only [hne, heven, ↓reduceIte]
  rw [Nat.mul_div_right n (by decide)]

theorem val2_mul_pow_odd {m j : ℕ} (hm : 0 < m) (hodd : m % 2 = 1) :
    val2 (m * 2 ^ j) = j := by
  induction j with
  | zero => simp [val2_of_odd hodd]
  | succ j ih =>
    have : m * 2 ^ (j + 1) = 2 * (m * 2 ^ j) := by rw [pow_succ]; ring
    rw [this, val2_two_mul (Nat.mul_pos hm (Nat.pow_pos (by decide))), ih]

theorem oddPart_mul_pow_odd {m j : ℕ} (hm : 0 < m) (hodd : m % 2 = 1) :
    oddPart (m * 2 ^ j) = m := by
  have h := oddPart_mul_pow (m * 2 ^ j)
  rw [val2_mul_pow_odd hm hodd] at h
  exact Nat.eq_of_mul_eq_mul_right (Nat.pow_pos (by decide)) h

theorem oddPart_is_B_kernel {p : ℕ} (hp : 0 < p)
    (hmod : p % 3 = 1 ∨ p % 3 = 2) :
    oddPart p % 6 = 1 ∨ oddPart p % 6 = 5 := by
  have hodd : oddPart p % 2 = 1 := oddPart_odd hp.ne'
  have hfact := oddPart_mul_pow p
  have hop3 : oddPart p % 3 ≠ 0 := by
    intro h0
    have h3o : 3 ∣ oddPart p := Nat.dvd_of_mod_eq_zero h0
    have h3p : 3 ∣ p := by rw [← hfact]; exact dvd_mul_of_dvd_left h3o _
    have : p % 3 = 0 := Nat.mod_eq_zero_of_dvd h3p
    omega
  have : oddPart p % 6 = 1 ∨ oddPart p % 6 = 3 ∨ oddPart p % 6 = 5 := by omega
  rcases this with h | h | h
  · exact Or.inl h
  · exact absurd (by omega : oddPart p % 3 = 0) hop3
  · exact Or.inr h

theorem mul_pow2_mod3_of_B {m j : ℕ} (hm : m % 6 = 1 ∨ m % 6 = 5) :
    (m * 2 ^ j) % 3 = 1 ∨ (m * 2 ^ j) % 3 = 2 := by
  have hm3 : m % 3 = 1 ∨ m % 3 = 2 := by omega
  have h2 : ∀ j, 2 ^ j % 3 = 1 ∨ 2 ^ j % 3 = 2 := by
    intro j; induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, Nat.mul_mod]; rcases ih with h | h <;> simp [h]
  rcases hm3 with hm3 | hm3 <;> rcases h2 j with h2 | h2 <;>
    simp [Nat.mul_mod, hm3, h2]

/-! ## expandPart / collapsePart -/

def expandPart (m : ℕ) (c : ℕ) : Multiset ℕ :=
  if c = 0 then (0 : Multiset ℕ)
  else
    let rest := expandPart (2 * m) (c / 2)
    if c % 2 = 1 then m ::ₘ rest else rest
termination_by c
decreasing_by
  exact Nat.div_lt_self (Nat.pos_of_ne_zero ‹c ≠ 0›) (by decide)

@[simp] theorem expandPart_zero (m : ℕ) : expandPart m 0 = 0 := by
  unfold expandPart; simp

theorem sum_expandPart (m c : ℕ) : Multiset.sum (expandPart m c) = m * c := by
  induction c using Nat.strong_induction_on generalizing m with
  | h c ih =>
    unfold expandPart
    split_ifs with hc hbit
    · simp [hc]
    · have hlt : c / 2 < c := Nat.div_lt_self (Nat.pos_of_ne_zero hc) (by decide)
      have hs := ih (c / 2) hlt (2 * m)
      rw [Multiset.sum_cons, hs]
      have hc1 : 1 + 2 * (c / 2) = c := by have := Nat.div_add_mod c 2; omega
      calc
        m + 2 * m * (c / 2) = m * (1 + 2 * (c / 2)) := by ring
        _ = m * c := by rw [hc1]
    · have hlt : c / 2 < c := Nat.div_lt_self (Nat.pos_of_ne_zero hc) (by decide)
      have hs := ih (c / 2) hlt (2 * m)
      rw [hs]
      have hc0 : 2 * (c / 2) = c := by
        have h0 : c % 2 = 0 := Nat.mod_two_ne_one.mp hbit
        exact Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h0)
      calc
        2 * m * (c / 2) = m * (2 * (c / 2)) := by ring
        _ = m * c := by rw [hc0]

theorem exists_bit_of_mem_expandPart {m c p : ℕ} (hp : p ∈ expandPart m c) :
    ∃ i : ℕ, p = m * 2 ^ i ∧ c.testBit i = true := by
  induction c using Nat.strong_induction_on generalizing m p with
  | h c ih =>
    unfold expandPart at hp
    split_ifs at hp with hc hbit
    · exact absurd hp (Multiset.not_mem_zero _)
    · have hlt : c / 2 < c := Nat.div_lt_self (Nat.pos_of_ne_zero hc) (by decide)
      rw [mem_cons] at hp
      rcases hp with rfl | hp
      · refine ⟨0, by simp, ?_⟩
        simp [testBit_zero, hbit]
      · rcases ih (c / 2) hlt hp with ⟨i, rfl, hbit'⟩
        refine ⟨i + 1, by ring, ?_⟩
        simpa [testBit_succ] using hbit'
    · have hlt : c / 2 < c := Nat.div_lt_self (Nat.pos_of_ne_zero hc) (by decide)
      rcases ih (c / 2) hlt hp with ⟨i, rfl, hbit'⟩
      refine ⟨i + 1, by ring, ?_⟩
      simpa [testBit_succ] using hbit'

theorem mem_expandPart_of_bit {m c i : ℕ} (hbit : c.testBit i = true) :
    m * 2 ^ i ∈ expandPart m c := by
  induction c using Nat.strong_induction_on generalizing m i with
  | h c ih =>
    have hc : c ≠ 0 := by
      intro h; subst h; simp [Nat.zero_testBit] at hbit
    unfold expandPart
    simp only [hc, ↓reduceIte]
    cases i with
    | zero =>
      have hodd : c % 2 = 1 := by
        have := hbit; simp only [testBit_zero, decide_eq_true_eq] at this; exact this
      simp [hodd, mem_cons, pow_zero, mul_one]
    | succ i =>
      have hlt : c / 2 < c := Nat.div_lt_self (Nat.pos_of_ne_zero hc) (by decide)
      have hbit' : (c / 2).testBit i = true := by simpa [testBit_succ] using hbit
      have hmem : (2 * m) * 2 ^ i ∈ expandPart (2 * m) (c / 2) :=
        ih (c / 2) hlt hbit'
      have heq : (2 * m) * 2 ^ i = m * 2 ^ (i + 1) := by ring
      rw [heq] at hmem
      split_ifs with hodd
      · exact mem_cons_of_mem hmem
      · exact hmem

theorem expandPart_nodup_of_pos {m c : ℕ} (hm : 0 < m) : (expandPart m c).Nodup := by
  induction c using Nat.strong_induction_on generalizing m with
  | h c ih =>
    unfold expandPart
    split_ifs with hc hbit
    · exact Multiset.nodup_zero
    · have hlt : c / 2 < c := Nat.div_lt_self (Nat.pos_of_ne_zero hc) (by decide)
      have hrest := ih (c / 2) hlt (by omega : 0 < 2 * m)
      refine Multiset.nodup_cons.mpr ⟨?_, hrest⟩
      intro hmem
      rcases exists_bit_of_mem_expandPart hmem with ⟨j, heq, _⟩
      have hmul : m * 1 = m * 2 ^ (j + 1) := by
        calc m * 1 = m := by ring
          _ = 2 * m * 2 ^ j := heq
          _ = m * (2 * 2 ^ j) := by ring
          _ = m * 2 ^ (j + 1) := by rw [pow_succ, Nat.mul_comm 2]
      have : 1 = 2 ^ (j + 1) := Nat.eq_of_mul_eq_mul_left hm hmul
      have : 2 ≤ 2 ^ (j + 1) :=
        Nat.pow_le_pow_of_le_right (by decide : 0 < 2) (by omega : 1 ≤ j + 1)
      omega
    · exact ih (c / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hc) (by decide))
        (by omega : 0 < 2 * m)

theorem expandPart_mem_mod3 {m c p : ℕ}
    (hmB : m % 6 = 1 ∨ m % 6 = 5) (hp : p ∈ expandPart m c) :
    p % 3 = 1 ∨ p % 3 = 2 := by
  rcases exists_bit_of_mem_expandPart hp with ⟨i, rfl, _⟩
  exact mul_pow2_mod3_of_B (j := i) hmB

def collapsePart (p : ℕ) : Multiset ℕ :=
  if p = 0 then (0 : Multiset ℕ) else replicate (2 ^ val2 p) (oddPart p)

theorem sum_collapsePart (p : ℕ) : Multiset.sum (collapsePart p) = p := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp [collapsePart]
  · unfold collapsePart
    simp only [hp, ↓reduceIte, Multiset.sum_replicate, nsmul_eq_mul]
    rw [Nat.mul_comm]
    exact oddPart_mul_pow p

theorem collapsePart_eq_odd {p : ℕ} (hp : 0 < p) :
    collapsePart p = replicate (2 ^ val2 p) (oddPart p) := by
  unfold collapsePart
  simp only [hp.ne', ↓reduceIte]

theorem collapsePart_mem_B {p q : ℕ} (hp : 0 < p)
    (hmod : p % 3 = 1 ∨ p % 3 = 2) (hq : q ∈ collapsePart p) :
    q % 6 = 1 ∨ q % 6 = 5 := by
  rw [collapsePart_eq_odd hp] at hq
  obtain ⟨_, rfl⟩ := Multiset.mem_replicate.mp hq
  exact oddPart_is_B_kernel hp hmod

/-! ## Multiset maps -/

def glaisherExpand (s : Multiset ℕ) : Multiset ℕ :=
  s.dedup.bind fun m => expandPart m (s.count m)

def glaisherCollapse (s : Multiset ℕ) : Multiset ℕ :=
  s.bind collapsePart

private theorem sum_nsmul_singleton_finset (s : Multiset ℕ) :
    Multiset.sum (∑ x ∈ s.toFinset, s.count x • ({x} : Multiset ℕ)) =
      ∑ x ∈ s.toFinset, s.count x * x := by
  classical
  refine Finset.induction_on (s.toFinset) ?_ ?_
  · simp
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Multiset.sum_add, ih]
    simp [Multiset.sum_nsmul, Multiset.sum_singleton, nsmul_eq_mul, Nat.mul_comm]

theorem sum_eq_sum_count_mul (s : Multiset ℕ) :
    Multiset.sum s = ∑ x ∈ s.toFinset, s.count x * x := by
  classical
  have hs := congr_arg Multiset.sum (toFinset_sum_count_nsmul_eq (s := s))
  -- hs : sum (∑ count • {x}) = sum s
  rw [sum_nsmul_singleton_finset s] at hs
  exact hs.symm

theorem sum_glaisherExpand (s : Multiset ℕ) :
    Multiset.sum (glaisherExpand s) = Multiset.sum s := by
  classical
  unfold glaisherExpand
  rw [Multiset.sum_bind]
  have hmap :
      s.dedup.map (fun m => Multiset.sum (expandPart m (s.count m))) =
        s.dedup.map fun m => m * s.count m :=
    Multiset.map_congr rfl fun m _ => sum_expandPart m (s.count m)
  rw [hmap]
  have hdedup : s.dedup = s.toFinset.val := by simp [toFinset]
  rw [hdedup]
  have hsum :
      Multiset.sum (s.toFinset.val.map fun m => m * s.count m) =
        ∑ x ∈ s.toFinset, x * s.count x := by
    simp [Finset.sum_eq_multiset_sum]
  rw [hsum]
  -- x * count = count * x
  simp_rw [Nat.mul_comm _ (Multiset.count _ _)]
  exact (sum_eq_sum_count_mul s).symm

theorem sum_glaisherCollapse (s : Multiset ℕ) :
    Multiset.sum (glaisherCollapse s) = Multiset.sum s := by
  unfold glaisherCollapse
  rw [Multiset.sum_bind]
  have hmap : s.map (fun a => Multiset.sum (collapsePart a)) = s.map id :=
    Multiset.map_congr rfl fun a _ => sum_collapsePart a
  rw [hmap]
  simp [Multiset.map_id']

theorem glaisherExpand_parts_mod3 {s : Multiset ℕ}
    (hB : ∀ m ∈ s, m % 6 = 1 ∨ m % 6 = 5) {p : ℕ}
    (hp : p ∈ glaisherExpand s) :
    p % 3 = 1 ∨ p % 3 = 2 := by
  classical
  simp only [glaisherExpand, mem_bind] at hp
  rcases hp with ⟨m, hm, hp'⟩
  exact expandPart_mem_mod3 (hB m (mem_dedup.mp hm)) hp'

theorem glaisherCollapse_parts_mod6 {s : Multiset ℕ}
    (hA : ∀ p ∈ s, 0 < p ∧ (p % 3 = 1 ∨ p % 3 = 2)) {q : ℕ}
    (hq : q ∈ glaisherCollapse s) :
    q % 6 = 1 ∨ q % 6 = 5 := by
  simp only [glaisherCollapse, mem_bind] at hq
  rcases hq with ⟨p, hp, hq'⟩
  have ⟨hpos, hmod⟩ := hA p hp
  exact collapsePart_mem_B hpos hmod hq'

/-- Partition-level B→A map (sum-preserving). -/
def glaisherBtoA_parts (p : Partition n) : Partition n :=
  ofSums n (glaisherExpand p.parts) (by
    simpa [p.parts_sum] using sum_glaisherExpand p.parts)

/-- Partition-level A→B map (sum-preserving). -/
def glaisherAtoB_parts (p : Partition n) : Partition n :=
  ofSums n (glaisherCollapse p.parts) (by
    simpa [p.parts_sum] using sum_glaisherCollapse p.parts)

/-! ## Level B — counts, Nodup, residue maps (OPE-445)

Partial lift toward `∀ n, (schurA n).card = (schurB n).card`.
This section closes Nodup of Glaisher expand on B-multisets and the one-way
Finset maps `schurB → schurA` and `schurA → schurB`. Inverse/count bijection
for card equality remains open (no sorry planted for the universal theorem).
-/

theorem B_part_odd {m : ℕ} (hm : m % 6 = 1 ∨ m % 6 = 5) : m % 2 = 1 := by omega

theorem B_part_pos {m : ℕ} (hm : m % 6 = 1 ∨ m % 6 = 5) : 0 < m := by omega

theorem B_part_mod3 {m : ℕ} (hm : m % 6 = 1 ∨ m % 6 = 5) :
    m % 3 = 1 ∨ m % 3 = 2 := by omega

theorem expandPart_pos {m c p : ℕ} (hm : 0 < m) (hp : p ∈ expandPart m c) : 0 < p := by
  rcases exists_bit_of_mem_expandPart hp with ⟨i, rfl, _⟩
  exact Nat.mul_pos hm (Nat.pow_pos (by decide))

theorem oddPart_expand {m c p : ℕ} (hm : 0 < m) (hodd : m % 2 = 1)
    (hp : p ∈ expandPart m c) : oddPart p = m := by
  rcases exists_bit_of_mem_expandPart hp with ⟨i, rfl, _⟩
  exact oddPart_mul_pow_odd hm hodd

theorem count_expandPart_pow {m c i : ℕ} (hm : 0 < m) :
    Multiset.count (m * 2 ^ i) (expandPart m c) =
      if c.testBit i = true then 1 else 0 := by
  classical
  by_cases hbit : c.testBit i = true
  · simp only [hbit, ↓reduceIte]
    exact Multiset.count_eq_one_of_mem (expandPart_nodup_of_pos hm)
      (mem_expandPart_of_bit hbit)
  · simp only [hbit, ↓reduceIte]
    by_contra hpos
    have hmem : m * 2 ^ i ∈ expandPart m c :=
      (count_pos (a := m * 2 ^ i)).1 (Nat.pos_of_ne_zero hpos)
    rcases exists_bit_of_mem_expandPart hmem with ⟨j, heq, hbit'⟩
    have hij : i = j :=
      Nat.pow_right_injective (by decide : 1 < 2) (Nat.eq_of_mul_eq_mul_left hm heq)
    subst hij
    exact hbit hbit'

theorem count_collapsePart (p q : ℕ) :
    Multiset.count q (collapsePart p) =
      if p = 0 then 0 else if q = oddPart p then 2 ^ val2 p else 0 := by
  classical
  by_cases h0 : p = 0
  · simp [collapsePart, h0]
  · simp [collapsePart, h0, Multiset.count_replicate]

/-- Expand parts from distinct positive odd kernels are pairwise disjoint. -/
theorem expandPart_disjoint_of_ne_odd {m₁ m₂ c₁ c₂ : ℕ}
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (ho₁ : m₁ % 2 = 1) (ho₂ : m₂ % 2 = 1) (hne : m₁ ≠ m₂) :
    Multiset.Disjoint (expandPart m₁ c₁) (expandPart m₂ c₂) := by
  intro p hp₁ hp₂
  have h1 := oddPart_expand hm₁ ho₁ hp₁
  have h2 := oddPart_expand hm₂ ho₂ hp₂
  exact hne (h1.symm.trans h2)

/-- Glaisher expand of a B-legal multiset is Nodup. -/
theorem glaisherExpand_nodup {s : Multiset ℕ}
    (hB : ∀ m ∈ s, m % 6 = 1 ∨ m % 6 = 5) :
    (glaisherExpand s).Nodup := by
  classical
  unfold glaisherExpand
  rw [Multiset.nodup_bind]
  constructor
  · intro m hm
    exact expandPart_nodup_of_pos (B_part_pos (hB m (mem_dedup.mp hm)))
  · refine Multiset.Nodup.pairwise ?_ (nodup_dedup s)
    intro a ha b hb hne
    exact expandPart_disjoint_of_ne_odd
      (B_part_pos (hB a (mem_dedup.mp ha)))
      (B_part_pos (hB b (mem_dedup.mp hb)))
      (B_part_odd (hB a (mem_dedup.mp ha)))
      (B_part_odd (hB b (mem_dedup.mp hb)))
      hne

theorem glaisherExpand_pos {s : Multiset ℕ}
    (hB : ∀ m ∈ s, m % 6 = 1 ∨ m % 6 = 5) {p : ℕ}
    (hp : p ∈ glaisherExpand s) : 0 < p := by
  simp only [glaisherExpand, mem_bind] at hp
  rcases hp with ⟨m, hm, hp'⟩
  exact expandPart_pos (B_part_pos (hB m (mem_dedup.mp hm))) hp'

theorem ofSums_parts_eq_of_pos {n : ℕ} {l : Multiset ℕ} (hl : l.sum = n)
    (hpos : ∀ x ∈ l, 0 < x) : (ofSums n l hl).parts = l := by
  simp only [ofSums]
  refine Multiset.filter_eq_self.2 ?_
  intro x hx
  exact (hpos x hx).ne'

/-- B→A Glaisher map sends `schurB` into `schurA`. -/
theorem glaisherBtoA_mem_schurA {n : ℕ} {p : Partition n} (hp : p ∈ schurB n) :
    glaisherBtoA_parts p ∈ schurA n := by
  classical
  have hB : partsMod6_15 p := schurB_mod6 hp
  have hBall : ∀ m ∈ p.parts, m % 6 = 1 ∨ m % 6 = 5 := hB
  unfold glaisherBtoA_parts schurA
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
  · have hparts :
        (ofSums n (glaisherExpand p.parts)
          (by simpa [p.parts_sum] using sum_glaisherExpand p.parts)).parts =
          glaisherExpand p.parts :=
      ofSums_parts_eq_of_pos _ (fun x hx => glaisherExpand_pos hBall hx)
    rw [hparts]
    exact glaisherExpand_nodup hBall
  · intro i hi
    have hparts :
        (ofSums n (glaisherExpand p.parts)
          (by simpa [p.parts_sum] using sum_glaisherExpand p.parts)).parts =
          glaisherExpand p.parts :=
      ofSums_parts_eq_of_pos _ (fun x hx => glaisherExpand_pos hBall hx)
    rw [hparts] at hi
    exact glaisherExpand_parts_mod3 hBall hi

theorem glaisherCollapse_pos {s : Multiset ℕ}
    (hA : ∀ p ∈ s, 0 < p) {q : ℕ} (hq : q ∈ glaisherCollapse s) : 0 < q := by
  simp only [glaisherCollapse, mem_bind] at hq
  rcases hq with ⟨p, hp, hq'⟩
  have hppos := hA p hp
  rw [collapsePart_eq_odd hppos] at hq'
  rcases Multiset.mem_replicate.mp hq' with ⟨_, rfl⟩
  exact oddPart_pos hppos

/-- A→B Glaisher map sends `schurA` into `schurB`. -/
theorem glaisherAtoB_mem_schurB {n : ℕ} {p : Partition n} (hp : p ∈ schurA n) :
    glaisherAtoB_parts p ∈ schurB n := by
  classical
  have hmod := schurA_mod3 hp
  have hA : ∀ q ∈ p.parts, 0 < q ∧ (q % 3 = 1 ∨ q % 3 = 2) := by
    intro q hq
    exact ⟨p.parts_pos hq, hmod q hq⟩
  unfold glaisherAtoB_parts schurB
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  intro i hi
  have hpos' : ∀ x ∈ glaisherCollapse p.parts, 0 < x :=
    fun x hx => glaisherCollapse_pos (fun q hq => (hA q hq).1) hx
  have hparts :
      (ofSums n (glaisherCollapse p.parts)
        (by simpa [p.parts_sum] using sum_glaisherCollapse p.parts)).parts =
        glaisherCollapse p.parts :=
    ofSums_parts_eq_of_pos _ hpos'
  rw [hparts] at hi
  exact glaisherCollapse_parts_mod6 hA hi

/-!
### Remaining for full `schur_partition` (card equality)
1. `glaisherCollapse (glaisherExpand s) = s` on B-legal multisets (binary bit-sum inverse).
2. `glaisherExpand (glaisherCollapse s) = s` on Nodup A-legal multisets.
3. Conclude `(schurA n).card = (schurB n).card` via `Finset.card_bij'`.
No `sorry` is planted for those goals.
-/

end ProofLab.Schur
