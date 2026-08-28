/-
Euler's partition theorem: odd parts = distinct parts.
Glaisher bijection on Mathlib `Nat.Partition`.

OPE-558 Formalist. formalize-only / known-classical (Euler 1748; combinatorial
bijection Glaisher 1883) / no novelty claim.

Reuses `oddPart` / `val2` / `expandPart` / `collapsePart` / `glaisherExpand` /
`glaisherCollapse` / the sum-preserving `ofSums` wrappers from
`ProofLab.SchurGlaisher` **without** the mod-6 / mod-3 filters.

Do **not** import `Archive.*` / `Theorems100`. Do **not** re-prime
`theorem schur_partition` (different identity: distinct ≡1,2 mod 3 vs
parts ≡±1 mod 6). Do **not** prove `oddDistincts` as the claim.
-/
import ProofLab.SchurGlaisher
import Mathlib.Tactic

open Nat Multiset
open Nat.Partition
open ProofLab.Schur

namespace ProofLab.Euler

/-! ## Odd-part helpers (no mod-6) -/

theorem not_even_iff_mod_two {n : ℕ} : ¬Even n ↔ n % 2 = 1 := by
  rw [Nat.even_iff]
  omega

theorem odd_pos {m : ℕ} (hodd : m % 2 = 1) : 0 < m := by omega

theorem odds_parts_odd {n : ℕ} {p : Partition n} (hp : p ∈ odds n) :
    ∀ m ∈ p.parts, m % 2 = 1 := by
  intro m hm
  exact not_even_iff_mod_two.mp ((Finset.mem_filter.mp hp).2 m hm)

theorem distincts_nodup {n : ℕ} {p : Partition n} (hp : p ∈ distincts n) :
    p.parts.Nodup :=
  (Finset.mem_filter.mp hp).2

/-! ## Expand of odd kernels is Nodup / positive -/

theorem glaisherExpand_nodup_odd {s : Multiset ℕ}
    (hOdd : ∀ m ∈ s, m % 2 = 1) :
    (glaisherExpand s).Nodup := by
  classical
  unfold glaisherExpand
  rw [Multiset.nodup_bind]
  constructor
  · intro m hm
    exact expandPart_nodup_of_pos (odd_pos (hOdd m (mem_dedup.mp hm)))
  · refine Multiset.Nodup.pairwise ?_ (nodup_dedup s)
    intro a ha b hb hne
    exact expandPart_disjoint_of_ne_odd
      (odd_pos (hOdd a (mem_dedup.mp ha)))
      (odd_pos (hOdd b (mem_dedup.mp hb)))
      (hOdd a (mem_dedup.mp ha))
      (hOdd b (mem_dedup.mp hb))
      hne

theorem glaisherExpand_pos_odd {s : Multiset ℕ}
    (hOdd : ∀ m ∈ s, m % 2 = 1) {p : ℕ}
    (hp : p ∈ glaisherExpand s) : 0 < p := by
  simp only [glaisherExpand, mem_bind] at hp
  rcases hp with ⟨m, hm, hp'⟩
  exact expandPart_pos (odd_pos (hOdd m (mem_dedup.mp hm))) hp'

theorem glaisherCollapse_parts_odd {s : Multiset ℕ}
    (hpos : ∀ p ∈ s, 0 < p) {q : ℕ}
    (hq : q ∈ glaisherCollapse s) : q % 2 = 1 := by
  simp only [glaisherCollapse, mem_bind] at hq
  rcases hq with ⟨p, hp, hq'⟩
  have hppos := hpos p hp
  rw [collapsePart_eq_odd hppos] at hq'
  rcases Multiset.mem_replicate.mp hq' with ⟨_, rfl⟩
  exact oddPart_odd hppos.ne'

/-! ## Inverses without residue filters -/

theorem glaisherCollapse_glaisherExpand_odd {s : Multiset ℕ}
    (hOdd : ∀ m ∈ s, m % 2 = 1) :
    glaisherCollapse (glaisherExpand s) = s := by
  classical
  unfold glaisherCollapse glaisherExpand
  rw [Multiset.bind_assoc]
  have hbind :
      (s.dedup.bind fun m => (expandPart m (s.count m)).bind collapsePart) =
        s.dedup.bind fun m => Multiset.replicate (s.count m) m := by
    refine Multiset.bind_congr ?_
    intro m hm
    have hOddm := hOdd m (Multiset.mem_dedup.mp hm)
    exact bind_collapse_expandPart (odd_pos hOddm) hOddm
  rw [hbind, dedup_bind_replicate_count]

theorem mem_glaisherExpand_iff_bit_odd {t : Multiset ℕ}
    (hOdd : ∀ m ∈ t, m % 2 = 1) {q : ℕ} :
    q ∈ glaisherExpand t ↔
      0 < q ∧ (t.count (oddPart q)).testBit (val2 q) = true ∧
        oddPart q ∈ t := by
  classical
  constructor
  · intro hq
    simp only [glaisherExpand, Multiset.mem_bind] at hq
    rcases hq with ⟨m, hm, hq'⟩
    have hOddm := hOdd m (Multiset.mem_dedup.mp hm)
    rcases exists_bit_of_mem_expandPart hq' with ⟨i, rfl, hbit⟩
    have hop := oddPart_mul_pow_odd (odd_pos hOddm) hOddm (j := i)
    have hv := val2_mul_pow_odd (odd_pos hOddm) hOddm (j := i)
    refine ⟨Nat.mul_pos (odd_pos hOddm) (Nat.pow_pos (by decide)), ?_, ?_⟩
    · simpa [hop, hv] using hbit
    · simpa [hop] using Multiset.mem_dedup.mp hm
  · rintro ⟨_hqpos, hbit, hm⟩
    refine Multiset.mem_bind.mpr ?_
    refine ⟨oddPart q, Multiset.mem_dedup.mpr hm, ?_⟩
    have hqeq : q = oddPart q * 2 ^ val2 q := eq_mul_pow_of_oddPart_val2 q
    have hmem :
        oddPart q * 2 ^ val2 q ∈ expandPart (oddPart q) (t.count (oddPart q)) :=
      mem_expandPart_of_bit hbit
    rwa [← hqeq] at hmem

theorem glaisherExpand_glaisherCollapse_nodup {s : Multiset ℕ} (hs : s.Nodup)
    (hpos : ∀ p ∈ s, 0 < p) :
    glaisherExpand (glaisherCollapse s) = s := by
  classical
  have hOdd : ∀ m ∈ glaisherCollapse s, m % 2 = 1 :=
    fun m hm => glaisherCollapse_parts_odd hpos hm
  have hnodupE : (glaisherExpand (glaisherCollapse s)).Nodup :=
    glaisherExpand_nodup_odd hOdd
  rw [Multiset.Nodup.ext hnodupE hs]
  intro q
  constructor
  · intro hq
    rcases (mem_glaisherExpand_iff_bit_odd hOdd).mp hq with ⟨_hqpos, hbit, _hm⟩
    have hbit' :=
      (testBit_count_glaisherCollapse hs hpos (oddPart q) (val2 q)).mp hbit
    rcases hbit' with ⟨p, hps, hop, hval⟩
    have hpq : p = q := by
      calc
        p = oddPart p * 2 ^ val2 p := eq_mul_pow_of_oddPart_val2 p
        _ = oddPart q * 2 ^ val2 q := by rw [hop, hval]
        _ = q := (eq_mul_pow_of_oddPart_val2 q).symm
    rwa [← hpq]
  · intro hq
    refine (mem_glaisherExpand_iff_bit_odd hOdd).mpr ?_
    have hqpos := hpos q hq
    refine ⟨hqpos, ?_, ?_⟩
    · exact (testBit_count_glaisherCollapse hs hpos (oddPart q) (val2 q)).mpr
        ⟨q, hq, rfl, rfl⟩
    · refine Multiset.mem_bind.mpr ⟨q, hq, ?_⟩
      rw [collapsePart_eq_odd hqpos]
      exact Multiset.mem_replicate.mpr ⟨(Nat.pow_pos (by decide)).ne', rfl⟩

/-! ## Partition-level maps (reuse sum-preserving `ofSums` wrappers) -/

/-- Odd → distinct: expand multiplicities of odd kernels into binary parts. -/
abbrev glaisherOddToDistinct {n : ℕ} (p : Partition n) : Partition n :=
  glaisherBtoA_parts p

/-- Distinct → odd: collapse each part `m * 2^k` into `2^k` copies of odd `m`. -/
abbrev glaisherDistinctToOdd {n : ℕ} (p : Partition n) : Partition n :=
  glaisherAtoB_parts p

theorem glaisherOddToDistinct_parts {n : ℕ} {p : Partition n}
    (hp : p ∈ odds n) :
    (glaisherOddToDistinct p).parts = glaisherExpand p.parts := by
  classical
  have hOdd := odds_parts_odd hp
  exact ofSums_parts_eq_of_pos _ (fun x hx => glaisherExpand_pos_odd hOdd hx)

theorem glaisherDistinctToOdd_parts {n : ℕ} {p : Partition n}
    (_hp : p ∈ distincts n) :
    (glaisherDistinctToOdd p).parts = glaisherCollapse p.parts := by
  classical
  have hpos : ∀ x ∈ p.parts, 0 < x := fun x hx => p.parts_pos hx
  have hpos' : ∀ x ∈ glaisherCollapse p.parts, 0 < x :=
    fun x hx => glaisherCollapse_pos hpos hx
  exact ofSums_parts_eq_of_pos _ hpos'

theorem glaisherOddToDistinct_mem {n : ℕ} {p : Partition n} (hp : p ∈ odds n) :
    glaisherOddToDistinct p ∈ distincts n := by
  classical
  have hOdd := odds_parts_odd hp
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  rw [glaisherOddToDistinct_parts hp]
  exact glaisherExpand_nodup_odd hOdd

theorem glaisherDistinctToOdd_mem {n : ℕ} {p : Partition n}
    (hp : p ∈ distincts n) :
    glaisherDistinctToOdd p ∈ odds n := by
  classical
  have hpos : ∀ x ∈ p.parts, 0 < x := fun x hx => p.parts_pos hx
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  intro i hi
  rw [glaisherDistinctToOdd_parts hp] at hi
  exact not_even_iff_mod_two.mpr (glaisherCollapse_parts_odd hpos hi)

theorem glaisherDistinctToOdd_OddToDistinct {n : ℕ} {p : Partition n}
    (hp : p ∈ odds n) :
    glaisherDistinctToOdd (glaisherOddToDistinct p) = p := by
  classical
  have hOD := glaisherOddToDistinct_mem hp
  have hpartsO := glaisherOddToDistinct_parts hp
  have hpartsD := glaisherDistinctToOdd_parts hOD
  have hOdd := odds_parts_odd hp
  apply Partition.ext
  rw [hpartsD, hpartsO, glaisherCollapse_glaisherExpand_odd hOdd]

theorem glaisherOddToDistinct_DistinctToOdd {n : ℕ} {p : Partition n}
    (hp : p ∈ distincts n) :
    glaisherOddToDistinct (glaisherDistinctToOdd p) = p := by
  classical
  have hDO := glaisherDistinctToOdd_mem hp
  have hpartsD := glaisherDistinctToOdd_parts hp
  have hpartsO := glaisherOddToDistinct_parts hDO
  have hs := distincts_nodup hp
  have hpos : ∀ x ∈ p.parts, 0 < x := fun x hx => p.parts_pos hx
  apply Partition.ext
  rw [hpartsO, hpartsD, glaisherExpand_glaisherCollapse_nodup hs hpos]

/-! ## Level A — tiny `native_decide` card guard (not the proof) -/

/-- Guard only: cards match through `n ≤ 10`. Off-by-one / even-kernel
landmines already fail at `n = 2,3,4`. -/
theorem euler_odd_eq_distinct_le_10 :
    ∀ n ≤ 10, (odds n).card = (distincts n).card := by
  intro n hn
  interval_cases n <;> native_decide

/-! ## Level B — ∀ n Glaisher bijection -/

/-- Euler's partition theorem: the number of partitions of `n` into odd
parts equals the number of partitions of `n` into distinct parts.

formalize-only / known-classical (Euler 1748 / Glaisher 1883) / no novelty
claim. Proof is the Glaisher bijection (`Finset.card_bij'`), not Archive
generating functions. -/
theorem euler_odd_eq_distinct (n : ℕ) :
    (odds n).card = (distincts n).card := by
  classical
  refine Finset.card_bij'
    (fun p _ => glaisherOddToDistinct p)
    (fun q _ => glaisherDistinctToOdd q)
    (fun p hp => glaisherOddToDistinct_mem hp)
    (fun q hq => glaisherDistinctToOdd_mem hq)
    (fun p hp => glaisherDistinctToOdd_OddToDistinct hp)
    (fun q hq => glaisherOddToDistinct_DistinctToOdd hq)

end ProofLab.Euler
