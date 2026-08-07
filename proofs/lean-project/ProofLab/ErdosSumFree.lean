import Mathlib.Data.Nat.Defs
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Tactic

open scoped BigOperators

namespace ProofLab.SumFree

/-!
# Erdős (1965) Z_p averaging proof — OPE-23 (development file)

Target: every finite set S ⊆ ℕ has a sum-free subset A with `3 * A.card ≥ S.card`.

Proved steps (zero sorries):
1. `middle_third_sumfree` — the middle third I={k | p<3k<2p} is sum-free in ℤ_p
   (reduced sum of two middle-third reps leaves the middle third).
2. `middleThird_mem` — membership unfolding for I.
3. `fiber_sum_free` — for any multiplier t, the fiber
   A_t = {s ∈ S | (t·s) % p ∈ I} is sum-free in ℕ (lift via linearity of t·x).

Remaining (tracked OPE-32/33):
4. Averaging: Σ_{t∈units} |A_t| = |S|·|I|, so some t has 3·|A_t| ≥ |S|.
5. Prime existence p > max(S) (Nat.exists_infinite_primes) and wiring into
   `SumFree.lean`'s main theorem (zero-sorry `lake build`).

This is a WORK-IN-PROGRESS development file; it never shadows `SumFree.lean`.
-/

/-- IsSumFree predicate, matching SumFree.lean. -/
def IsSumFree (A : Finset ℕ) : Prop :=
  ∀ x y z, x ∈ A → y ∈ A → z ∈ A → x + y ≠ z

/-- CORE (proved): if a, b are in the middle third, the reduced sum
    (a + b) % p avoids the middle third: 3·((a+b)%p) ≤ p or 2p ≤ 3·((a+b)%p). -/
lemma middle_third_sumfree (p a b : ℕ) (hp : 0 < p)
    (ha1 : p < 3 * a) (ha2 : 3 * a < 2 * p)
    (hb1 : p < 3 * b) (hb2 : 3 * b < 2 * p) :
    (3 * ((a + b) % p) ≤ p) ∨ (2 * p ≤ 3 * ((a + b) % p)) := by
  by_cases hab : a + b < p
  · have hlt : (a + b) % p = a + b := Nat.mod_eq_of_lt hab
    right
    rw [hlt]
    nlinarith
  · have hge : p ≤ a + b := Nat.le_of_not_gt hab
    have hsub_lt : a + b - p < p := by omega
    have hsub : (a + b) % p = a + b - p := by
      rw [Nat.mod_eq_sub_mod hge]
      exact Nat.mod_eq_of_lt hsub_lt
    left
    have h4 : 3 * (a + b) < 4 * p := by nlinarith
    omega

/-- The middle third I = {k | p < 3k ∧ 3k < 2p}. -/
def middleThird (p : ℕ) : Finset ℕ :=
  (Finset.range (2 * p)).filter (fun k => p < 3 * k ∧ 3 * k < 2 * p)

/-- Membership in the middle third. -/
lemma middleThird_mem {p k : ℕ} (h : k ∈ middleThird p) :
    p < 3 * k ∧ 3 * k < 2 * p := by
  simp [middleThird] at h
  exact h.2

/-- Fiber A_t = {s ∈ S | (t·s) % p ∈ I} is sum-free.
    x+y ∈ S ⟹ t·(x+y)=t·z ⟹ (a+b) ≡ p (t·z) mod p (a=(t·x)%p,b=(t·y)%p).
    a,b ∈ I so (a+b)%p avoids I by `middle_third_sumfree`, contradicting
    that z ∈ A_t says (t·z)%p ∈ I. ✓ -/
lemma fiber_sum_free {p t : ℕ} (hp : 0 < p) (S : Finset ℕ) :
    IsSumFree (S.filter (fun s => (t * s) % p ∈ middleThird p)) := by
  unfold IsSumFree
  intro x y z hx hy hz hsum
  simp at hx hy hz
  rcases hx with ⟨hxS, hxI⟩
  rcases hy with ⟨hyS, hyI⟩
  rcases hz with ⟨hzS, hzI⟩
  let a := (t * x) % p
  let b := (t * y) % p
  have ha1 : p < 3 * a := (middleThird_mem hxI).1
  have ha2 : 3 * a < 2 * p := (middleThird_mem hxI).2
  have hb1 : p < 3 * b := (middleThird_mem hyI).1
  have hb2 : 3 * b < 2 * p := (middleThird_mem hyI).2
  have hlin : t * x + t * y = t * z := by
    rw [← mul_add t x y]
    rw [hsum]
  have hcond : (a + b) % p ≡ (t * z) % p [MOD p] := by
    have h1 : a ≡ t * x [MOD p] := by
      dsimp [a]
      exact Nat.mod_modEq (t * x) p
    have h2 : b ≡ t * y [MOD p] := by
      dsimp [b]
      exact Nat.mod_modEq (t * y) p
    have hab : a + b ≡ t * x + t * y [MOD p] := Nat.ModEq.add h1 h2
    have htr : t * x + t * y ≡ t * z [MOD p] := by rw [hlin]
    have heq : a + b ≡ t * z [MOD p] := hab.trans htr
    have hmm : (a + b) % p ≡ a + b [MOD p] := Nat.mod_modEq (a + b) p
    have hptr : (a + b) % p ≡ t * z [MOD p] := hmm.trans heq
    have hzmod : (t * z) % p ≡ t * z [MOD p] := Nat.mod_modEq (t * z) p
    exact hptr.trans hzmod.symm
  have heq : (a + b) % p = (t * z) % p :=
    hcond.eq_of_lt_of_lt (Nat.mod_lt _ hp) (Nat.mod_lt _ hp)
  have hzI' : p < 3 * ((t * z) % p) ∧ 3 * ((t * z) % p) < 2 * p := middleThird_mem hzI
  have hred : p < 3 * ((a + b) % p) ∧ 3 * ((a + b) % p) < 2 * p := by
    simpa [heq] using hzI'
  rcases middle_third_sumfree p a b hp ha1 ha2 hb1 hb2 with hlo | hhi
  · omega
  · omega

/-! ## OPE-34: Erdős averaging over unit multipliers

Step 4 of the OPE-23 plan.  For `t ∈ (F_p)^*` (represented by `1..p-1`) let
`A_t = {s ∈ S | (t·s) % p ∈ I}`.  Multiplication by a fixed unit `s` permutes
`(F_p)^*`, so each `s ∈ S` is hit exactly `|I|` times:

    Σ_{t ∈ units} |A_t| = |S| · |I|                            (`averaging_sum`)

Combined with the middle-third size bound `3·|I| ≥ p-1 = #units`
(`middle_third_count_bound`, OPE-30) a pigeonhole argument yields:

    ∃ t, 3·|A_t| ≥ |S|                                         (`averaging_bound`)
-/

/-- The set of unit multipliers `(F_p)^*` as nonzero residues `{1..p-1}`. -/
def unitsRes (p : ℕ) : Finset ℕ := (Finset.range p).erase 0

/-- The middle third avoids `0` and stays below `p`, hence lies in the units. -/
lemma middleThird_subset_units (p : ℕ) (hp : 2 ≤ p) :
    middleThird p ⊆ unitsRes p := by
  intro k hk
  have h1 : p < 3 * k := (middleThird_mem hk).1
  have h2 : 3 * k < 2 * p := (middleThird_mem hk).2
  rw [unitsRes]
  rw [Finset.mem_erase, Finset.mem_range]
  constructor
  · intro hk0
    subst k
    omega
  · exact (by nlinarith)

/-- A unit representative `s` satisfies `0 < s`. -/
lemma units_mem_pos {p s : ℕ} (hs : s ∈ unitsRes p) : 0 < s := by
  rw [unitsRes] at hs
  exact Nat.pos_of_ne_zero (Finset.mem_erase.mp hs).1

/-- A unit representative `s` satisfies `s < p`. -/
lemma units_mem_lt {p s : ℕ} (hs : s ∈ unitsRes p) : s < p := by
  rw [unitsRes] at hs
  exact Finset.mem_range.mp (Finset.mem_erase.mp hs).2

/-- Units are coprime to `p` (primality of `p` is essential). -/
lemma coprime_of_mem_units {p s : ℕ} (hp : p.Prime) (hs : s ∈ unitsRes p) :
    Nat.Coprime p s := by
  exact (hp.coprime_iff_not_dvd).2 (Nat.not_dvd_of_pos_of_lt (units_mem_pos hs) (units_mem_lt hs))

/-- `t ↦ (t·s) % p` maps units into units: a prime times no factor is never
    divisible by `p`, so the residue is a nonzero class. -/
lemma mul_units_mem {p s t : ℕ} (hp : p.Prime) (hs : s ∈ unitsRes p) (ht : t ∈ unitsRes p) :
    (t * s) % p ∈ unitsRes p := by
  have hp2 : 2 ≤ p := hp.two_le
  rw [unitsRes]
  rw [Finset.mem_erase, Finset.mem_range]
  constructor
  · have hnd : ¬ p ∣ t * s := by
      intro hdiv
      rcases (hp.dvd_mul.mp hdiv) with hpt | hps
      · exact (Nat.not_dvd_of_pos_of_lt (units_mem_pos ht) (units_mem_lt ht)) hpt
      · exact (Nat.not_dvd_of_pos_of_lt (units_mem_pos hs) (units_mem_lt hs)) hps
    intro hz
    exact hnd ((Nat.dvd_iff_mod_eq_zero p (t * s)).mpr hz)
  · exact Nat.mod_lt (t * s) (by omega : 0 < p)

/-- Multiplication by a unit `s` is injective on the units mod `p`. -/
lemma mul_units_injective {p s : ℕ} (hp : p.Prime) (hs : s ∈ unitsRes p) :
    Set.InjOn (fun t => (t * s) % p) (unitsRes p) := by
  intro t₁ ht₁ t₂ ht₂ h
  have hc : Nat.Coprime p s := coprime_of_mem_units hp hs
  have hmod : t₁ ≡ t₂ [MOD p] := by
    apply Nat.ModEq.cancel_left_of_coprime hc
    simpa [mul_comm] using h
  exact Nat.ModEq.eq_of_lt_of_lt hmod (units_mem_lt ht₁) (units_mem_lt ht₂)

/-- The image of the units under multiplication by a unit `s` is all of the units. -/
lemma mul_image_units {p s : ℕ} (hp : p.Prime) (hs : s ∈ unitsRes p) :
    (unitsRes p).image (fun t => (t * s) % p) = unitsRes p := by
  have hsub : (unitsRes p).image (fun t => (t * s) % p) ⊆ unitsRes p := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨t, ht, rfl⟩
    exact mul_units_mem hp hs ht
  have hcard : ((unitsRes p).image (fun t => (t * s) % p)).card = (unitsRes p).card :=
    Finset.card_image_of_injOn (mul_units_injective hp hs)
  exact Finset.eq_of_subset_of_card_le hsub (by simp [hcard])

/-- For a fixed unit `s`, the multiplier sum of indicators is exactly `|I|`:
    as `t` runs over the units, `(t·s) % p` runs over the units once each. -/
lemma inner_sum_units (p : ℕ) (hp : p.Prime) {s : ℕ} (hs : s ∈ unitsRes p) :
    (∑ t in unitsRes p, if (t * s) % p ∈ middleThird p then (1 : ℕ) else 0)
      = (middleThird p).card := by
  have hmap : (unitsRes p).image (fun t => (t * s) % p) = unitsRes p := mul_image_units hp hs
  have hinj : Set.InjOn (fun t => (t * s) % p) (unitsRes p) := mul_units_injective hp hs
  have hp2 : 2 ≤ p := hp.two_le
  calc
    (∑ t in unitsRes p, if (t * s) % p ∈ middleThird p then (1 : ℕ) else 0)
        = (∑ u in (unitsRes p).image (fun t => (t * s) % p),
            if u ∈ middleThird p then (1 : ℕ) else 0) := by
            symm
            exact Finset.sum_image hinj
    _ = (∑ u in unitsRes p, if u ∈ middleThird p then (1 : ℕ) else 0) := by rw [hmap]
    _ = ((unitsRes p).filter (fun u => u ∈ middleThird p)).card := by
            exact (Finset.card_filter (fun u => u ∈ middleThird p) (unitsRes p)).symm
    _ = (middleThird p).card := by
            congr 1
            ext u
            simp only [Finset.mem_filter]
            constructor
            · rintro ⟨_, hu⟩
              exact hu
            · intro hu
              exact ⟨middleThird_subset_units p hp2 hu, hu⟩

/-- **Averaging identity** (Erdős step 4): `Σ_{t ∈ (F_p)^*} |A_t| = |S| · |I|`. -/
theorem averaging_sum (p : ℕ) (hp : p.Prime) (S : Finset ℕ) (hS : S ⊆ unitsRes p) :
    (∑ t in unitsRes p,
        (S.filter (fun s => (t * s) % p ∈ middleThird p)).card)
      = S.card * (middleThird p).card := by
  calc
    (∑ t in unitsRes p, (S.filter (fun s => (t * s) % p ∈ middleThird p)).card)
        = ∑ t in unitsRes p,
            ∑ s in S, if (t * s) % p ∈ middleThird p then (1 : ℕ) else 0 := by
            apply Finset.sum_congr rfl
            intro t _
            rw [Finset.card_filter]
    _ = ∑ s in S, ∑ t in unitsRes p,
            if (t * s) % p ∈ middleThird p then (1 : ℕ) else 0 := by
            exact Finset.sum_comm (s := unitsRes p) (t := S)
              (f := fun t s => if (t * s) % p ∈ middleThird p then (1 : ℕ) else 0)
    _ = ∑ s in S, (middleThird p).card := by
            apply Finset.sum_congr rfl
            intro s hs
            exact inner_sum_units p hp (hS hs)
    _ = S.card * (middleThird p).card := by
            simp [Finset.sum_const]

/-- `1` is a unit multiplier (needs `p ≥ 2` so `1 < p`). -/
lemma one_mem_units (p : ℕ) (hp : 2 ≤ p) : 1 ∈ unitsRes p := by
  rw [unitsRes]
  rw [Finset.mem_erase, Finset.mem_range]
  exact ⟨by norm_num, by omega⟩

/-- Cardinality of the unit set: `|{1..p-1}| = p-1`. -/
lemma unitsRes_card (p : ℕ) (hp : 1 ≤ p) : (unitsRes p).card = p - 1 := by
  rw [unitsRes]
  have hmem : 0 ∈ Finset.range p := Finset.mem_range.mpr (by omega)
  have hcard : ((Finset.range p).erase 0).card + 1 = p := by
    rw [Finset.card_erase_add_one hmem]
    exact Finset.card_range p
  omega

/-- **Averaging bound** (Erdős step 4): if `3·|I| ≥ p-1` then some multiplier `t`
    has `3·|A_t| ≥ |S|`.  Pigeonhole against `Σ |A_t| = |S|·|I|`. -/
theorem averaging_bound (p : ℕ) (hp : p.Prime) (S : Finset ℕ) (hS : S ⊆ unitsRes p)
    (hI : 3 * (middleThird p).card ≥ p - 1) :
    ∃ t ∈ unitsRes p, 3 * (S.filter (fun s => (t * s) % p ∈ middleThird p)).card ≥ S.card := by
  by_cases hS0 : S.card = 0
  · rcases (show ∃ t, t ∈ unitsRes p from
        ⟨1, one_mem_units p (by exact hp.two_le)⟩) with ⟨t, ht⟩
    refine ⟨t, ht, ?_⟩
    have hSempty : S = ∅ := Finset.card_eq_zero.mp hS0
    simp [hSempty]
  · have hp2 : 2 ≤ p := hp.two_le
    have hp1 : 1 ≤ p := by omega
    let A := fun t : ℕ => S.filter (fun s => (t * s) % p ∈ middleThird p)
    by_contra hn
    push_neg at hn
    have hsum3 : (∑ t in unitsRes p, 3 * (A t).card) = 3 * (∑ t in unitsRes p, (A t).card) := by
      simp [Finset.mul_sum]
    have hsum : (∑ t in unitsRes p, (A t).card) = S.card * (middleThird p).card := by
      simpa [A] using (averaging_sum p hp S hS)
    have hmid : S.card * (p - 1) ≤ 3 * (S.card * (middleThird p).card) := by
      have hm := Nat.mul_le_mul_left S.card hI
      simpa [mul_assoc, mul_comm, mul_left_comm] using hm
    have hcardu : S.card * (p - 1) = S.card * (unitsRes p).card := by
      rw [unitsRes_card p hp1]
    have hlo : S.card * (unitsRes p).card ≤ ∑ t in unitsRes p, 3 * (A t).card := by
      nlinarith [hsum3, hsum, hmid, hcardu]
    have hterm_le' : ∀ t ∈ unitsRes p, 3 * (A t).card ≤ S.card := by
      intro t ht
      have hlt : 3 * (A t).card < S.card := hn t ht
      omega
    rcases (show ∃ t₀ ∈ unitsRes p, True from
        ⟨1, one_mem_units p hp2, True.intro⟩) with ⟨t₀, ht₀, _⟩
    have hterm_strict : ∃ t ∈ unitsRes p, 3 * (A t).card < S.card := ⟨t₀, ht₀, hn t₀ ht₀⟩
    have hsum_lt : (∑ t in unitsRes p, 3 * (A t).card) < (unitsRes p).card * S.card := by
      have hcore := Finset.sum_lt_sum hterm_le' hterm_strict
      have hconst : (∑ t in unitsRes p, S.card) = (unitsRes p).card * S.card := by
        simp [Finset.sum_const]
      simpa [hconst] using hcore
    nlinarith [hsum_lt, hlo]

end ProofLab.SumFree