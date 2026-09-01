/-
Wolstenholme's theorem (binomial congruence modulo p³).

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 has `Nat.choose` (`Data/Nat/Choose/Basic.lean`), `Nat.ModEq` /
`ZMod`, and `harmonic : ℕ → ℚ` (`NumberTheory/Harmonic/Defs.lean`) —
**definition only**. ZERO Wolstenholme theorem, ZERO `p^3` binomial
congruence under `Mathlib/` or `Archive/`. Completing the namesake is the gap.

Pin: `catalog/problems/wolstenholme-theorem/STATEMENT.md` (OPE-832; Scout
OPE-821 leftover slot #2; Director OPE-831). Encoding: `Nat.choose` +
`Nat.ModEq` + `p.Prime` + `5 ≤ p`. Zero `sorry`. Do not import `Archive.*`.

This is **not** Wilson (`wilsons_lemma` already Mathlib).
This is **not** Lucas binomial (`Data/Nat/Choose/Lucas.lean` already Mathlib).
This is **not** `harmonic_not_int` / harmonic-series divergence (already Mathlib;
different statements). The namesake is the binomial congruence, not
harmonic-in-ℚ.
This is **not** Korselt / Carmichael (consumed PR #86).
This is **not** Euclid–Euler (consumed #80).
This is **not** n-fold inclusion-exclusion (consumed #88).
This is **not** LLL / Vosper / Heron (consumed #85 / #82 / #83).
Do **not** prove Wolstenholme primes / congruence mod `p^4`.
Do **not** use Bernoulli numbers / p-adic zeta / irregular primes.
Leave OPE-403 alone.

v1 is the **binomial p³ congruence**. Level A `choose_mod_p_sq` is the weak
`mod p²` form for `p ≥ 3` and is **not** labelled Wolstenholme. Level B
namesake `wolstenholme` (`mod p³`, `p ≥ 5`) is **not** sorry-ed: the p³
lift (cube expansion + ∑ k⁻² vanishing in F_p) did not close this
heartbeat. Honest partial. `5 ≤ p` remains load-bearing on the namesake.

Transcribed classical argument (J. Wolstenholme, On certain properties of
prime numbers, Q.J. Pure Appl. Math. 5 (1862), 35–39): product expansion
of `(2p−1).choose (p−1) = ∏_{k=1}^{p−1} (1 + p/k)` in `ZMod (p^n)`, with
the harmonic-sum pairing `k⁻¹ + (p−k)⁻¹ = p (k(p−k))⁻¹`.
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option maxHeartbeats 800000

open Nat Finset

namespace ProofLab.Wolstenholme

/-! ## Arithmetic glue -/

lemma two_ne_of_three_le {p : ℕ} (h : 3 ≤ p) : p ≠ 2 := by omega

lemma coprime_two_pow {p n : ℕ} (hp : p.Prime) (h : 3 ≤ p) :
    Nat.Coprime 2 (p ^ n) := by
  have hp2 : p ≠ 2 := two_ne_of_three_le h
  have h2p : Nat.Coprime 2 p := by
    rw [Nat.prime_two.coprime_iff_not_dvd]
    intro hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 hd).symm
  exact h2p.pow_right n

lemma coprime_of_mem_Ico {p n k : ℕ} (hp : p.Prime) (hk : k ∈ Ico 1 p) :
    Nat.Coprime k (p ^ n) := by
  have hk' := mem_Ico.mp hk
  have hkp : Nat.Coprime k p := by
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    intro hd
    have : p ≤ k := Nat.le_of_dvd hk'.1 hd
    omega
  exact hkp.pow_right n

lemma mem_Ico_const_sub {p k : ℕ} (hk : k ∈ Ico 1 p) : p - k ∈ Ico 1 p := by
  have hk' := mem_Ico.mp hk
  have hle : k ≤ p := hk'.2.le
  have hpos : 0 < k := hk'.1
  rw [mem_Ico]
  constructor
  · exact Nat.le_sub_of_add_le (by omega : 1 + k ≤ p)
  · exact Nat.sub_lt (lt_of_lt_of_le hpos hle) hpos

lemma isUnit_of_mem_Ico {p n k : ℕ} (hp : p.Prime) (hk : k ∈ Ico 1 p) :
    IsUnit (k : ZMod (p ^ n)) :=
  (ZMod.isUnit_iff_coprime k (p ^ n)).2 (coprime_of_mem_Ico (n := n) hp hk)

lemma mul_inv_of_mem_Ico {p n k : ℕ} (hp : p.Prime) (hk : k ∈ Ico 1 p) :
    (k : ZMod (p ^ n)) * (k : ZMod (p ^ n))⁻¹ = 1 :=
  ZMod.mul_inv_of_unit _ (isUnit_of_mem_Ico (n := n) hp hk)

lemma two_mul_inv {p n : ℕ} (hp : p.Prime) (h3 : 3 ≤ p) :
    (2 : ZMod (p ^ n)) * (2 : ZMod (p ^ n))⁻¹ = 1 :=
  ZMod.mul_inv_of_unit _ ((ZMod.isUnit_iff_coprime 2 (p ^ n)).2 (coprime_two_pow hp h3))

lemma p_pow_cast_eq_zero (p n : ℕ) : ((p : ZMod (p ^ n)) ^ n) = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_self]

/-! ## Product expansion modulo `x² = 0` -/

lemma prod_one_add_of_sq_eq_zero {ι α : Type*} [CommRing α] [DecidableEq ι]
    (x : α) (hx : x ^ 2 = 0) (s : Finset ι) (f : ι → α) :
    ∏ i ∈ s, (1 + x * f i) = 1 + x * ∑ i ∈ s, f i := by
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha ih
    rw [prod_insert ha, sum_insert ha, ih]
    have hxx : x * x = 0 := by rwa [← sq]
    calc
      (1 + x * f a) * (1 + x * ∑ i ∈ s, f i)
          = 1 + x * ∑ i ∈ s, f i + x * f a
              + x * x * (f a * ∑ i ∈ s, f i) := by ring
      _ = 1 + x * ∑ i ∈ s, f i + x * f a := by simp [hxx]
      _ = 1 + x * (f a + ∑ i ∈ s, f i) := by ring

/-! ## Choose as a product of `(1 + p k⁻¹)` -/

lemma descFactorial_two_mul_sub_one {p : ℕ} (hp : 2 ≤ p) :
    (2 * p - 1).descFactorial (p - 1) = ∏ k ∈ Ico 1 p, (p + k) := by
  have hp1 : 1 ≤ p - 1 := Nat.le_sub_of_add_le (by omega : 2 ≤ p)
  have hppos : 0 < p := lt_of_lt_of_le (by decide : 0 < 2) hp
  rw [descFactorial_eq_prod_range]
  refine prod_nbij' (fun i => p - 1 - i) (fun k => p - 1 - k) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    have hlt : i < p - 1 := mem_range.mp hi
    rw [mem_Ico]
    constructor
    · have : 1 + i ≤ p - 1 := by
        rw [add_comm]
        exact Nat.succ_le_of_lt hlt
      exact Nat.le_sub_of_add_le this
    · exact Nat.lt_of_le_of_lt (Nat.sub_le (p - 1) i)
        (Nat.sub_lt hppos (by decide : 0 < 1))
  · intro k hk
    have hk' := mem_Ico.mp hk
    rw [mem_range]
    exact Nat.sub_lt hp1 hk'.1
  · intro i hi
    exact Nat.sub_sub_self (Nat.le_of_lt (mem_range.mp hi))
  · intro k hk
    exact Nat.sub_sub_self (Nat.le_pred_of_lt (mem_Ico.mp hk).2)
  · intro i hi
    have hle : i ≤ p - 1 := Nat.le_of_lt (mem_range.mp hi)
    have hsum : p + (p - 1) = 2 * p - 1 := by omega
    calc
      2 * p - 1 - i = p + (p - 1) - i := by rw [hsum]
      _ = p + (p - 1 - i) := Nat.add_sub_assoc hle p

lemma factorial_eq_prod_Ico {p : ℕ} (hp : 1 ≤ p) :
    (p - 1)! = ∏ k ∈ Ico 1 p, k := by
  have h := (prod_Ico_id_eq_factorial (p - 1)).symm
  have : p - 1 + 1 = p := Nat.sub_add_cancel hp
  simpa [this] using h

lemma choose_mul_factorial_eq_prod {p : ℕ} (hp : 2 ≤ p) :
    (2 * p - 1).choose (p - 1) * (p - 1)! = ∏ k ∈ Ico 1 p, (p + k) := by
  rw [mul_comm, ← descFactorial_eq_factorial_mul_choose (2 * p - 1) (p - 1)]
  exact descFactorial_two_mul_sub_one hp

lemma add_p_eq_mul_one_add {p n k : ℕ} (hp : p.Prime) (hk : k ∈ Ico 1 p) :
    ((p + k : ℕ) : ZMod (p ^ n)) =
      (k : ZMod (p ^ n)) *
        (1 + (p : ZMod (p ^ n)) * (k : ZMod (p ^ n))⁻¹) := by
  have hkk : (k : ZMod (p ^ n)) * (k : ZMod (p ^ n))⁻¹ = 1 :=
    mul_inv_of_mem_Ico hp hk
  rw [Nat.cast_add, mul_add, mul_one, add_comm]
  congr 1
  rw [← mul_assoc, mul_comm (k : ZMod (p ^ n)) p, mul_assoc, hkk, mul_one]

lemma prod_add_p_eq {p n : ℕ} (hp : p.Prime) :
    ∏ k ∈ Ico 1 p, ((p + k : ℕ) : ZMod (p ^ n)) =
      (∏ k ∈ Ico 1 p, (k : ZMod (p ^ n))) *
        ∏ k ∈ Ico 1 p, (1 + (p : ZMod (p ^ n)) * (k : ZMod (p ^ n))⁻¹) := by
  rw [← prod_mul_distrib]
  refine prod_congr rfl fun k hk => add_p_eq_mul_one_add hp hk

lemma prod_k_mul_prod_inv {p n : ℕ} (hp : p.Prime) :
    (∏ k ∈ Ico 1 p, (k : ZMod (p ^ n))) *
      ∏ k ∈ Ico 1 p, (k : ZMod (p ^ n))⁻¹ = 1 := by
  rw [← prod_mul_distrib]
  exact prod_eq_one fun k hk => mul_inv_of_mem_Ico hp hk

lemma choose_eq_prod_one_add {p n : ℕ} (hp : p.Prime) (h2 : 2 ≤ p) :
    ((2 * p - 1).choose (p - 1) : ZMod (p ^ n)) =
      ∏ k ∈ Ico 1 p, (1 + (p : ZMod (p ^ n)) * (k : ZMod (p ^ n))⁻¹) := by
  have hp1 : 1 ≤ p := le_trans (by decide : 1 ≤ 2) h2
  have hnat := choose_mul_factorial_eq_prod h2
  have hfac := factorial_eq_prod_Ico hp1
  have hcast :
      ((2 * p - 1).choose (p - 1) : ZMod (p ^ n)) *
          ∏ k ∈ Ico 1 p, (k : ZMod (p ^ n)) =
        ∏ k ∈ Ico 1 p, ((p + k : ℕ) : ZMod (p ^ n)) := by
    have h1 :
        ((2 * p - 1).choose (p - 1) : ZMod (p ^ n)) * ((p - 1)! : ZMod (p ^ n)) =
          ∏ k ∈ Ico 1 p, ((p + k : ℕ) : ZMod (p ^ n)) := by
      rw [← Nat.cast_mul, hnat, Nat.cast_prod]
    have h2 : ((p - 1)! : ZMod (p ^ n)) = ∏ k ∈ Ico 1 p, (k : ZMod (p ^ n)) := by
      rw [hfac, Nat.cast_prod]
    rwa [h2] at h1
  have hP := prod_add_p_eq (n := n) hp
  have hcancel := prod_k_mul_prod_inv (n := n) hp
  have hP' := hcast.trans hP
  calc
    ((2 * p - 1).choose (p - 1) : ZMod (p ^ n))
        = ((2 * p - 1).choose (p - 1) : ZMod (p ^ n)) * 1 := by rw [mul_one]
    _ = ((2 * p - 1).choose (p - 1) : ZMod (p ^ n)) *
          ((∏ k ∈ Ico 1 p, (k : ZMod (p ^ n))) *
            ∏ k ∈ Ico 1 p, (k : ZMod (p ^ n))⁻¹) := by rw [hcancel]
    _ = (((2 * p - 1).choose (p - 1) : ZMod (p ^ n)) *
          ∏ k ∈ Ico 1 p, (k : ZMod (p ^ n))) *
            ∏ k ∈ Ico 1 p, (k : ZMod (p ^ n))⁻¹ := by rw [mul_assoc]
    _ = ((∏ k ∈ Ico 1 p, (k : ZMod (p ^ n))) *
          ∏ k ∈ Ico 1 p, (1 + (p : ZMod (p ^ n)) * (k : ZMod (p ^ n))⁻¹)) *
            ∏ k ∈ Ico 1 p, (k : ZMod (p ^ n))⁻¹ := by rw [hP']
    _ = (∏ k ∈ Ico 1 p, (1 + (p : ZMod (p ^ n)) * (k : ZMod (p ^ n))⁻¹)) *
          ((∏ k ∈ Ico 1 p, (k : ZMod (p ^ n))) *
            ∏ k ∈ Ico 1 p, (k : ZMod (p ^ n))⁻¹) := by
          ac_rfl
    _ = (∏ k ∈ Ico 1 p, (1 + (p : ZMod (p ^ n)) * (k : ZMod (p ^ n))⁻¹)) * 1 := by
          rw [hcancel]
    _ = ∏ k ∈ Ico 1 p, (1 + (p : ZMod (p ^ n)) * (k : ZMod (p ^ n))⁻¹) := by
          rw [mul_one]

/-! ## Pairing of inverses -/

lemma add_inv_pair {p n k : ℕ} (hp : p.Prime) (hk : k ∈ Ico 1 p) :
    (k : ZMod (p ^ n))⁻¹ + ((p - k : ℕ) : ZMod (p ^ n))⁻¹ =
      (p : ZMod (p ^ n)) * ((k * (p - k) : ℕ) : ZMod (p ^ n))⁻¹ := by
  set m := p - k
  have hm : m ∈ Ico 1 p := mem_Ico_const_sub hk
  have hk' := mem_Ico.mp hk
  have hkm : k + m = p := Nat.add_sub_of_le hk'.2.le
  have hkk : (k : ZMod (p ^ n)) * (k : ZMod (p ^ n))⁻¹ = 1 := mul_inv_of_mem_Ico hp hk
  have hmm : (m : ZMod (p ^ n)) * (m : ZMod (p ^ n))⁻¹ = 1 := mul_inv_of_mem_Ico hp hm
  have hprod_unit :
      ((k * m : ℕ) : ZMod (p ^ n)) * ((k : ZMod (p ^ n))⁻¹ * (m : ZMod (p ^ n))⁻¹) = 1 := by
    rw [Nat.cast_mul]
    calc
      (k : ZMod (p ^ n)) * m * ((k : ZMod (p ^ n))⁻¹ * (m : ZMod (p ^ n))⁻¹)
          = (k * (k : ZMod (p ^ n))⁻¹) * (m * (m : ZMod (p ^ n))⁻¹) := by ring
      _ = 1 * 1 := by rw [hkk, hmm]
      _ = 1 := by rw [mul_one]
  have hinv_prod :
      ((k * m : ℕ) : ZMod (p ^ n))⁻¹ = (k : ZMod (p ^ n))⁻¹ * (m : ZMod (p ^ n))⁻¹ :=
    ZMod.inv_eq_of_mul_eq_one (p ^ n) _ _ hprod_unit
  calc
    (k : ZMod (p ^ n))⁻¹ + (m : ZMod (p ^ n))⁻¹
        = (k : ZMod (p ^ n))⁻¹ * (m * (m : ZMod (p ^ n))⁻¹)
            + (k * (k : ZMod (p ^ n))⁻¹) * (m : ZMod (p ^ n))⁻¹ := by
          rw [hmm, hkk, mul_one, one_mul]
    _ = ((k : ZMod (p ^ n))⁻¹ * (m : ZMod (p ^ n))⁻¹) * (m + k) := by ring
    _ = ((k * m : ℕ) : ZMod (p ^ n))⁻¹ * (k + m) := by
          rw [← hinv_prod, add_comm]
    _ = ((k * m : ℕ) : ZMod (p ^ n))⁻¹ * ((k + m : ℕ) : ZMod (p ^ n)) := by
          rw [Nat.cast_add]
    _ = ((k * m : ℕ) : ZMod (p ^ n))⁻¹ * p := by rw [hkm]
    _ = p * ((k * m : ℕ) : ZMod (p ^ n))⁻¹ := by rw [mul_comm]

lemma sum_inv_eq_sum_sub_inv {p n : ℕ} (hp : p.Prime) :
    ∑ k ∈ Ico 1 p, (k : ZMod (p ^ n))⁻¹ =
      ∑ k ∈ Ico 1 p, ((p - k : ℕ) : ZMod (p ^ n))⁻¹ := by
  refine sum_nbij' (fun k => p - k) (fun k => p - k)
    (fun k hk => mem_Ico_const_sub hk)
    (fun k hk => mem_Ico_const_sub hk)
    (fun k hk => Nat.sub_sub_self (mem_Ico.mp hk).2.le)
    (fun k hk => Nat.sub_sub_self (mem_Ico.mp hk).2.le)
    (fun k hk => by
      have : p - (p - k) = k := Nat.sub_sub_self (mem_Ico.mp hk).2.le
      simp [this])

lemma two_mul_sum_inv {p n : ℕ} (hp : p.Prime) :
    2 * ∑ k ∈ Ico 1 p, (k : ZMod (p ^ n))⁻¹ =
      (p : ZMod (p ^ n)) *
        ∑ k ∈ Ico 1 p, ((k * (p - k) : ℕ) : ZMod (p ^ n))⁻¹ := by
  have hre := sum_inv_eq_sum_sub_inv (n := n) hp
  calc
    2 * ∑ k ∈ Ico 1 p, (k : ZMod (p ^ n))⁻¹
        = ∑ k ∈ Ico 1 p, (k : ZMod (p ^ n))⁻¹
            + ∑ k ∈ Ico 1 p, (k : ZMod (p ^ n))⁻¹ := by rw [two_mul]
    _ = ∑ k ∈ Ico 1 p, (k : ZMod (p ^ n))⁻¹
            + ∑ k ∈ Ico 1 p, ((p - k : ℕ) : ZMod (p ^ n))⁻¹ := by rw [hre]
    _ = ∑ k ∈ Ico 1 p,
          ((k : ZMod (p ^ n))⁻¹ + ((p - k : ℕ) : ZMod (p ^ n))⁻¹) := by
          rw [← sum_add_distrib]
    _ = ∑ k ∈ Ico 1 p,
          (p : ZMod (p ^ n)) * ((k * (p - k) : ℕ) : ZMod (p ^ n))⁻¹ := by
          refine sum_congr rfl fun k hk => add_inv_pair hp hk
    _ = (p : ZMod (p ^ n)) *
          ∑ k ∈ Ico 1 p, ((k * (p - k) : ℕ) : ZMod (p ^ n))⁻¹ := by
          rw [mul_sum]

/-! ## Level A — congruence modulo `p²` (not labelled Wolstenholme) -/

lemma p_mul_sum_inv_eq_zero_mod_p_sq {p : ℕ} (hp : p.Prime) (h3 : 3 ≤ p) :
    (p : ZMod (p ^ 2)) * ∑ k ∈ Ico 1 p, (k : ZMod (p ^ 2))⁻¹ = 0 := by
  have h2S := two_mul_sum_inv (n := 2) hp
  have hxx : ((p : ZMod (p ^ 2)) ^ 2) = 0 := p_pow_cast_eq_zero p 2
  have h2pS :
      (2 : ZMod (p ^ 2)) * ((p : ZMod (p ^ 2)) *
        ∑ k ∈ Ico 1 p, (k : ZMod (p ^ 2))⁻¹) = 0 := by
    calc
      (2 : ZMod (p ^ 2)) * (p * ∑ k ∈ Ico 1 p, (k : ZMod (p ^ 2))⁻¹)
          = p * (2 * ∑ k ∈ Ico 1 p, (k : ZMod (p ^ 2))⁻¹) := by ring
      _ = p * (p * ∑ k ∈ Ico 1 p, ((k * (p - k) : ℕ) : ZMod (p ^ 2))⁻¹) := by
            rw [h2S]
      _ = (p * p) * ∑ k ∈ Ico 1 p, ((k * (p - k) : ℕ) : ZMod (p ^ 2))⁻¹ := by ring
      _ = (p ^ 2) * ∑ k ∈ Ico 1 p, ((k * (p - k) : ℕ) : ZMod (p ^ 2))⁻¹ := by
            rw [← pow_two]
      _ = 0 := by simp [hxx]
  have h2u := two_mul_inv (n := 2) hp h3
  calc
    (p : ZMod (p ^ 2)) * ∑ k ∈ Ico 1 p, (k : ZMod (p ^ 2))⁻¹
        = 1 * (p * ∑ k ∈ Ico 1 p, (k : ZMod (p ^ 2))⁻¹) := by rw [one_mul]
    _ = ((2 : ZMod (p ^ 2)) * (2 : ZMod (p ^ 2))⁻¹) *
          (p * ∑ k ∈ Ico 1 p, (k : ZMod (p ^ 2))⁻¹) := by rw [h2u]
    _ = (2 : ZMod (p ^ 2))⁻¹ *
          ((2 : ZMod (p ^ 2)) * (p * ∑ k ∈ Ico 1 p, (k : ZMod (p ^ 2))⁻¹)) := by
          ring
    _ = (2 : ZMod (p ^ 2))⁻¹ * 0 := by rw [h2pS]
    _ = 0 := by simp

lemma choose_eq_one_mod_p_sq {p : ℕ} (hp : p.Prime) (h3 : 3 ≤ p) :
    ((2 * p - 1).choose (p - 1) : ZMod (p ^ 2)) = 1 := by
  have h2 : 2 ≤ p := le_trans (by decide : 2 ≤ 3) h3
  rw [choose_eq_prod_one_add hp h2]
  have hx : ((p : ZMod (p ^ 2)) ^ 2) = 0 := p_pow_cast_eq_zero p 2
  rw [prod_one_add_of_sq_eq_zero (p : ZMod (p ^ 2)) hx]
  simp [p_mul_sum_inv_eq_zero_mod_p_sq hp h3]

/-- Level A: the weak `mod p²` form. **Not** labelled Wolstenholme.
Holds for every prime `p ≥ 3` (`p = 3` holds mod 9 and fails mod 27). -/
theorem choose_mod_p_sq {p : ℕ} (hp : p.Prime) (h3 : 3 ≤ p) :
    (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 2] := by
  rw [← ZMod.eq_iff_modEq_nat, Nat.cast_one]
  exact choose_eq_one_mod_p_sq hp h3

end ProofLab.Wolstenholme
