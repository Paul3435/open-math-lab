/-
Ostrowski 1916 for nontrivial `MulRingNorm ℚ` — Level A unbounded/archimedean
engine only.

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 `NumberTheory/Ostrowski.lean` has the **bounded** half
`mulRingNorm_equiv_padic_of_bounded` (infra — **USE, do not re-prove, never
cite as this gap**) and ZERO archimedean engine / ZERO `mulRingNorm_real` /
ZERO namesake disjunction. Completing the unbounded engine `f n = n^α` on
`ℕ` and packaging `MulRingNorm.equiv f mulRingNorm_real` is the gap this
ticket lands. The Level B namesake `ostrowski` (unbounded vs padic
disjunction) is **out of this ticket** and is **not** sorry-ed.

Pin: `catalog/problems/ostrowski-q/STATEMENT.md` (OPE-1090; Scout OPE-1078
leftover; Director OPE-1089). Encoding: Mathlib `MulRingNorm` /
`MulRingNorm.equiv` / `mulRingNorm_padic`. Zero `sorry`. Do not import
`Archive.*`.

This is **not** `mulRingNorm_equiv_padic_of_bounded` (already Mathlib;
bounded half; **USE**). This is **not** Ostrowski for number fields
(file-header TODO; out of v1). This is **not** Hensel / Gelfand–Mazur /
π-irrational / Niven / e-transcendental / e-irrational (#92). This is
**not** andrasfai-erdos-sos Level B / frobenius-real-division Level B /
noether-normalization Level B / krenn-gu / hou-zeng-pfc / sun-135.
Do not re-prime the consumed mill. Leave OPE-403 alone.

v1 is `MulRingNorm ℚ` only. **Do not label any theorem Ostrowski.**

Level A: if `f` is unbounded on `ℕ`, then `∃ α > 0, ∀ n, f n = n^α`
(sandwich via `f 2 = 2^α`); package as `MulRingNorm.equiv f mulRingNorm_real`.
**Not** labelled Ostrowski.

Transcribed classical argument (Ostrowski, Acta Math. 41 (1916) 271–284;
Conrad *Ostrowski's theorem for ℚ*; Cassels *Local fields*). Compact form:
Wikipedia *Ostrowski's theorem*. Bounded padic theorem is infra, not this
claim.
-/
import Mathlib.NumberTheory.Ostrowski
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.GeomSum
import Mathlib.Data.Nat.Digits

set_option linter.unusedVariables false
set_option maxHeartbeats 800000

open Filter Real Topology
open scoped Classical

noncomputable section

namespace ProofLab.OstrowskiQ

open Rat.MulRingNorm

/-! ## Usual absolute value as a `MulRingNorm`

Not labelled Ostrowski. -/

/-- The usual archimedean absolute value on `ℚ`, as a `MulRingNorm`.
Not labelled Ostrowski. -/
def mulRingNorm_real : MulRingNorm ℚ where
  toFun x := |(x : ℝ)|
  map_zero' := by simp
  add_le' r s := by
    simpa [Rat.cast_add] using abs_add_le (r : ℝ) (s : ℝ)
  neg' x := by simp
  eq_zero_of_map_eq_zero' x := by simp
  map_one' := by simp
  map_mul' x y := by simp [abs_mul]

@[simp] lemma mulRingNorm_real_apply (x : ℚ) : mulRingNorm_real x = |(x : ℝ)| := rfl

lemma mulRingNorm_real_nat (n : ℕ) : mulRingNorm_real n = n := by
  simp [mulRingNorm_real_apply, Rat.cast_natCast, Nat.abs_cast]

/-! ## List helpers -/

lemma mapIdx_mul_left {α : Type*} (c : ℝ) (l : List α) (g : ℕ → ℝ) :
    (l.mapIdx fun i _ => c * g i).sum = c * (l.mapIdx fun i _ => g i).sum := by
  induction l generalizing g with
  | nil => simp
  | cons a l ih =>
    rw [List.mapIdx_cons, List.sum_cons, List.mapIdx_cons, List.sum_cons, ih]
    ring

lemma mapIdx_sum_le {α : Type*} (l : List α) {g h : ℕ → ℝ} (hle : ∀ i, g i ≤ h i) :
    (l.mapIdx fun i _ => g i).sum ≤ (l.mapIdx fun i _ => h i).sum := by
  induction l generalizing g h with
  | nil => simp
  | cons a l ih =>
    rw [List.mapIdx_cons, List.sum_cons, List.mapIdx_cons, List.sum_cons]
    exact add_le_add (hle 0) (ih fun i => hle (i + 1))

lemma mapIdx_pow_sum {α : Type*} (y : ℝ) (l : List α) (k : ℕ) :
    (l.mapIdx fun i _ => y ^ (i + k)).sum =
      ∑ i ∈ Finset.range l.length, y ^ (i + k) := by
  induction l generalizing k with
  | nil => simp
  | cons a l ih =>
    rw [List.mapIdx_cons, List.sum_cons, List.length_cons, Finset.sum_range_succ']
    simp only [Nat.zero_add]
    rw [add_comm _ (y ^ k)]
    have hidx : ∀ i : ℕ, i + 1 + k = i + (k + 1) := fun i => by omega
    simp_rw [hidx]
    rw [ih (k + 1)]

lemma mapIdx_geom {α : Type*} (y : ℝ) (l : List α) :
    (l.mapIdx fun i _ => y ^ i).sum = ∑ i ∈ Finset.range l.length, y ^ i := by
  simpa using mapIdx_pow_sum (y := y) (l := l) (k := 0)

lemma mapIdx_pow_succ_sum {α : Type*} (y : ℝ) (l : List α) :
    (l.mapIdx fun i _ => y ^ (i + 1)).sum = y * (l.mapIdx fun i _ => y ^ i).sum := by
  rw [mapIdx_pow_sum y l 1, mapIdx_geom]
  simp only [pow_succ]
  simp_rw [mul_comm (y ^ _) y]
  rw [← Finset.mul_sum]

lemma one_lt_natCast {m : ℕ} (hm : 1 < m) : (1 : ℝ) < m :=
  Nat.one_lt_cast.mpr hm

lemma natLog_le_logb {m n : ℕ} (hm : 1 < m) (hn : n ≠ 0) :
    (Nat.log m n : ℝ) ≤ logb m n := by
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hm)
  have hm1 : (1 : ℝ) < m := one_lt_natCast hm
  have hpow : (m : ℝ) ^ Nat.log m n ≤ (n : ℝ) := by
    rw [← Nat.cast_pow]
    exact Nat.cast_le.mpr (Nat.pow_log_le_self m hn)
  have hpos : (0 : ℝ) < (m : ℝ) ^ Nat.log m n := pow_pos hm0 _
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hle := (logb_le_logb hm1 hpos hnpos).mpr hpow
  have : logb (m : ℝ) ((m : ℝ) ^ Nat.log m n) = (Nat.log m n : ℝ) := by
    rw [logb_pow hm0, logb_self_eq_one hm1, mul_one]
  rwa [this] at hle

/-! ## Digit expansion bound -/

lemma ofDigits_norm_le (f : MulRingNorm ℚ) {m : ℕ} (hm : 1 < m) (L : List ℕ)
    (hL : ∀ d ∈ L, d < m) :
    f (↑(Nat.ofDigits (m : ℕ) L) : ℚ) ≤
      (L.mapIdx fun i _ => (m : ℝ) * f (m : ℚ) ^ i).sum := by
  induction L with
  | nil => simp [Nat.ofDigits]
  | cons d L ih =>
    have hd : d < m := hL d (List.mem_cons_self _ _)
    have hL' : ∀ x ∈ L, x < m := fun x hx => hL x (List.mem_cons_of_mem _ hx)
    have hfpos : 0 ≤ f (m : ℚ) := apply_nonneg f _
    have hfd : f (d : ℚ) ≤ (m : ℝ) :=
      (MulRingNorm_nat_le_nat d f).trans (Nat.cast_le.mpr hd.le)
    have hcons :
        (Nat.ofDigits (m : ℕ) (d :: L) : ℕ) = d + m * Nat.ofDigits m L := rfl
    have hrec := ih hL'
    have hshift :
        (L.mapIdx fun i _ => (m : ℝ) * f (m : ℚ) ^ (i + 1)).sum =
          f (m : ℚ) * (L.mapIdx fun i _ => (m : ℝ) * f (m : ℚ) ^ i).sum := by
      have h1 := mapIdx_mul_left (c := (m : ℝ)) (l := L)
        (g := fun i => f (m : ℚ) ^ (i + 1))
      have h2 := mapIdx_mul_left (c := (m : ℝ)) (l := L)
        (g := fun i => f (m : ℚ) ^ i)
      have hgeom := mapIdx_pow_succ_sum (y := f (m : ℚ)) (l := L)
      calc
        (L.mapIdx fun i _ => (m : ℝ) * f (m : ℚ) ^ (i + 1)).sum
            = (m : ℝ) * (L.mapIdx fun i _ => f (m : ℚ) ^ (i + 1)).sum := h1
        _ = (m : ℝ) * (f (m : ℚ) * (L.mapIdx fun i _ => f (m : ℚ) ^ i).sum) := by
            rw [hgeom]
        _ = f (m : ℚ) * ((m : ℝ) * (L.mapIdx fun i _ => f (m : ℚ) ^ i).sum) := by ring
        _ = f (m : ℚ) * (L.mapIdx fun i _ => (m : ℝ) * f (m : ℚ) ^ i).sum := by rw [h2]
    rw [hcons, List.mapIdx_cons, List.sum_cons]
    simp only [pow_zero, mul_one]
    have htri :
        f ((d : ℚ) + (m : ℚ) * (Nat.ofDigits m L : ℕ)) ≤
          f (d : ℚ) + f (m : ℚ) * f (Nat.ofDigits m L : ℕ) := by
      calc
        f ((d : ℚ) + (m : ℚ) * (Nat.ofDigits m L : ℕ))
            ≤ f (d : ℚ) + f ((m : ℚ) * (Nat.ofDigits m L : ℕ)) := f.add_le' _ _
        _ = f (d : ℚ) + f (m : ℚ) * f (Nat.ofDigits m L : ℕ) := by rw [map_mul]
    have hcast :
        ((d + m * Nat.ofDigits m L : ℕ) : ℚ) =
          (d : ℚ) + (m : ℚ) * (Nat.ofDigits m L : ℕ) := by
      push_cast; rfl
    calc
      f (↑(d + m * Nat.ofDigits m L) : ℚ)
          ≤ f (d : ℚ) + f (m : ℚ) * f (Nat.ofDigits m L : ℕ) := by
            simpa [hcast] using htri
      _ ≤ (m : ℝ) + f (m : ℚ) * (L.mapIdx fun i _ => (m : ℝ) * f (m : ℚ) ^ i).sum :=
            add_le_add hfd (mul_le_mul_of_nonneg_left hrec hfpos)
      _ = (m : ℝ) + (L.mapIdx fun i _ => (m : ℝ) * f (m : ℚ) ^ (i + 1)).sum := by
            rw [hshift]

/-- `f n` is bounded by the base-`m` digit geometric majorant.
Not labelled Ostrowski. -/
lemma apply_le_sum_digits (f : MulRingNorm ℚ) (n : ℕ) {m : ℕ} (hm : 1 < m) :
    f n ≤ ((Nat.digits m n).mapIdx fun i _ => (m : ℝ) * f (m : ℚ) ^ i).sum := by
  have hmem : ∀ d ∈ Nat.digits m n, d < m := fun d hd => Nat.digits_lt_base hm hd
  have h := ofDigits_norm_le f hm (Nat.digits m n) hmem
  rwa [Nat.ofDigits_digits m n] at h

/-! ## Unbounded ⇒ `1 < f n₀` for every `n₀ ≥ 2` -/

lemma tendsto_const_rpow_inv {C : ℝ} (hC : 0 < C) :
    Tendsto (fun k : ℕ ↦ C ^ (k : ℝ)⁻¹) atTop (𝓝 1) := by
  have hcont : Tendsto (fun t : ℝ => C ^ t) (𝓝 0) (𝓝 (C ^ (0 : ℝ))) :=
    (continuousAt_const_rpow hC.ne').tendsto
  simp only [rpow_zero] at hcont
  exact hcont.comp (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)

lemma tendsto_nat_rpow_inv :
    Tendsto (fun k : ℕ ↦ (k : ℝ) ^ (k : ℝ)⁻¹) atTop (𝓝 1) := by
  simp_rw [← one_div]
  exact tendsto_rpow_div.comp tendsto_natCast_atTop_atTop

/-- If `f` is unbounded on `ℕ`, then `1 < f n₀` for every `n₀ ≥ 2`.
Not labelled Ostrowski. -/
lemma one_lt_of_not_bounded {f : MulRingNorm ℚ} (notbdd : ¬ ∀ n : ℕ, f n ≤ 1)
    {n₀ : ℕ} (hn₀ : 1 < n₀) : 1 < f n₀ := by
  contrapose! notbdd
  intro n
  have hn₀0 : (0 : ℝ) < n₀ := by exact_mod_cast (Nat.zero_lt_of_lt hn₀)
  have hn₀1 : (1 : ℝ) < n₀ := by exact_mod_cast hn₀
  have hf0 : 0 ≤ f n₀ := apply_nonneg f _
  have hpowle : ∀ i : ℕ, f n₀ ^ i ≤ 1 := fun i =>
    pow_le_one i hf0 notbdd
  have h_ineq1 {m : ℕ} (hm : m ≠ 0) :
      f m ≤ n₀ * (logb n₀ m + 1) := by
    have hlen : ((Nat.digits n₀ m).length : ℝ) = (Nat.log n₀ m : ℝ) + 1 := by
      rw [Nat.digits_len n₀ m hn₀ hm]; norm_cast
    have hmaj :
        ((Nat.digits n₀ m).mapIdx fun i _ => (n₀ : ℝ) * f (n₀ : ℚ) ^ i).sum ≤
          ((Nat.digits n₀ m).mapIdx fun i _ => (n₀ : ℝ)).sum := by
      have hle : ∀ i, (n₀ : ℝ) * f (n₀ : ℚ) ^ i ≤ (n₀ : ℝ) := fun i =>
        mul_le_of_le_one_right (le_of_lt hn₀0) (hpowle i)
      have := mapIdx_sum_le (Nat.digits n₀ m) hle
      simpa using this
    have hsumc :
        ((Nat.digits n₀ m).mapIdx fun i _ => (n₀ : ℝ)).sum =
          n₀ * (Nat.digits n₀ m).length := by
      induction Nat.digits n₀ m with
      | nil => simp
      | cons a L ih =>
        rw [List.mapIdx_cons, List.sum_cons, List.length_cons, ih]
        push_cast; ring
    have hlog : (Nat.log n₀ m : ℝ) ≤ logb n₀ m := natLog_le_logb hn₀ hm
    have hbound := apply_le_sum_digits f m hn₀
    have : (n₀ : ℝ) * ((Nat.log n₀ m : ℝ) + 1) ≤ n₀ * (logb n₀ m + 1) := by
      gcongr
    calc
      f m ≤ ((Nat.digits n₀ m).mapIdx fun i _ => (n₀ : ℝ) * f (n₀ : ℚ) ^ i).sum := hbound
      _ ≤ ((Nat.digits n₀ m).mapIdx fun i _ => (n₀ : ℝ)).sum := hmaj
      _ = n₀ * (Nat.digits n₀ m).length := hsumc
      _ = n₀ * ((Nat.log n₀ m : ℝ) + 1) := by rw [hlen]
      _ ≤ n₀ * (logb n₀ m + 1) := this
  rcases n.eq_zero_or_pos with rfl | hnpos
  · simp
  rcases eq_or_ne n 1 with rfl | hn1
  · simp
  have hn2 : 1 < n := by omega
  have hC : 0 < (n₀ : ℝ) * (logb n₀ n + 1) := by
    have : 0 ≤ logb (n₀ : ℝ) n :=
      logb_nonneg hn₀1 (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hnpos.ne'))
    positivity
  have h_ineq2 {k : ℕ} (hk : 1 ≤ k) :
      f n ≤ ((n₀ : ℝ) * (logb n₀ n + 1)) ^ (k : ℝ)⁻¹ * (k : ℝ) ^ (k : ℝ)⁻¹ := by
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hk)
    have hnk : n ^ k ≠ 0 := pow_ne_zero _ hnpos.ne'
    have hposf : 0 ≤ f n := apply_nonneg f _
    have hroot : f n = (f (n ^ k : ℕ)) ^ (k : ℝ)⁻¹ := by
      rw [Nat.cast_pow, map_pow, ← rpow_natCast, rpow_rpow_inv hposf hk0]
    have hlogpow : logb (n₀ : ℝ) (n ^ k : ℕ) = k * logb n₀ n := by
      rw [Nat.cast_pow, logb_pow (by exact_mod_cast hnpos)]
    have hineq := h_ineq1 hnk
    have hlogn : 0 ≤ logb (n₀ : ℝ) n :=
      logb_nonneg hn₀1 (by exact_mod_cast (Nat.one_le_of_lt hn2))
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hinv : 0 ≤ (k : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg k)
    have hbase0 : 0 ≤ (n₀ : ℝ) * (logb n₀ (n ^ k : ℕ) + 1) := by
      have : 0 ≤ logb (n₀ : ℝ) (n ^ k : ℕ) :=
        logb_nonneg hn₀1 (by exact_mod_cast (one_le_pow_of_one_le (Nat.one_le_of_lt hn2) k))
      positivity
    have hbase1 : 0 ≤ (n₀ : ℝ) * (k * logb n₀ n + 1) := by positivity
    have hbase2 : 0 ≤ (n₀ : ℝ) * (k * logb n₀ n + k) := by positivity
    calc
      f n = (f (n ^ k : ℕ)) ^ (k : ℝ)⁻¹ := hroot
      _ ≤ ((n₀ : ℝ) * (logb n₀ (n ^ k : ℕ) + 1)) ^ (k : ℝ)⁻¹ :=
          rpow_le_rpow (apply_nonneg f _) hineq hinv
      _ = ((n₀ : ℝ) * (k * logb n₀ n + 1)) ^ (k : ℝ)⁻¹ := by rw [hlogpow]
      _ ≤ ((n₀ : ℝ) * (k * logb n₀ n + k)) ^ (k : ℝ)⁻¹ := by
        refine rpow_le_rpow hbase1 ?_ hinv
        gcongr
      _ = ((n₀ : ℝ) * (logb n₀ n + 1)) ^ (k : ℝ)⁻¹ * (k : ℝ) ^ (k : ℝ)⁻¹ := by
        have : (n₀ : ℝ) * (k * logb n₀ n + k) =
            ((n₀ : ℝ) * (logb n₀ n + 1)) * k := by ring
        rw [this, mul_rpow (by positivity) (by positivity)]
  refine le_of_tendsto_of_tendsto tendsto_const_nhds ?_
      (eventually_atTop.mpr ⟨1, fun k hk => h_ineq2 hk⟩)
  nth_rw 2 [← mul_one (1 : ℝ)]
  exact (tendsto_const_rpow_inv hC).mul tendsto_nat_rpow_inv

/-! ## Sandwich `f n ≤ f m ^ logb m n` -/

lemma expr_pos {f : MulRingNorm ℚ} {m : ℕ} (hm : 1 < m)
    (notbdd : ¬ ∀ n : ℕ, f n ≤ 1) :
    0 < (m : ℝ) * f m / (f m - 1) := by
  have hf1 : 1 < f m := one_lt_of_not_bounded notbdd hm
  have hf0 : 0 < f m := lt_trans zero_lt_one hf1
  exact div_pos (mul_pos (by exact_mod_cast (Nat.zero_lt_of_lt hm)) hf0) (sub_pos.mpr hf1)

lemma digit_geom_bound {f : MulRingNorm ℚ} {m n : ℕ} (hm : 1 < m) (hn : 1 < n)
    (notbdd : ¬ ∀ k : ℕ, f k ≤ 1) :
    f n ≤ ((m : ℝ) * f m / (f m - 1)) * f m ^ logb m n := by
  have hf1 : 1 < f m := one_lt_of_not_bounded notbdd hm
  have hf0 : 0 < f m := lt_trans zero_lt_one hf1
  have hfne : f m ≠ 1 := hf1.ne'
  have hn0 : n ≠ 0 := (Nat.zero_lt_of_lt hn).ne'
  let d := Nat.log m n
  have hlen : (Nat.digits m n).length = d + 1 := Nat.digits_len m n hm hn0
  have hsum := apply_le_sum_digits f n hm
  have hmul := mapIdx_mul_left (c := (m : ℝ)) (l := Nat.digits m n) (g := fun i => f m ^ i)
  have hgeom := mapIdx_geom (y := f m) (l := Nat.digits m n)
  have hgs : ∑ i ∈ Finset.range (Nat.digits m n).length, f m ^ i =
      (f m ^ (Nat.digits m n).length - 1) / (f m - 1) :=
    geom_sum_eq hfne _
  have hposden : 0 < f m - 1 := sub_pos.mpr hf1
  have hle1 : f m ^ (d + 1) - 1 ≤ f m ^ (d + 1) := by
    linarith [one_le_pow_of_one_le hf1.le (d + 1)]
  have hlog : (d : ℝ) ≤ logb m n := natLog_le_logb hm hn0
  have hexp := (expr_pos hm notbdd).le
  have hrpow : f m ^ (d : ℝ) ≤ f m ^ logb m n :=
    (rpow_le_rpow_left_iff hf1).mpr hlog
  calc
    f n ≤ ((Nat.digits m n).mapIdx fun i _ => (m : ℝ) * f m ^ i).sum := hsum
    _ = (m : ℝ) * ((Nat.digits m n).mapIdx fun i _ => f m ^ i).sum := hmul
    _ = (m : ℝ) * ∑ i ∈ Finset.range (Nat.digits m n).length, f m ^ i := by rw [hgeom]
    _ = (m : ℝ) * ((f m ^ (Nat.digits m n).length - 1) / (f m - 1)) := by rw [hgs]
    _ = (m : ℝ) * ((f m ^ (d + 1) - 1) / (f m - 1)) := by rw [hlen]
    _ ≤ (m : ℝ) * (f m ^ (d + 1) / (f m - 1)) := by
      gcongr
    _ = ((m : ℝ) * f m / (f m - 1)) * f m ^ d := by
      simp only [pow_succ]
      field_simp [hposden.ne']
      ring
    _ ≤ ((m : ℝ) * f m / (f m - 1)) * f m ^ logb m n := by
      have : (f m : ℝ) ^ d = f m ^ (d : ℝ) := (rpow_natCast _ _).symm
      rw [this]
      exact mul_le_mul_of_nonneg_left hrpow hexp

lemma param_upperbound {f : MulRingNorm ℚ} {m n k : ℕ} (hm : 1 < m) (hn : 1 < n)
    (notbdd : ¬ ∀ t : ℕ, f t ≤ 1) (hk : k ≠ 0) :
    f n ≤ ((m : ℝ) * f m / (f m - 1)) ^ (k : ℝ)⁻¹ * f m ^ logb m n := by
  have hnk : 1 < n ^ k := Nat.one_lt_pow hk hn
  have hposf : 0 ≤ f n := apply_nonneg f _
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hinv : 0 ≤ (k : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg k)
  have hroot : f n = (f (n ^ k : ℕ)) ^ (k : ℝ)⁻¹ := by
    rw [Nat.cast_pow, map_pow, ← rpow_natCast, rpow_rpow_inv hposf hk0]
  have hineq := digit_geom_bound (f := f) hm hnk notbdd
  have hlog : logb (m : ℝ) (n ^ k : ℕ) = k * logb m n := by
    rw [Nat.cast_pow, logb_pow (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn))]
  have hexp := (expr_pos (f := f) hm notbdd).le
  have hC0 : 0 ≤ (m : ℝ) * f m / (f m - 1) := hexp
  have hfm0 : 0 ≤ f m := apply_nonneg f _
  have hbase : 0 ≤ ((m : ℝ) * f m / (f m - 1)) * f m ^ logb m (n ^ k : ℕ) :=
    mul_nonneg hC0 (rpow_nonneg hfm0 _)
  calc
    f n = (f (n ^ k : ℕ)) ^ (k : ℝ)⁻¹ := hroot
    _ ≤ (((m : ℝ) * f m / (f m - 1)) * f m ^ logb m (n ^ k : ℕ)) ^ (k : ℝ)⁻¹ :=
        rpow_le_rpow (apply_nonneg f _) hineq hinv
    _ = (((m : ℝ) * f m / (f m - 1)) * f m ^ (k * logb m n)) ^ (k : ℝ)⁻¹ := by
        rw [hlog]
    _ = ((m : ℝ) * f m / (f m - 1)) ^ (k : ℝ)⁻¹ * (f m ^ (k * logb m n)) ^ (k : ℝ)⁻¹ :=
        mul_rpow hC0 (rpow_nonneg hfm0 _)
    _ = ((m : ℝ) * f m / (f m - 1)) ^ (k : ℝ)⁻¹ * f m ^ logb m n := by
        have : (f m ^ (k * logb (m : ℝ) n)) ^ (k : ℝ)⁻¹ = f m ^ logb m n := by
          rw [← rpow_mul hfm0, mul_comm (k : ℝ), mul_assoc, mul_inv_cancel hk0, mul_one]
        rw [this]

/-- Given `m, n ≥ 2`, `f n ≤ f m ^ logb m n`. Not labelled Ostrowski. -/
lemma le_pow_log {f : MulRingNorm ℚ} {m n : ℕ} (hm : 1 < m) (hn : 1 < n)
    (notbdd : ¬ ∀ t : ℕ, f t ≤ 1) :
    f n ≤ f m ^ logb m n := by
  have hexp := expr_pos (f := f) hm notbdd
  have hlim :
      Tendsto (fun k : ℕ ↦ ((m : ℝ) * f m / (f m - 1)) ^ (k : ℝ)⁻¹ * f m ^ logb m n)
        atTop (𝓝 (f m ^ logb m n)) := by
    nth_rw 2 [← one_mul (f m ^ logb (m : ℝ) n)]
    exact (tendsto_const_rpow_inv hexp).mul_const _
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim <|
    eventually_atTop.mpr ⟨2, fun b hb => param_upperbound hm hn notbdd (ne_of_gt (by omega : 0 < b))⟩

lemma le_of_eq_pow {f : MulRingNorm ℚ} {m n : ℕ} (hm : 1 < m) (hn : 1 < n)
    (notbdd : ¬ ∀ t : ℕ, f t ≤ 1) {s t : ℝ}
    (hfm : f m = (m : ℝ) ^ s) (hfn : f n = (n : ℝ) ^ t) : t ≤ s := by
  have := le_pow_log (f := f) hm hn notbdd
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
  rw [← rpow_le_rpow_left_iff hn1, ← hfn]
  refine this.trans ?_
  rw [hfm, ← rpow_mul (Nat.cast_nonneg m), mul_comm, rpow_mul (Nat.cast_nonneg m),
    rpow_logb (by exact_mod_cast (Nat.zero_lt_of_lt hm)) (by exact_mod_cast hm.ne')
      (by exact_mod_cast (Nat.zero_lt_of_lt hn))]

lemma eq_of_eq_pow {f : MulRingNorm ℚ} {m n : ℕ} (hm : 1 < m) (hn : 1 < n)
    (notbdd : ¬ ∀ t : ℕ, f t ≤ 1) {s t : ℝ}
    (hfm : f m = (m : ℝ) ^ s) (hfn : f n = (n : ℝ) ^ t) : s = t :=
  le_antisymm (le_of_eq_pow hn hm notbdd hfn hfm) (le_of_eq_pow hm hn notbdd hfm hfn)

/-! ## Level A engine: `f n = n^α` on `ℕ`

Not labelled Ostrowski. Sandwich via `f 2 = 2^α`. -/

/-- If `f` is unbounded on `ℕ`, there is `α > 0` with `f n = n^α` for every
natural `n`. Not labelled Ostrowski. -/
theorem unbounded_eq_pow {f : MulRingNorm ℚ} (notbdd : ¬ ∀ n : ℕ, f n ≤ 1) :
    ∃ α : ℝ, 0 < α ∧ ∀ n : ℕ, f n = (n : ℝ) ^ α := by
  obtain ⟨m, hm⟩ := not_forall.mp notbdd
  have oneltm : 1 < m := by
    contrapose! hm
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hm with rfl | rfl <;> simp
  have hf1 : 1 < f m := one_lt_of_not_bounded notbdd oneltm
  set α := logb m (f m) with hα
  have hαpos : 0 < α :=
    logb_pos (by exact_mod_cast oneltm) hf1
  have hfm : f m = (m : ℝ) ^ α := by
    rw [hα, rpow_logb (by exact_mod_cast (Nat.zero_lt_of_lt oneltm))
      (by exact_mod_cast oneltm.ne') (lt_trans zero_lt_one hf1)]
  refine ⟨α, hαpos, fun n => ?_⟩
  rcases lt_trichotomy n 1 with h | rfl | h
  · have : n = 0 := by omega
    subst n
    have hα0 : α ≠ 0 := hαpos.ne'
    simp [zero_rpow hα0]
  · simp
  · have hn : 1 < n := h
    have hfn' : f n = (n : ℝ) ^ logb n (f n) := by
      have hf1n : 1 < f n := one_lt_of_not_bounded notbdd hn
      rw [rpow_logb (by exact_mod_cast (Nat.zero_lt_of_lt hn))
        (by exact_mod_cast hn.ne') (lt_trans zero_lt_one hf1n)]
    have heq := eq_of_eq_pow (f := f) oneltm hn notbdd hfm hfn'
    rw [hfn', heq]

/-! ## Level A package: `MulRingNorm.equiv f mulRingNorm_real`

Not labelled Ostrowski. Uses already-upstream `equiv_on_nat_iff_equiv`. -/

/-- If `f` is unbounded on `ℕ`, then `f` is equivalent to the usual absolute
value. Not labelled Ostrowski. -/
theorem equiv_mulRingNorm_real_of_unbounded {f : MulRingNorm ℚ}
    (notbdd : ¬ ∀ n : ℕ, f n ≤ 1) :
    MulRingNorm.equiv f mulRingNorm_real := by
  obtain ⟨α, hα, hpow⟩ := unbounded_eq_pow notbdd
  refine equiv_on_nat_iff_equiv.mp ⟨α⁻¹, inv_pos.mpr hα, fun n => ?_⟩
  have hα0 : α ≠ 0 := hα.ne'
  rw [hpow n, mulRingNorm_real_nat, ← rpow_mul (Nat.cast_nonneg n),
    mul_inv_cancel hα0, rpow_one]

/-
Residual (not sorry-ed; out of this ticket):

Level B namesake `theorem ostrowski (f : MulRingNorm ℚ) (hf : f ≠ 1)` —
`MulRingNorm.equiv f mulRingNorm_real ∨ ∃ p, Fact p.Prime ∧
MulRingNorm.equiv f (mulRingNorm_padic p)`.

The bounded half is already Mathlib `mulRingNorm_equiv_padic_of_bounded`
(USE, do not re-prove). Number-field Ostrowski is out of v1. Do not land
the namesake here.
-/

end ProofLab.OstrowskiQ
