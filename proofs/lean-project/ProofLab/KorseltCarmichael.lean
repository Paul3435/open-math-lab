/-
Korselt's criterion for Carmichael numbers.

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 has `Nat.ProbablePrime` / `Nat.FermatPsp`
(`NumberTheory/FermatPsp.lean`; file comment: Carmichael numbers are
**"not yet defined in this file"** — that comment **is** the gap),
`Squarefree`, `ZMod.chineseRemainder` / `Nat.chineseRemainder`, and
Fermat–Euler `Nat.ModEq.pow_totient` / `ZMod.pow_totient`. ZERO
`IsCarmichael`, ZERO Korselt criterion, ZERO "pseudoprime to all bases"
characterization under `Mathlib/` or `Archive/`. Completing the namesake
is the gap.

Pin: `catalog/problems/korselt-carmichael/STATEMENT.md` (OPE-815; Scout
OPE-804 leftover slot #2; Director OPE-814). Encoding: Mathlib
`Nat.ProbablePrime` + new `IsCarmichael` / `Korselt`. Zero `sorry`.
Do not import `Archive.*`.

This is **not** infinitude of Carmichael numbers (Alford–Granville–
Pomerance 1994, out of v1). `Nat.exists_infinite_pseudoprimes` is
already Mathlib (FermatPsp to a **fixed** base — different theorem).
This is **not** the Carmichael function `λ(n)` (out of v1).
This is **not** Euclid–Euler / even perfect (`ProofLab/EuclidEulerPerfect.lean`,
PR #80). Odd-perfect / aliquot / Lucas–Lehmer stay banned.
This is **not** FLT (`NumberTheory/FLT/{Three,Four}.lean` already Mathlib).
This is **not** Fermat–Euler totient (`Nat.ModEq.pow_totient` — used, not
re-proved).
This is **not** Wilson / Lucas binomial / Euler criterion / quadratic
reciprocity.
This is **not** LLL (`ProofLab/LovaszLocalLemma.lean`, PR #85).
Leave OPE-403 alone.

`1 < n` and `¬ n.Prime` are load-bearing: primes satisfy Fermat
`a^{p-1} ≡ 1 (mod p)` for `p ∤ a`, so the composite clause is what
makes the namesake nontrivial. Squarefree is load-bearing on the
Korselt side (a prime-square fails the Fermat test to a suitable base).

v1 is **Korselt's iff**. Level A `isCarmichael_squarefree` /
`isCarmichael_prime_sub_one_dvd` / `isCarmichael_imp_korselt` is the
easy direction and is **not** labelled the namesake. Level B
`korselt_imp_isCarmichael` is the CRT + totient converse. The namesake
is the conjunction `korselt`.

Transcribed classical argument (A. Korselt 1899; R. D. Carmichael 1910).
-/
import Mathlib.NumberTheory.FermatPsp
import Mathlib.Data.Nat.Squarefree
import Mathlib.RingTheory.IntegralDomain
import Mathlib.GroupTheory.Exponent
import Mathlib.Tactic

set_option linter.unusedVariables false

open Nat Monoid

namespace ProofLab.KorseltCarmichael

/-! ## Pins (match STATEMENT.md exactly) -/

/-- A Carmichael number is a composite `n > 1` that is a Fermat probable
prime to every base coprime to `n`. Reuses `Nat.ProbablePrime`. -/
def IsCarmichael (n : ℕ) : Prop :=
  1 < n ∧ ¬ n.Prime ∧ ∀ a : ℕ, Nat.Coprime a n → Nat.ProbablePrime n a

/-- Korselt's arithmetic condition: composite squarefree `n > 1` with
`p − 1 ∣ n − 1` for every prime `p ∣ n`. -/
def Korselt (n : ℕ) : Prop :=
  Squarefree n ∧ ¬ n.Prime ∧ 1 < n ∧
    ∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ n - 1

/-! ## Glue -/

lemma ne_zero_of_one_lt {n : ℕ} (hn : 1 < n) : n ≠ 0 :=
  (lt_trans Nat.zero_lt_one hn).ne'

lemma coprime_pos_of_coprime_of_one_lt {a n : ℕ} (h : Coprime a n) (hn : 1 < n) :
    0 < a := by
  refine Nat.pos_of_ne_zero ?_
  rintro rfl
  rw [Nat.coprime_zero_left] at h
  exact hn.ne.symm h

lemma probablePrime_of_coprime {n a : ℕ} (hn : 1 < n)
    (h : Coprime a n) (hmod : a ^ (n - 1) ≡ 1 [MOD n]) :
    ProbablePrime n a :=
  (probablePrime_iff_modEq n (coprime_pos_of_coprime_of_one_lt h hn)).2 hmod

lemma modEq_of_probablePrime {n a : ℕ} (hn : 1 < n)
    (h : Coprime a n) (hp : ProbablePrime n a) :
    a ^ (n - 1) ≡ 1 [MOD n] :=
  (probablePrime_iff_modEq n (coprime_pos_of_coprime_of_one_lt h hn)).1 hp

/-- Split `n = p^e * m` with `p ∤ m`. Glue, not namesake. -/
lemma exists_pow_mul_not_dvd {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime) :
    ∃ e m : ℕ, ¬ p ∣ m ∧ n = p ^ e * m :=
  exists_eq_pow_mul_and_not_dvd hn p hp.ne_one

/-- CRT lift: residue `a` modulo `p^k` and `1` modulo the `p`-free part. -/
lemma exists_coprime_modEq_pow {n p e m a k : ℕ} (hp : p.Prime)
    (hn : n = p ^ e * m) (hpm : ¬ p ∣ m) (hk : k ≠ 0)
    (ha : Coprime a (p ^ k)) :
    ∃ x, Coprime x n ∧ x ≡ a [MOD p ^ k] := by
  have hcop : Coprime (p ^ k) m := (hp.coprime_iff_not_dvd.2 hpm).pow_left _
  let x := chineseRemainder hcop a 1
  refine ⟨x, ?_, x.prop.1⟩
  have hx1 : (x : ℕ) ≡ 1 [MOD m] := x.prop.2
  have hxk : (x : ℕ) ≡ a [MOD p ^ k] := x.prop.1
  have hx_m : Coprime (x : ℕ) m := by
    rw [Nat.coprime_iff_gcd_eq_one, Nat.ModEq.gcd_eq hx1, Nat.gcd_one_left]
  have hx_pk : Coprime (x : ℕ) (p ^ k) := by
    rwa [Nat.coprime_iff_gcd_eq_one, Nat.ModEq.gcd_eq hxk, ← Nat.coprime_iff_gcd_eq_one]
  have hx_p : Coprime (x : ℕ) p :=
    hx_pk.coprime_dvd_right (dvd_pow_self p hk)
  have hx_pe : Coprime (x : ℕ) (p ^ e) := hx_p.pow_right _
  simpa [hn] using hx_pe.mul_right hx_m

lemma one_add_prime_coprime_pow (p k : ℕ) (hp : p.Prime) :
    Coprime (1 + p) (p ^ k) := by
  have : Coprime (1 + p) p := by
    rw [add_comm, Nat.coprime_self_add_left]
    exact Nat.coprime_one_left _
  exact this.pow_right _

/-- Binomial truncation in `ZMod (p^2)`: `(1+p)^k ≡ 1 + k p`. Glue. -/
lemma one_add_cast_pow (p k : ℕ) :
    (1 + (p : ZMod (p ^ 2))) ^ k = 1 + k * (p : ZMod (p ^ 2)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hp2 : (p : ZMod (p ^ 2)) * p = 0 := by
      rw [← Nat.cast_mul, ← pow_two, ZMod.natCast_self]
    rw [pow_add, pow_one, ih]
    have hmul :
        (1 + (k : ZMod (p ^ 2)) * p) * (1 + p) = 1 + p + k * p := by
      rw [add_mul, one_mul, mul_add, mul_one, mul_assoc, hp2, mul_zero, add_zero]
    rw [hmul, Nat.cast_succ, add_mul, one_mul]
    simp [mul_comm, add_comm, add_left_comm, add_assoc]

lemma one_add_pow_modEq (p k : ℕ) :
    (1 + p) ^ k ≡ 1 + k * p [MOD p ^ 2] := by
  rw [← ZMod.eq_iff_modEq_nat]
  convert one_add_cast_pow p k using 1
  · simp [Nat.cast_pow, Nat.cast_add, Nat.cast_one]
  · simp [Nat.cast_add, Nat.cast_mul, Nat.cast_one]

lemma dvd_of_squarefree_of_forall_prime_dvd {n a : ℕ}
    (hsq : Squarefree n) (hn : 0 < n)
    (h : ∀ p : ℕ, p.Prime → p ∣ n → p ∣ a) : n ∣ a := by
  rcases eq_or_ne a 0 with rfl | ha
  · exact dvd_zero n
  rw [← factorization_le_iff_dvd hn.ne.symm ha]
  intro p
  have hle : n.factorization p ≤ 1 := hsq.natFactorization_le_one p
  by_cases hp0 : n.factorization p = 0
  · simp [hp0]
  have hpP : p.Prime := by
    contrapose! hp0
    exact factorization_eq_zero_of_non_prime n hp0
  have hpn : p ∣ n := (hpP.dvd_iff_one_le_factorization hn.ne.symm).2 (by omega)
  have hpa : p ∣ a := h p hpP hpn
  have : 1 ≤ a.factorization p := (hpP.dvd_iff_one_le_factorization ha).1 hpa
  omega

lemma two_le_pow_of_sq_dvd {p e m : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m)
    (hsq : p ^ 2 ∣ p ^ e * m) : 2 ≤ e := by
  have hpe : p ^ 2 ∣ p ^ e :=
    ((hp.coprime_iff_not_dvd.2 hpm).pow_left 2).dvd_of_dvd_mul_right hsq
  exact (pow_dvd_pow_iff_le_right hp.one_lt).1 hpe

lemma one_le_pow_of_prime_dvd {p e m : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m)
    (hpn : p ∣ p ^ e * m) : 1 ≤ e := by
  have : p ∣ p ^ e := (hp.coprime_iff_not_dvd.2 hpm).dvd_of_dvd_mul_right hpn
  have : p ^ 1 ∣ p ^ e := by simpa using this
  exact (pow_dvd_pow_iff_le_right hp.one_lt).1 this

lemma prime_dvd_of_sq_dvd_mul {p t : ℕ} (hp : 0 < p) (h : p ^ 2 ∣ t * p) : p ∣ t := by
  have : p * p ∣ p * t := by
    simpa [pow_two, mul_comm t] using h
  exact (Nat.mul_dvd_mul_iff_left hp).1 this

lemma nat_dvd_sub_one_of_modEq {p a : ℕ} (hle : 1 ≤ a) (h : a ≡ 1 [MOD p]) : p ∣ a - 1 :=
  mod_cast (Nat.ModEq.dvd h.symm)

/-! ## Level A — `IsCarmichael → Korselt` (not labelled namesake) -/

/-- If `n` is Carmichael then `n` is squarefree. A prime-square factor
fails the Fermat test to a CRT lift of `1+p`. **Not** labelled Korselt. -/
theorem isCarmichael_squarefree {n : ℕ} (h : IsCarmichael n) : Squarefree n := by
  rcases h with ⟨hn, _, hpsp⟩
  rw [squarefree_iff_prime_squarefree]
  intro p hp hsq
  obtain ⟨e, m, hpm, rfl⟩ := exists_pow_mul_not_dvd (ne_zero_of_one_lt hn) hp
  have hsq' : p ^ 2 ∣ p ^ e * m := by simpa [pow_two] using hsq
  have he : 2 ≤ e := two_le_pow_of_sq_dvd hp hpm hsq'
  obtain ⟨x, hxcop, hxmod⟩ :=
    exists_coprime_modEq_pow (k := 2) hp rfl hpm (by omega)
      (one_add_prime_coprime_pow p 2 hp)
  have hxpp : x ^ (p ^ e * m - 1) ≡ 1 [MOD p ^ e * m] :=
    modEq_of_probablePrime hn hxcop (hpsp x hxcop)
  have hmod2 : p ^ 2 ∣ p ^ e * m := dvd_mul_of_dvd_left (pow_dvd_pow p he) _
  have hx1 : x ^ (p ^ e * m - 1) ≡ 1 [MOD p ^ 2] := hxpp.of_dvd hmod2
  have hxap : x ^ (p ^ e * m - 1) ≡ (1 + p) ^ (p ^ e * m - 1) [MOD p ^ 2] :=
    hxmod.pow _
  have hbin : (1 + p) ^ (p ^ e * m - 1) ≡ 1 + (p ^ e * m - 1) * p [MOD p ^ 2] :=
    one_add_pow_modEq p _
  have hfinal : 1 + (p ^ e * m - 1) * p ≡ 1 [MOD p ^ 2] :=
    (hbin.symm.trans hxap.symm).trans hx1
  have hdiv0 : p ^ 2 ∣ (1 + (p ^ e * m - 1) * p) - 1 :=
    nat_dvd_sub_one_of_modEq (Nat.le_add_right 1 _) hfinal
  have hdiv : p ^ 2 ∣ (p ^ e * m - 1) * p := by
    simpa [Nat.add_sub_cancel_left] using hdiv0
  have hsub : p ∣ p ^ e * m - 1 := prime_dvd_of_sq_dvd_mul hp.pos hdiv
  have hpn : p ∣ p ^ e * m := dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) _
  have hn1 : 1 ≤ p ^ e * m := le_of_lt hn
  have : p ∣ (p ^ e * m) - (p ^ e * m - 1) :=
    Nat.dvd_sub (Nat.sub_le _ _) hpn hsub
  rw [tsub_tsub_cancel_of_le hn1] at this
  exact hp.not_dvd_one this

/-- If `n` is Carmichael then `p − 1 ∣ n − 1` for every prime `p ∣ n`,
via cyclicity of `(ZMod p)ˣ`. **Not** labelled Korselt. -/
theorem isCarmichael_prime_sub_one_dvd {n p : ℕ} (h : IsCarmichael n)
    (hp : p.Prime) (hpn : p ∣ n) : p - 1 ∣ n - 1 := by
  rcases h with ⟨hn, _, hpsp⟩
  obtain ⟨e, m, hpm, rfl⟩ := exists_pow_mul_not_dvd (ne_zero_of_one_lt hn) hp
  have he : 1 ≤ e := one_le_pow_of_prime_dvd hp hpm hpn
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hpow : ∀ u : (ZMod p)ˣ, u ^ (p ^ e * m - 1) = 1 := by
    intro u
    have hcop_val : Coprime (u : ZMod p).val p := ZMod.val_coe_unit_coprime u
    obtain ⟨x, hxcop, hxmod⟩ :=
      exists_coprime_modEq_pow (k := 1) hp rfl hpm (by omega) (by
        simpa [pow_one] using hcop_val)
    have hxpp : x ^ (p ^ e * m - 1) ≡ 1 [MOD p ^ e * m] :=
      modEq_of_probablePrime hn hxcop (hpsp x hxcop)
    have hmodp : p ∣ p ^ e * m := dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) _
    have hx1 : x ^ (p ^ e * m - 1) ≡ 1 [MOD p] := hxpp.of_dvd hmodp
    have hxu : x ^ (p ^ e * m - 1) ≡ (u : ZMod p).val ^ (p ^ e * m - 1) [MOD p] := by
      have : x ≡ (u : ZMod p).val [MOD p] := by simpa [pow_one] using hxmod
      exact this.pow _
    have hnat : (u : ZMod p).val ^ (p ^ e * m - 1) ≡ 1 [MOD p] := hxu.symm.trans hx1
    have hcast :
        (Nat.cast ((u : ZMod p).val ^ (p ^ e * m - 1)) : ZMod p) = Nat.cast (1 : ℕ) := by
      rw [ZMod.eq_iff_modEq_nat]
      exact hnat
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    rw [← ZMod.natCast_zmod_val (u : ZMod p), ← Nat.cast_pow]
    simpa [Nat.cast_one] using hcast
  have hexp : exponent (ZMod p)ˣ ∣ p ^ e * m - 1 :=
    exponent_dvd_iff_forall_pow_eq_one.2 hpow
  have hcard : exponent (ZMod p)ˣ = Fintype.card (ZMod p)ˣ :=
    IsCyclic.exponent_eq_card
  have hφ : Fintype.card (ZMod p)ˣ = φ p := ZMod.card_units_eq_totient p
  have htot : φ p = p - 1 := totient_prime hp
  rw [hcard, hφ, htot] at hexp
  exact hexp

/-- Level A full easy direction. **Not** labelled `korselt`. -/
theorem isCarmichael_imp_korselt {n : ℕ} (h : IsCarmichael n) : Korselt n := by
  rcases h with ⟨hn, hnp, hpsp⟩
  refine ⟨isCarmichael_squarefree ⟨hn, hnp, hpsp⟩, hnp, hn, ?_⟩
  intro p hp hpn
  exact isCarmichael_prime_sub_one_dvd ⟨hn, hnp, hpsp⟩ hp hpn

/-! ## Level B — converse (CRT + totient) and namesake -/

/-- Converse: Korselt's condition implies the Fermat test to every
coprime base. Engine: squarefree + Fermat/`pow_totient` at each prime. -/
theorem korselt_imp_isCarmichael {n : ℕ} (h : Korselt n) : IsCarmichael n := by
  rcases h with ⟨hsq, hnp, hn, hdiv⟩
  refine ⟨hn, hnp, ?_⟩
  intro a ha
  have ha1 : 0 < a := coprime_pos_of_coprime_of_one_lt ha hn
  have hpowpos : 1 ≤ a ^ (n - 1) := Nat.one_le_pow _ _ ha1
  refine dvd_of_squarefree_of_forall_prime_dvd hsq (lt_trans Nat.zero_lt_one hn) ?_
  intro p hp hpn
  have hcop_p : Coprime a p := ha.coprime_dvd_right hpn
  have hfermat : a ^ φ p ≡ 1 [MOD p] := Nat.ModEq.pow_totient hcop_p
  have hpow : a ^ (p - 1) ≡ 1 [MOD p] := by simpa [totient_prime hp] using hfermat
  obtain ⟨k, hk⟩ := hdiv p hp hpn
  have : a ^ (n - 1) ≡ 1 [MOD p] := by
    rw [hk, pow_mul]
    convert hpow.pow k using 1
    rw [one_pow]
  exact nat_dvd_sub_one_of_modEq hpowpos this

/-- Korselt's criterion: a composite `n > 1` is Carmichael iff it is
squarefree and `p − 1 ∣ n − 1` for every prime `p ∣ n`.

Classical (Korselt 1899 / Carmichael 1910). **No novelty claim.**
Not infinitude. Not `λ(n)`. Not Euclid–Euler. Not FLT. Not totient. -/
theorem korselt {n : ℕ} : IsCarmichael n ↔ Korselt n :=
  ⟨isCarmichael_imp_korselt, korselt_imp_isCarmichael⟩

end ProofLab.KorseltCarmichael
