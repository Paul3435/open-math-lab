/-
Euclid–Euler even-perfect characterization.

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 has `Nat.Perfect` / `perfect_iff_sum_divisors_eq_two_mul`
(`NumberTheory/Divisors.lean`), `mersenne` (`NumberTheory/LucasLehmer.lean`;
**do not re-prove Lucas–Lehmer**), and `σ` / `isMultiplicative_sigma` /
`sigma_one_apply` (`NumberTheory/ArithmeticFunction.lean`). ZERO Euclid–Euler
/ even-perfect theorem under `Mathlib/`. Completing the namesake is the gap.

Pin: `catalog/problems/euclid-euler-perfect/STATEMENT.md` (OPE-781; Scout
OPE-770 leftover slot #2; Director OPE-780). Encoding: Mathlib `mersenne`
+ `Nat.Perfect`. Zero `sorry`. Do not import `Archive.*`.

This is **not** odd perfect numbers (OPEN, out of v1). `Even n` is
load-bearing on the converse.
This is **not** Lucas–Lehmer primality (`lucas_lehmer_sufficiency` is
already Mathlib). The Mersenne-prime hypothesis is an *input*.
This is **not** Frobenius (`frobeniusNumber_pair` already Mathlib; OPE-25).
This is **not** Catalan / derangement / Stirling `n!` (already Mathlib).
This is **not** bipartite-odd-cycle (`ProofLab/BipartiteOddCycle.lean`, PR #79).
This is **not** Moore / Stirling second kind / pentagonal / KST / sunflower /
CNS / Kruskal–Katona / Oddtown / Cayley / Friendship / Havel / Menger /
Dilworth / Eulerian / König / Dirac / Brooks / greedy / EKR / Mycielski.
Leave OPE-403 alone.

v1 is the **even** characterization. Level A `euclid_perfect` is Euclid
IX.36 (Mersenne prime ⇒ perfect) and is **not** labelled the full namesake.
Level B `euler_even_perfect` is Euler's converse. The namesake is the
conjunction `even_perfect_iff`.

`k ≠ 0` is load-bearing for evenness (`mersenne 1 = 1` is not prime, so
the prime hypothesis already excludes `k = 0`).

Transcribed classical argument (Euclid IX.36 + Euler even-perfect
converse). Wiedijk 100 Theorem 70 is the *same* statement and lives
only in `Archive/Wiedijk100Theorems/PerfectNumbers.lean` — **do not
import it**.
-/
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.Algebra.GeomSum
import Mathlib.RingTheory.Multiplicity
import Mathlib.Tactic

set_option linter.unusedVariables false

open Nat ArithmeticFunction Finset

namespace ProofLab.EuclidEulerPerfect

/-! ## Glue: σ of a 2-power and odd Mersenne numbers -/

/-- Mersenne numbers `2^{k+1} − 1` are odd. -/
theorem odd_mersenne_succ (k : ℕ) : ¬ 2 ∣ mersenne (k + 1) := by
  simp [← even_iff_two_dvd, ← Nat.even_add_one, parity_simps]

/-- Geometric-sum formula: `σ(2^k) = 2^{k+1} − 1`. -/
theorem sigma_two_pow_eq_mersenne_succ (k : ℕ) : σ 1 (2 ^ k) = mersenne (k + 1) := by
  simp_rw [sigma_one_apply, mersenne, show 2 = 1 + 1 from rfl, ← geom_sum_mul_add 1 (k + 1)]
  norm_num

/-- A Mersenne prime forces `k ≠ 0` (`mersenne 1 = 1` is not prime). -/
theorem ne_zero_of_prime_mersenne (k : ℕ) (pr : (mersenne (k + 1)).Prime) : k ≠ 0 := by
  intro H
  simp [H, mersenne, Nat.not_prime_one] at pr

/-- Euclid form is even when the Mersenne factor is prime. Glue, not namesake. -/
theorem even_two_pow_mul_mersenne_of_prime (k : ℕ) (pr : (mersenne (k + 1)).Prime) :
    Even (2 ^ k * mersenne (k + 1)) := by
  simp [ne_zero_of_prime_mersenne k pr, parity_simps]

/-! ## Level A — Euclid IX.36 (not labelled namesake) -/

/-- Euclid: a Mersenne prime `2^{k+1} − 1` produces an even perfect number
`2^k * mersenne (k+1)`. **Not** the full Euclid–Euler namesake. -/
theorem euclid_perfect (k : ℕ) (h : Nat.Prime (mersenne (k + 1))) :
    Nat.Perfect (2 ^ k * mersenne (k + 1)) := by
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul, ← mul_assoc, ← Nat.pow_succ',
    ← sigma_one_apply, mul_comm,
    isMultiplicative_sigma.map_mul_of_coprime
      (Nat.prime_two.coprime_pow_of_not_dvd (odd_mersenne_succ _)),
    sigma_two_pow_eq_mersenne_succ]
  · simp [h, Nat.prime_two, sigma_one_apply]
  · positivity

/-! ## 2-adic splitting -/

/-- Every positive `n` is `2^k * m` with `m` odd. -/
theorem eq_two_pow_mul_odd {n : ℕ} (hpos : 0 < n) :
    ∃ k m : ℕ, n = 2 ^ k * m ∧ ¬ Even m := by
  have h := multiplicity.finite_nat_iff.2 ⟨Nat.prime_two.ne_one, hpos⟩
  cases' multiplicity.pow_multiplicity_dvd h with m hm
  use (multiplicity 2 n).get h, m
  refine ⟨hm, ?_⟩
  rw [even_iff_two_dvd]
  have hg := multiplicity.is_greatest' h (Nat.lt_succ_self _)
  contrapose! hg
  rcases hg with ⟨k, rfl⟩
  apply Dvd.intro k
  rw [pow_succ, mul_assoc, ← hm]

/-! ## Level B — Euler converse -/

/-- Euler: every even perfect number is Euclid form
`2^k * mersenne (k+1)` with that Mersenne number prime.
`Even n` is load-bearing (odd perfect numbers are OPEN). -/
theorem euler_even_perfect {n : ℕ} (hev : Even n) (hp : Nat.Perfect n) :
    ∃ k : ℕ, Nat.Prime (mersenne (k + 1)) ∧ n = 2 ^ k * mersenne (k + 1) := by
  have hpos := hp.2
  rcases eq_two_pow_mul_odd hpos with ⟨k, m, rfl, hm⟩
  use k
  rw [even_iff_two_dvd] at hm
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul hpos, ← sigma_one_apply,
    isMultiplicative_sigma.map_mul_of_coprime (Nat.prime_two.coprime_pow_of_not_dvd hm).symm,
    sigma_two_pow_eq_mersenne_succ, ← mul_assoc, ← Nat.pow_succ'] at hp
  rcases Nat.Coprime.dvd_of_dvd_mul_left
      (Nat.prime_two.coprime_pow_of_not_dvd (odd_mersenne_succ _)) (Dvd.intro _ hp) with
    ⟨j, rfl⟩
  rw [← mul_assoc, mul_comm _ (mersenne _), mul_assoc] at hp
  have h := mul_left_cancel₀ (by positivity) hp
  rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self, ← succ_mersenne, add_mul,
    one_mul, add_comm] at h
  have hj := add_left_cancel h
  cases Nat.sum_properDivisors_dvd (by rw [hj]; apply Dvd.intro_left (mersenne (k + 1)) rfl) with
  | inl h_1 =>
    have j1 : j = 1 := Eq.trans hj.symm h_1
    rw [j1, mul_one, Nat.sum_properDivisors_eq_one_iff_prime] at h_1
    simp [h_1, j1]
  | inr h_1 =>
    have jcon := Eq.trans hj.symm h_1
    rw [← one_mul j, ← mul_assoc, mul_one] at jcon
    have jcon2 := mul_right_cancel₀ ?_ jcon
    · exfalso
      match k with
      | 0 =>
        apply hm
        rw [← jcon2, pow_zero, one_mul, one_mul] at hev
        rw [← jcon2, one_mul]
        exact even_iff_two_dvd.mp hev
      | .succ k =>
        apply Nat.ne_of_lt _ jcon2
        rw [mersenne, ← Nat.pred_eq_sub_one, Nat.lt_pred_iff, ← pow_one (Nat.succ 1)]
        apply pow_lt_pow_right (Nat.lt_succ_self 1) (Nat.succ_lt_succ (Nat.succ_pos k))
    contrapose! hm
    simp [hm]

/-! ## Namesake — even + Perfect ↔ Euclid form -/

/-- Euclid–Euler theorem: an even natural is perfect iff it is
`2^k * mersenne (k+1)` with that Mersenne number prime.
Odd perfect numbers are OPEN and out of v1. -/
theorem even_perfect_iff {n : ℕ} :
    Even n ∧ Nat.Perfect n ↔ ∃ k : ℕ, Nat.Prime (mersenne (k + 1)) ∧
      n = 2 ^ k * mersenne (k + 1) := by
  constructor
  · rintro ⟨ev, perf⟩
    exact euler_even_perfect ev perf
  · rintro ⟨k, pr, rfl⟩
    exact ⟨even_two_pow_mul_mersenne_of_prime k pr, euclid_perfect k pr⟩

end ProofLab.EuclidEulerPerfect
