/-
Bang's theorem (Zsigmondy `b = 1`), formalize-only.

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 has `Polynomial.cyclotomic` / `cyclotomic.eval` /
`sub_one_lt_natAbs_cyclotomic_eval` / `orderOf` on `ZMod p` /
`IsCyclic (ZMod p)ˣ` / `isRoot_cyclotomic_iff`. ZERO named Bang /
Zsigmondy / primitive prime divisor under `Mathlib/` or `Archive/`.
`infinite_setOf_prime_modEq_one` is **already upstream and a different
theorem** (infinitude ≡ 1 mod k). Completing Bang is the gap.

Pin: `catalog/problems/zsigmondy-theorem/STATEMENT.md` (OPE-864; Scout
OPE-853 leftover slot #2; Director OPE-863). Encoding: Mathlib
`orderOf (a : ZMod p) = n`. Zero `sorry`. Do not import `Archive.*`.

This is **not** `infinite_setOf_prime_modEq_one` (already Mathlib).
This is **not** infinitude of primes ≡ 3 (mod 4) (Cassini-class).
This is **not** Dirichlet primes in AP.
This is **not** Wolstenholme / Korselt / Euclid–Euler / Carmichael-infinitude.
This is **not** full Zsigmondy `a^n − b^n` for `b > 1` (out of v1).
This is **not** Artin's primitive-root conjecture (open, out of v1).
This is **not** `erdos-ramsey-lower` (consumed #94).
Do **not** re-prove `cyclotomic` / `cyclotomic.eval` /
`sub_one_lt_natAbs_cyclotomic_eval` / `IsCyclic (ZMod p)ˣ` /
`pow_totient` / `infinite_setOf_prime_modEq_one`.
Leave OPE-403 alone.

v1 is Bang (`b = 1`), `n ≥ 3`, exception `(2, 6)` only.
`n = 1` and `n = 2` are out of v1.

Level A `cyclotomic_eval_prime_factor` is **not** labelled Bang:
`|Φ_n(a)| > 1` via `sub_one_lt_natAbs_cyclotomic_eval` (not re-proved),
hence a prime factor. Holds for all `2 ≤ a`, `3 ≤ n` (including `(2, 6)`).

Level B engine (not the namesake): a prime factor of `Φ_n(a)` that does
not divide `n` has order `n` (`isPrimitivePrimeDivisor_of_dvd_not_dvd`),
via Mathlib `isRoot_cyclotomic_iff`. The namesake `bang` needs the
intrinsic-prime / `(2, 6)` exclusion (`p | n`); that argument is the
residual and is **not** sorry-ed.

Transcribed classical argument (Bang 1886; Zsigmondy 1892 `b = 1`).
No novelty claim.
-/
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.Tactic

set_option maxHeartbeats 800000
set_option linter.unusedVariables false

open Polynomial Nat Monoid
open scoped Nat

noncomputable section

namespace ProofLab.Zsigmondy

/-! ## Pins (match STATEMENT.md exactly) -/

/-- `p` is a primitive prime divisor of `a^n − 1`. -/
def IsPrimitivePrimeDivisor (p a n : ℕ) : Prop :=
  p.Prime ∧ ¬ p ∣ a ∧ orderOf (a : ZMod p) = n

/-- Integer value `Φ_n(a)`. Glue, not namesake. -/
abbrev cyclotomicEval (a n : ℕ) : ℤ := (cyclotomic n ℤ).eval (a : ℤ)

/-! ## Level A: `|Φ_n(a)| > 1`, hence a prime factor. Not labelled Bang. -/

lemma one_lt_natAbs_cyclotomicEval {a n : ℕ} (ha : 2 ≤ a) (hn : 3 ≤ n) :
    1 < (cyclotomicEval a n).natAbs := by
  have hn' : 1 < n := lt_trans Nat.one_lt_two hn
  have hq : a ≠ 1 := by omega
  have hbound := sub_one_lt_natAbs_cyclotomic_eval (n := n) (q := a) hn' hq
  have : 1 ≤ a - 1 := by omega
  exact lt_of_le_of_lt this hbound

/-- Level A. **Not** labelled Bang. Uses Mathlib
`sub_one_lt_natAbs_cyclotomic_eval`; does not re-prove the size bound.
The `(2, 6)` pair is allowed here: `Φ_6(2) = 3 > 1`. -/
theorem cyclotomic_eval_prime_factor (a n : ℕ) (ha : 2 ≤ a) (hn : 3 ≤ n) :
    ∃ p, p.Prime ∧ p ∣ (cyclotomicEval a n).natAbs := by
  have hgt : 1 < (cyclotomicEval a n).natAbs := one_lt_natAbs_cyclotomicEval ha hn
  refine ⟨minFac _, minFac_prime (Nat.ne_of_lt hgt).symm, minFac_dvd _⟩

/-! ## Glue: a prime dividing `Φ_n(a)` is a root in `ZMod p`.

Follows `Nat.exists_prime_gt_modEq_one`
(`NumberTheory/PrimesCongruentOne.lean`). Not labelled Bang. -/

lemma isRoot_cyclotomic_of_dvd {a n p : ℕ} [hp : Fact p.Prime]
    (hdvd : p ∣ (cyclotomicEval a n).natAbs) :
    IsRoot (cyclotomic n (ZMod p)) (Nat.castRingHom (ZMod p) a) := by
  have : ((a : ℤ) : ZMod p) = ↑(Int.castRingHom (ZMod p) a) := by simp
  rw [IsRoot.def, ← map_cyclotomic_int n (ZMod p), eval_map, coe_castRingHom,
    ← Int.cast_natCast, this, eval₂_hom, Int.coe_castRingHom,
    ZMod.intCast_zmod_eq_zero_iff_dvd]
  apply Int.dvd_natAbs.1
  exact_mod_cast hdvd

lemma not_dvd_of_root {a n p : ℕ} [hp : Fact p.Prime] (hn : 0 < n)
    (hroot : IsRoot (cyclotomic n (ZMod p)) (Nat.castRingHom (ZMod p) a)) :
    ¬ p ∣ a := by
  have hcop := coprime_of_root_cyclotomic hn hroot
  exact (hp.out.coprime_iff_not_dvd).1 hcop.symm

/-- If `p ∤ n`, a root of `Φ_n` in `ZMod p` is a primitive `n`-th root.
Engine for Level B; **not** labelled Bang. Uses `isRoot_cyclotomic_iff`. -/
lemma orderOf_eq_of_root_not_dvd {a n p : ℕ} [hp : Fact p.Prime]
    (hpn : ¬ p ∣ n)
    (hroot : IsRoot (cyclotomic n (ZMod p)) (a : ZMod p)) :
    orderOf (a : ZMod p) = n := by
  haveI : NeZero (n : ZMod p) := NeZero.of_not_dvd (ZMod p) hpn
  exact (isRoot_cyclotomic_iff.mp hroot).eq_orderOf.symm

/-- Level B engine (not the namesake): a prime factor of `Φ_n(a)` that
does not divide `n` is a primitive prime divisor. The namesake `bang`
still needs the intrinsic case `p | n` / exception `(2, 6)` and is
**not** sorry-ed. -/
lemma isPrimitivePrimeDivisor_of_dvd_not_dvd {a n p : ℕ} [hp : Fact p.Prime]
    (hn : 0 < n) (hpn : ¬ p ∣ n)
    (hdvd : p ∣ (cyclotomicEval a n).natAbs) :
    IsPrimitivePrimeDivisor p a n := by
  have hroot := isRoot_cyclotomic_of_dvd hdvd
  refine ⟨hp.out, not_dvd_of_root hn hroot,
    orderOf_eq_of_root_not_dvd hpn (by simpa [eq_natCast] using hroot)⟩

/-!
## Namesake residual (`theorem bang`)

Not sorry-ed. Remaining work: if every prime factor of `Φ_n(a)` divides
`n` (the unique intrinsic prime `p`, with `n = p^k · ord_p(a)`), show
this happens only for `(a, n) = (2, 6)`. Classical engine: LTE for odd
`p` gives `v_p(Φ_n(a)) = 1`, then size bounds / expand identities rule
out `Φ_n(a) = p`; the `p = 2` case is `Φ_{2^k}(a) = a^{2^{k-1}} + 1 ≡ 2
[MOD 4]` for odd `a ≥ 3`, `k ≥ 2`, hence an odd prime factor.
-/

end ProofLab.Zsigmondy
