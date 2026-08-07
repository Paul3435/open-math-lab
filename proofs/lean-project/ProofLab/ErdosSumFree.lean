import Mathlib.Data.Nat.Defs
import Mathlib.Data.Finset.Card
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

end ProofLab.SumFree