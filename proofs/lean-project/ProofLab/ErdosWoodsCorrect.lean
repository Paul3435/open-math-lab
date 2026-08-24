import Mathlib.Tactic

/-!
# Erdős–Woods numbers — correct literature formalization (OPE-391)

**HARD VETO reminder:** `ProofLab/ErdosWoodsVetoed.lean` (formerly
`ErdosWoods.lean`) used a *wrong* predicate (closed interval, prime-
distinguishes XOR, spurious witness `a = 5`). Do **not** import or revive it.

This file matches `problems/erdos-woods/STATEMENT.md`:

```
∃ a > 0, ∀ j, (a < j < a+k) → (gcd(j,a) > 1 ∨ gcd(j, a+k) > 1)
```

Canonical literature witness: `k = 16`, `a = 2184` (interval `(2184, 2200)`).
Certification is exhaustive decidable check over the 15 interior integers —
zero `sorry` / `admit` / custom `axiom`. Formalize-only; **no novelty claim**.
Minimality of `a = 2184` for `k = 16` is literature (Erdős–Woods 1980 / OEIS
A059756) and is **not** proven here.
-/

namespace ProofLab.ErdosWoodsCorrect

/--
A positive integer `a` is an **Erdős–Woods witness** for positive `k` when
every integer in the **open** interval `(a, a+k)` shares a prime factor with
at least one endpoint `{a, a+k}` (equivalently: `gcd > 1` with `a` or with
`a+k`).
-/
def IsErdosWoodsWitness (k a : ℕ) : Prop :=
  0 < k ∧ 0 < a ∧
    ∀ j : ℕ, a < j → j < a + k → 1 < Nat.gcd j a ∨ 1 < Nat.gcd j (a + k)

/-- Positive `k` is an **Erdős–Woods number** when some positive witness exists. -/
def IsErdosWoodsNumber (k : ℕ) : Prop :=
  ∃ a : ℕ, IsErdosWoodsWitness k a

/--
Computable certificate: for each offset `i ∈ [0, k)`, either `i = 0` (the
left endpoint, not interior) or `a+i` shares a factor with `a` or `a+k`.
Interior points are exactly offsets `1, …, k-1`.
-/
def witnessCertificate (k a : ℕ) : Bool :=
  (List.range k).all fun i =>
    i == 0 || (1 < Nat.gcd (a + i) a || 1 < Nat.gcd (a + i) (a + k))

/-- Concrete Bool certificate for the literature pair `(k, a) = (16, 2184)`. -/
theorem witnessCertificate_16_2184 : witnessCertificate 16 2184 = true := by
  native_decide

/--
Literature witness theorem: `a = 2184` is an Erdős–Woods witness for `k = 16`.
Proved by `interval_cases` on the 15 interior points `j ∈ (2184, 2200)` and
`native_decide` on each finite gcd comparison. Zero `sorry`.
-/
theorem isErdosWoodsWitness_16_2184 : IsErdosWoodsWitness 16 2184 := by
  refine ⟨by decide, by decide, ?_⟩
  intro j hj_gt hj_lt
  -- j ∈ {2185, …, 2199}
  have h_lo : 2185 ≤ j := by omega
  have h_hi : j ≤ 2199 := by omega
  interval_cases j <;> native_decide

/-- `k = 16` is an Erdős–Woods number via literature witness `a = 2184`. -/
theorem erdos_woods_16 : IsErdosWoodsNumber 16 :=
  ⟨2184, isErdosWoodsWitness_16_2184⟩

/-- Endpoint factorizations (documentation / sanity, native-checked). -/
example : 2184 = 2 ^ 3 * 3 * 7 * 13 := by native_decide
example : 2200 = 2 ^ 3 * 5 ^ 2 * 11 := by native_decide

/-!
## Remaining (out of OPE-391 acceptance; optional stretch)

* Minimality: no positive `a < 2184` is a witness for `k = 16`.
  Literature: Erdős–Woods 1980; OEIS A059756. Not proven in this file.
* Classification of all Erdős–Woods numbers. Open-ended; not attempted.
-/

end ProofLab.ErdosWoodsCorrect
